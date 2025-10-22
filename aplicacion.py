import requests
from bs4 import BeautifulSoup
from datetime import datetime, timedelta
import mysql.connector
from mysql.connector import Error
import re
from collections import Counter
import sys
import time
import pandas as pd
from sklearn.model_selection import train_test_split
from sklearn.ensemble import RandomForestClassifier
from sklearn.metrics import accuracy_score, classification_report
import numpy as np
from xgboost import XGBClassifier
import joblib
from itertools import combinations
import datetime as dt
from sqlalchemy import create_engine

# --- Importaciones de Selenium ---
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait
from selenium.common.exceptions import TimeoutException, WebDriverException

# --- Importaciones para GUI ---
import customtkinter
import tkinter as tk
from tkinter import scrolledtext
import threading

# --- Nueva clase para redirigir la salida de print a un Textbox ---
class TextRedirector:
    def __init__(self, widget, tag="stdout"):
        self.widget = widget
        self.tag = tag

    def write(self, str):
        self.widget.insert(tk.END, str, (self.tag,))
        self.widget.see(tk.END)

    def flush(self):
        pass
# --- Funciones auxiliares (Necesarias para Lags de terminación en este scope) ---
def calcular_terminacion(num_str):
    if pd.isna(num_str) or not str(num_str).isdigit(): return 0
    try: return int(num_str) % 10
    except ValueError: return 0 
    
def calcular_decena(num_str):
    if pd.isna(num_str) or not str(num_str).isdigit(): return 0
    try: return (int(num_str) // 10) % 10
    except ValueError: return 0

def format_timedelta_to_time(td):
    """
    Convierte un objeto dt.timedelta, dt.time, o cualquier otro tipo 
    a una cadena de tiempo HH:MM:SS de manera segura.
    """
    # 🚨 CORRECCIÓN CLAVE: Usar datetime.timedelta o el tipo importado
    if isinstance(td, timedelta): # <--- Usamos el tipo directo 'timedelta'
        # Maneja el caso de timedelta (duración)
        total_seconds = int(td.total_seconds())
        hours = total_seconds // 3600
        minutes = (total_seconds % 3600) // 60
        seconds = total_seconds % 60
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"
    
    elif hasattr(td, 'strftime'):
        # Maneja el caso de dt.time o dt.datetime
        return td.strftime('%H:%M:%S')
        
    # En cualquier otro caso, intenta la conversión a cadena
    return str(td)

def obtener_ultimo_hit(id_loteria):
    """
    Obtiene la fecha y hora de la última vez que salió CADA animalito en una lotería.
    """
    data = {}
    query = """
SELECT 
    a.numero_asociado AS id_target,
    MAX(STR_TO_DATE(CONCAT(s.fecha, ' ', s.hora), '%Y-%m-%d %H:%i:%S')) AS last_hit_datetime
FROM sorteos s
INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
WHERE s.id_loteria = %s
GROUP BY a.numero_asociado;
"""
    conn_a_usar = obtener_conexion_db()
    if conn_a_usar is None: return {} 

    try:
        with conn_a_usar.cursor(dictionary=True) as cursor:
            parametro_tupla = (id_loteria,) 
            cursor.execute(query, parametro_tupla)
            resultados = cursor.fetchall()
            for item in resultados:
                id_target = int(str(item['id_target']))
                data[id_target] = item['last_hit_datetime']
    except Exception as e:
        print(f"❌ Error al obtener el último hit por animalito: {e}")
        return {} 
    finally:
        if conn_a_usar and conn_a_usar.is_connected():
            conn_a_usar.close()
            
    return data 

def obtener_ultimo_hit_cruzado(animalito_id, id_loteria_actual):
    """
    Busca la última fecha/hora en que un animalito ganó en CUALQUIER OTRA lotería
    (diferente a la actual).
    Devuelve un objeto datetime o None.
    """
    conn = obtener_conexion_db()
    if conn is None: return None
    
    numero_animalito_str = str(animalito_id).zfill(2) 
    
    query = """
    SELECT MAX(STR_TO_DATE(CONCAT(s.fecha, ' ', s.hora), '%Y-%m-%d %H:%i:%S')) AS last_cross_hit_dt
    FROM sorteos s
    INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
    WHERE a.numero_asociado = %s AND s.id_loteria != %s
    """
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute(query, (numero_animalito_str, id_loteria_actual)) 
            resultado = cursor.fetchone()
            if resultado and resultado['last_cross_hit_dt']:
                return resultado['last_cross_hit_dt']
            return None
    except Exception as e:
        # print(f"Error en obtener_ultimo_hit_cruzado: {e}")
        return None
    finally:
        if conn and conn.is_connected(): conn.close()

# 🆕 FUNCIÓN AÑADIDA: Antigüedad Global
def obtener_ultimo_hit_global(animalito_id):
    """
    Busca la fecha y hora de la última vez que salió el animalito_id
    en CUALQUIER lotería del sistema (Antigüedad Global).
    """
    conn = obtener_conexion_db()
    if conn is None: return None
    
    numero_animalito_str = str(animalito_id).zfill(2) 
    
    # 🚨 QUERY GLOBAL: SIN FILTRO DE LOTERÍA 🚨
    query = """
    SELECT MAX(STR_TO_DATE(CONCAT(s.fecha, ' ', s.hora), '%Y-%m-%d %H:%i:%S')) AS last_hit_datetime
    FROM sorteos s
    INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
    WHERE a.numero_asociado = %s
    """
    
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute(query, (numero_animalito_str,)) 
            resultado = cursor.fetchone()
            if resultado and resultado['last_hit_datetime']:
                return resultado['last_hit_datetime']
            return None
    except Exception as e:
        # print(f"Error en obtener_ultimo_hit_global: {e}")
        return None
    finally:
        if conn and conn.is_connected(): conn.close()

# 🆕 FUNCIÓN AÑADIDA: Frecuencia de Repetición Inmediata (para Lag 1)
def obtener_frecuencia_repeticion(id_loteria, n_sorteos=150):
    """
    Calcula el porcentaje de veces que el animalito del sorteo anterior 
    se repitió en el sorteo inmediato siguiente de esta misma lotería,
    sobre los últimos n_sorteos. Devuelve un float entre 0.0 y 1.0.
    """
    conn = obtener_conexion_db()
    if conn is None: return 0.0
    
    query = """
    SELECT s.id_animalito_ganador AS id_actual
    FROM sorteos s
    WHERE s.id_loteria = %s
    ORDER BY s.fecha DESC, s.hora DESC 
    LIMIT %s; 
    """
    
    repeticiones = 0
    total_comparaciones = 0
    
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute(query, (id_loteria, n_sorteos + 1)) 
            resultados = cursor.fetchall()
            ids_animalito = [row['id_actual'] for row in resultados]
            
            for i in range(len(ids_animalito) - 1):
                if ids_animalito[i] == ids_animalito[i+1]:
                    repeticiones += 1
                total_comparaciones += 1
                
    except Exception as e:
        # print(f"❌ Error en obtener_frecuencia_repeticion: {e}")
        return 0.0
    finally:
        if conn and conn.is_connected(): conn.close()
            
    if total_comparaciones > 0: return repeticiones / total_comparaciones
    else: return 0.0

def obtener_antiguedad_lag_especifico_1(animalito_numero_lag_1, id_loteria_prediccion):
    """
    Busca la última fecha/hora en que el animalito que fue el lag_especifico_1 
    salió en la LOTERÍA DE PREDICCIÓN. Esto ayuda a la asignación de lotería.
    """
    conn_a_usar = obtener_conexion_db()
    if conn_a_usar is None: return None

    cursor = None
    last_hit_dt = None
    
    try:
        cursor = conn_a_usar.cursor(dictionary=True)
        num_str = str(animalito_numero_lag_1)
        if len(num_str) == 1: num_str = num_str.zfill(2)
        elif num_str == '0': num_str = '00'

        query_last_hit = """
        SELECT MAX(STR_TO_DATE(CONCAT(s.fecha, ' ', s.hora), '%Y-%m-%d %H:%i:%S')) AS last_hit_dt
        FROM sorteos s
        INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
        WHERE s.id_loteria = %s AND a.numero_asociado = %s
        """
        cursor.execute(query_last_hit, (id_loteria_prediccion, num_str))
        hit_data = cursor.fetchone()
        
        if hit_data and hit_data['last_hit_dt']:
            last_hit_dt = hit_data['last_hit_dt']

    except Exception as e:
        print(f"❌ Error en obtener_antiguedad_lag_especifico_1: {e}")
        
    finally:
        if cursor: cursor.close()
        if conn_a_usar and conn_a_usar.is_connected(): conn_a_usar.close()
    
    return last_hit_dt

def obtener_horarios_sorteo_diarios(id_loteria):
    """
    Obtiene todos los horarios únicos de sorteo para una lotería específica.
    """
    conn_a_usar = obtener_conexion_db()
    cursor = None
    if conn_a_usar is None: return []
        
    try:
        cursor = conn_a_usar.cursor()
        query = """
        SELECT DISTINCT hora 
        FROM sorteos 
        WHERE id_loteria = %s
        ORDER BY hora ASC;
        """
        cursor.execute(query, (id_loteria,))
        horarios = [format_timedelta_to_time(row[0]) for row in cursor.fetchall()]
        return horarios
        
    except Exception as e:
        print(f"❌ Error al obtener horarios de sorteo: {e}")
        return []
    finally:
        if cursor: cursor.close()
        if conn_a_usar and conn_a_usar.is_connected(): conn_a_usar.close()

def obtener_frecuencia_animal_loteria_hora(animalito_id, id_loteria, hora_sorteo_time, n_sorteos=100):
    """
    Calcula la frecuencia con la que ha salido un animalito específico en 
    una lotería y hora específica en los últimos N sorteos (o días).
    Esta función es CRÍTICA para la discriminación de lotería.
    """
    conn_a_usar = obtener_conexion_db()
    if conn_a_usar is None: return 0.0

    frecuencia = 0.0
    
    # ⚠️ IMPORTANTE: IMPLEMENTAR LA LÓGICA DE CONSULTA SQL A LA DB AQUÍ ⚠️
    # La consulta debe contar: (Victorias del animalito en esta lotería y hora) / (Total de sorteos en esta lotería y hora)
    try:
        with conn_a_usar.cursor(dictionary=True) as cursor:
            # Consulta de Ejemplo (AJUSTAR A TU ESQUEMA DB):
            # Obtener el total de veces que ha salido el animalito en esa lotería/hora en los últimos 90 días
            query_victorias = """
            SELECT COUNT(s.id_sorteo) AS victorias
            FROM sorteos s
            INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
            WHERE s.id_loteria = %s AND s.hora = %s AND a.numero_asociado = %s
            AND s.fecha >= DATE_SUB(CURDATE(), INTERVAL 90 DAY); 
            """
            # Obtener el total de sorteos de esa lotería/hora en los últimos 90 días
            query_total_sorteos = """
            SELECT COUNT(id_sorteo) AS total
            FROM sorteos
            WHERE id_loteria = %s AND hora = %s
            AND fecha >= DATE_SUB(CURDATE(), INTERVAL 90 DAY);
            """
            
            cursor.execute(query_victorias, (id_loteria, hora_sorteo_time.strftime('%H:%M:%S'), str(animalito_id).zfill(2)))
            victorias = cursor.fetchone()['victorias']
            
            cursor.execute(query_total_sorteos, (id_loteria, hora_sorteo_time.strftime('%H:%M:%S')))
            total_sorteos = cursor.fetchone()['total']
            
            if total_sorteos > 0:
                frecuencia = victorias / total_sorteos
                
    except Exception as e:
        print(f"❌ Error al calcular frecuencia_animal_loteria_hora: {e}")
    finally:
        if conn_a_usar and conn_a_usar.is_connected(): conn_a_usar.close()
        
    return frecuencia

# 🆕 FUNCIÓN AÑADIDA: Cluster de Hora
def crear_cluster_hora(hora_dt):
    """
    Clasifica una hora de sorteo en Mañana (M), Tarde (T), o Noche (N).
    """
    if isinstance(hora_dt, str):
        try:
            hora_dt = datetime.strptime(hora_dt, '%H:%M:%S').time()
        except ValueError:
            return 'N' 

    # Manejar caso en que se pasa un datetime object completo y solo queremos la hora
    if hasattr(hora_dt, 'hour'):
         hora_int = hora_dt.hour
    elif isinstance(hora_dt, datetime.time):
        hora_int = hora_dt.hour
    else:
        return 'N'
        
    if 6 <= hora_int < 12:
        cluster = 'M' # Mañana
    elif 12 <= hora_int < 18:
        cluster = 'T' # Tarde
    else:
        cluster = 'N' # Noche
        
    return cluster
def obtener_frecuencia_repeticion_local(id_loteria, hora_sorteo_time, n_sorteos_hora=50):
    """
    Calcula el porcentaje de veces que hubo repetición inmediata (Lag 1) 
    solamente entre sorteos que comparten la misma lotería y la misma hora exacta,
    sobre los últimos N sorteos en ese slot. Devuelve un float.
    """
    conn = obtener_conexion_db()
    if conn is None: return 0.0
    
    # Se consulta el animalito ganador para el slot específico, ordenado inversamente
    query = """
    SELECT s.id_animalito_ganador AS id_actual
    FROM sorteos s
    WHERE s.id_loteria = %s AND s.hora = %s
    ORDER BY s.fecha DESC, s.hora DESC 
    LIMIT %s; 
    """
    
    repeticiones = 0
    total_comparaciones = 0
    hora_str = hora_sorteo_time.strftime('%H:%M:%S')

    try:
        with conn.cursor(dictionary=True) as cursor:
            # Se pide n_sorteos_hora + 1 para tener el número de comparaciones deseado
            cursor.execute(query, (id_loteria, hora_str, n_sorteos_hora + 1)) 
            resultados = cursor.fetchall()
            ids_animalito = [row['id_actual'] for row in resultados]
            
            # La lógica de comparación se realiza en Python
            for i in range(len(ids_animalito) - 1):
                # Compara el sorteo 'i' con el sorteo inmediatamente anterior 'i+1' 
                if ids_animalito[i] == ids_animalito[i+1]:
                    repeticiones += 1
                total_comparaciones += 1
                
    except Exception as e:
        # print(f"❌ Error en obtener_frecuencia_repeticion_local: {e}")
        return 0.0
    finally:
        if conn and conn.is_connected(): conn.close()
            
    if total_comparaciones > 0: 
        return repeticiones / total_comparaciones
    else: 
        return 0.0
from datetime import timedelta

def obtener_frecuencia_influencia_global(animalito_id, hora_sorteo_dt, intervalo_horas=24):
    """
    Calcula la frecuencia con la que un animalito ha salido en CUALQUIER LOTERÍA 
    en el periodo inmediatamente anterior (ej: las últimas 24h) a la hora de predicción.
    A mayor frecuencia, mayor influencia global (está "caliente").
    """
    conn = obtener_conexion_db()
    if conn is None: return 0.0

    # Definir el rango de tiempo (ej: 24 horas antes)
    fecha_limite_inferior = hora_sorteo_dt - timedelta(hours=intervalo_horas)
    
    numero_animalito_str = str(animalito_id).zfill(2) 
    
    # ⚠️ Importante: La comparación de fechas y horas debe ser precisa
    query = """
    SELECT 
        SUM(CASE WHEN a.numero_asociado = %s THEN 1 ELSE 0 END) AS victorias,
        COUNT(s.id_sorteo) AS total_sorteos
    FROM sorteos s
    INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
    WHERE STR_TO_DATE(CONCAT(s.fecha, ' ', s.hora), '%Y-%m-%d %H:%i:%S') >= %s
    AND STR_TO_DATE(CONCAT(s.fecha, ' ', s.hora), '%Y-%m-%d %H:%i:%S') < %s
    """
    
    try:
        with conn.cursor(dictionary=True) as cursor:
            # El límite superior es la hora exacta de la predicción
            cursor.execute(query, (numero_animalito_str, fecha_limite_inferior.strftime('%Y-%m-%d %H:%M:%S'), hora_sorteo_dt.strftime('%Y-%m-%d %H:%M:%S')))
            resultado = cursor.fetchone()
            
            victorias = resultado['victorias']
            total_sorteos = resultado['total_sorteos']
            
            if total_sorteos > 0:
                return victorias / total_sorteos
            return 0.0
            
    except Exception as e:
        # print(f"❌ Error en obtener_frecuencia_influencia_global: {e}")
        return 0.0
    finally:
        if conn and conn.is_connected(): conn.close()
def calcular_fidelidad_score(animalito_id, id_loteria, hora_sorteo_time, dias_analisis=90):
    """
    Calcula un score que bonifica o penaliza al animalito basándose en la 
    comparación de su frecuencia local (lotería/hora) vs. su frecuencia global.
    
    Score > 0: El animalito es fiel a este slot. (BONIFICACIÓN)
    Score < 0: El animalito es más común en otros slots/loterías. (PENALIZACIÓN)
    """
    conn = obtener_conexion_db()
    if conn is None: return 0.0

    numero_animalito_str = str(animalito_id).zfill(2) 
    hora_str = hora_sorteo_time.strftime('%H:%M:%S')

    try:
        with conn.cursor(dictionary=True) as cursor:
            
            # A. Frecuencia LOCAL: Victorias en Loteria/Hora sobre Total Sorteos Loteria/Hora (en 90 días)
            query_local = """
            SELECT 
                SUM(CASE WHEN a.numero_asociado = %s THEN 1 ELSE 0 END) AS victorias_local,
                COUNT(s.id_sorteo) AS total_local
            FROM sorteos s
            INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
            WHERE s.id_loteria = %s AND s.hora = %s
            AND s.fecha >= DATE_SUB(CURDATE(), INTERVAL %s DAY); 
            """
            cursor.execute(query_local, (numero_animalito_str, id_loteria, hora_str, dias_analisis))
            res_local = cursor.fetchone()
            victorias_local = res_local['victorias_local']
            total_local = res_local['total_local']
            frecuencia_local = victorias_local / total_local if total_local > 0 else 0.0
            
            # B. Frecuencia GLOBAL: Victorias en CUALQUIER slot sobre Total Sorteos Globales (en 90 días)
            query_global = """
            SELECT 
                SUM(CASE WHEN a.numero_asociado = %s THEN 1 ELSE 0 END) AS victorias_global,
                COUNT(s.id_sorteo) AS total_global
            FROM sorteos s
            INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
            WHERE s.fecha >= DATE_SUB(CURDATE(), INTERVAL %s DAY);
            """
            cursor.execute(query_global, (numero_animalito_str, dias_analisis))
            res_global = cursor.fetchone()
            victorias_global = res_global['victorias_global']
            total_global = res_global['total_global']
            frecuencia_global = victorias_global / total_global if total_global > 0 else 0.0
            
            # C. Cálculo del Score de Fidelidad
            # Normalizar la frecuencia global para el número de animalitos (38)
            frecuencia_esperada_por_slot = 1.0 / 38.0 
            
            # Score base: Compara la frecuencia local vs. la frecuencia global del animalito
            fidelidad_score_bruto = frecuencia_local - (frecuencia_global * (total_local / total_global) if total_global > 0 else 0)

            # Usar una normalización simple o devolver el bruto. Aquí devolvemos una versión ajustada:
            # Se normaliza la diferencia respecto a lo que se esperaría ganar en un slot promedio (1/38)
            score_final = (frecuencia_local - frecuencia_esperada_por_slot) * total_local # Ponderación por volumen de datos local
            
            return score_final
            
    except Exception as e:
        # print(f"❌ Error en calcular_fidelidad_score: {e}")
        return 0.0
    finally:
        if conn and conn.is_connected(): conn.close()
def obtener_frecuencia_repeticion_terminacion(lag_terminacion_1, id_loteria, n_sorteos=150):
    """
    ESTRATEGIA 4: Calcula la frecuencia con la que la terminación (0-9) 
    del Lag Específico 1 ha salido en los últimos N sorteos de esta lotería.
    """
    conn = obtener_conexion_db()
    if conn is None: return 0.0
    
    # lag_terminacion_1 es un número de 0 a 9 que representa la terminación.
    terminacion_a_buscar = str(lag_terminacion_1)
    patron_terminacion = f"%{terminacion_a_buscar}" # Busca números que terminen en esa cifra (ej: %5)
    
    # 1. Contar el total de sorteos de esta lotería en el periodo
    query_total = """
    SELECT COUNT(id_sorteo) AS total 
    FROM sorteos s
    WHERE s.id_loteria = %s 
    ORDER BY s.fecha DESC, s.hora DESC 
    LIMIT %s;
    """
    
    # 2. Contar cuántas veces ha ganado un animalito con esa terminación
    query_victorias_term = """
    SELECT COUNT(s.id_sorteo) AS victorias 
    FROM sorteos s
    INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
    WHERE s.id_loteria = %s AND a.numero_asociado LIKE %s
    ORDER BY s.fecha DESC, s.hora DESC 
    LIMIT %s;
    """
    
    victorias = 0
    total_sorteos = n_sorteos # Valor de respaldo
    
    try:
        with conn.cursor(dictionary=True) as cursor:
            # Ejecutar la consulta de victorias (Límite por número de sorteos)
            cursor.execute(query_victorias_term, (id_loteria, patron_terminacion, n_sorteos))
            victorias = cursor.fetchone()['victorias']
            
            # Ejecutar la consulta del total de sorteos (Para el denominador)
            cursor.execute(query_total, (id_loteria, n_sorteos))
            total_sorteos = cursor.fetchone()['total']

    except Exception as e:
        # print(f"❌ Error en obtener_frecuencia_repeticion_terminacion: {e}")
        return 0.0
    finally:
        if conn and conn.is_connected(): conn.close()
        
    return victorias / total_sorteos if total_sorteos > 0 else 0.0
def obtener_antiguedad_lag_terminacion(lag_terminacion_1, id_loteria):
    """
    ESTRATEGIA 5: Obtiene el datetime del último hit de la terminación 
    del Lag Específico 1 en la lotería target.
    Devuelve un objeto datetime o None.
    """
    conn = obtener_conexion_db()
    if conn is None: return None
    
    # lag_terminacion_1 es un número de 0 a 9 que representa la terminación.
    terminacion_a_buscar = str(lag_terminacion_1)
    patron_terminacion = f"%{terminacion_a_buscar}" 
    
    query = """
    SELECT MAX(STR_TO_DATE(CONCAT(s.fecha, ' ', s.hora), '%Y-%m-%d %H:%i:%S')) AS last_hit_terminacion_dt
    FROM sorteos s
    INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
    WHERE s.id_loteria = %s AND a.numero_asociado LIKE %s
    """
    
    try:
        with conn.cursor(dictionary=True) as cursor:
            cursor.execute(query, (id_loteria, patron_terminacion))
            resultado = cursor.fetchone()
            
            if resultado and resultado['last_hit_terminacion_dt']:
                return resultado['last_hit_terminacion_dt']
            return None
    except Exception as e:
        # print(f"❌ Error en obtener_antiguedad_lag_terminacion: {e}")
        return None
    finally:
        if conn and conn.is_connected(): conn.close()
def obtener_repeticion_L1E_L_H(lag_especifico_1, id_loteria, hora_time, n_sorteos=50):
    """
    Calcula la frecuencia histórica de repetición inmediata (Ganador == Lag Específico 1) 
    en la misma Lotería y a la misma Hora.
    """
    if id_loteria is None:
        return 0.0

    conn = obtener_conexion_db()
    if not conn:
        print("❌ Error: No se pudo conectar a la DB para calcular repetición histórica.")
        return 0.0

    # Convertir la hora a formato de cadena para la consulta SQL
    hora_str = hora_time.strftime('%H:%M:%S')

    query = f"""
        WITH HistoricalLags AS (
            -- Obtener todos los resultados de la lotería específica
            SELECT 
                s.fecha, 
                s.hora, 
                a.numero_asociado AS id_target,
                -- 💥 CORRECCIÓN FINAL: Usar IFNULL para evitar el tercer argumento problemático de LAG()
                IFNULL(LAG(a.numero_asociado, 1) OVER (
                    ORDER BY s.fecha ASC, s.hora ASC 
                ), 0) AS lag_especifico_1_historico
            FROM sorteos s
            INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
            WHERE s.id_loteria = {id_loteria}
            ORDER BY s.fecha DESC, s.hora DESC
            LIMIT {n_sorteos * 3} 
        )
        -- Filtrar solo las filas que coinciden con la hora actual
        SELECT 
            id_target,
            lag_especifico_1_historico
        FROM HistoricalLags
        WHERE hora = '{hora_str}'
    """
    
    try:
        # Usamos pd.read_sql para evitar el error '1064' de MariaDB/MySQL
        df = pd.read_sql(query, conn)
        
        if df.empty:
             return 0.0

        # Limpieza de datos (CRÍTICO: ya que la columna id_target puede venir como string '00')
        df['id_target'] = df['id_target'].replace('00', '0').astype(int)
        # El lag_historico viene de LAG, que normalmente devuelve el tipo de dato original
        df['lag_especifico_1_historico'] = df['lag_especifico_1_historico'].astype(int)

        # LÓGICA CORREGIDA: Frecuencia de repetición inmediata (cualquier animalito)
        # Es decir: ¿Qué porcentaje de veces el ganador actual fue igual al anterior?
        conteo_repeticiones_inmediatas = (df['id_target'] == df['lag_especifico_1_historico']).sum() 
        total_sorteos_hora = len(df)
        
        if total_sorteos_hora == 0:
            return 0.0
            
        frecuencia_repeticion = conteo_repeticiones_inmediatas / total_sorteos_hora
        return frecuencia_repeticion
        
    except Exception as e:
        # Esta es la línea que fallaba antes, ahora debería funcionar con la sintaxis corregida
        print(f"❌ Error al ejecutar consulta SQL para obtener repetición L1E-L-H: {e}")
        return 0.0
    finally:
        if conn and conn.is_connected():
            conn.close()


# -------------------------------------------------------------------
# 📊 GENERACIÓN DE FEATURES (MODIFICADA)
# -------------------------------------------------------------------

def generar_features_avanzadas(df, target_col='id_target'):
    """
    Agrega todas las características, incluyendo Correlación Cruzada, Frecuencia Reciente Global, 
    Antigüedad Cruzada, Antigüedad Global, y la Interacción Lotería-Hora.
    CRÍTICO: Incluye las Interacciones Lags-Lotería, las L1E-Tiempo, y las NUEVAS FEATURES
    PARA REFORZAR LA DISCRIMINACIÓN POR LOTERÍA.
    """
    df = df.copy() 

    # 1. FEATURE CÍCLICAS (Tiempo)
    df['fecha_sorteo'] = pd.to_datetime(df['fecha_sorteo'], errors='coerce') 
    
    # Manejo de 'hora_sorteo'
    if pd.api.types.is_timedelta64_dtype(df['hora_sorteo']):
        df['hora'] = df['hora_sorteo'].dt.components.hours
        df['hora_sorteo_str'] = df['hora_sorteo'].apply(lambda x: str(x).split(' ')[-1])
    else:
        try:
            # Intenta manejar el formato HH:MM:SS para obtener la hora
            df['hora'] = pd.to_datetime(df['hora_sorteo'].astype(str), format='%H:%M:%S', errors='coerce').dt.hour 
        except:
            df['hora'] = pd.to_datetime(df['hora_sorteo'], errors='coerce').dt.hour
        df['hora_sorteo_str'] = df['hora_sorteo'].astype(str)
    
    df = df.dropna(subset=['fecha_sorteo', 'hora']).copy()
    
    # NUEVO: INTERACCIÓN LOTERÍA-HORA (Cluster)
    # Convertimos la cadena de tiempo a un objeto time para el clustering
    df['hora_dt'] = df['hora_sorteo_str'].apply(lambda x: datetime.strptime(x, '%H:%M:%S').time() if isinstance(x, str) else None)
    df['hora_cluster'] = df['hora_dt'].apply(crear_cluster_hora)

    # Crea la feature categórica combinada: LH_ID_CLUSTER (Ej: LH_46_M)
    df['loteria_hora_cluster'] = 'LH_' + df['id_loteria'].astype(str) + '_' + df['hora_cluster']
    
    df['dia_semana'] = df['fecha_sorteo'].dt.dayofweek 
    df['dia_semana_sin'] = np.sin(2 * np.pi * df['dia_semana'] / 7)
    df['dia_semana_cos'] = np.cos(2 * np.pi * df['dia_semana'] / 7)
    df['hora_fraccional'] = df['hora'] + df['hora_dt'].apply(lambda x: x.minute / 60 if x is not None else 0)
    df['hora_sin'] = np.sin(2 * np.pi * df['hora_fraccional'] / 24)
    df['hora_cos'] = np.cos(2 * np.pi * df['hora_fraccional'] / 24)
    
    df = df.sort_values(by=['fecha_sorteo', 'hora'], ascending=True).reset_index(drop=True)
    df[target_col] = df[target_col].astype(int) 

    # 2. FEATURE SECUENCIAL EXTENDIDA
    df['lag_global_1'] = df[target_col].shift(1)
    df['lag_global_2'] = df[target_col].shift(2)
    df['lag_global_3'] = df[target_col].shift(3)
    df['lag_global_4'] = df[target_col].shift(4) 
    df['lag_global_5'] = df[target_col].shift(5) 
    df['lag_especifico_1'] = df.groupby('id_loteria')[target_col].shift(1)
    df['lag_especifico_2'] = df.groupby('id_loteria')[target_col].shift(2)
    df['lag_especifico_3'] = df.groupby('id_loteria')[target_col].shift(3)
    df['lag_especifico_4'] = df.groupby('id_loteria')[target_col].shift(4)
    df['lag_especifico_5'] = df.groupby('id_loteria')[target_col].shift(5) 
    df['lag_especifico_6'] = df.groupby('id_loteria')[target_col].shift(6) 
    df['sorteo_key'] = df['id_loteria'].astype(str) + df['hora_sorteo_str'].astype(str)
    df['lag_semanal_7'] = df.groupby('sorteo_key')[target_col].shift(7)

    # 🚨 CRÍTICO: FEATURES DE INTERACCIÓN Lotería-Lag para Discriminación 🚨
    df['id_loteria_num'] = df['id_loteria'].astype(int)
    
    # Interacción Lag Global 1 x ID Lotería
    df['interaccion_L1G_Loteria'] = df['lag_global_1'] * df['id_loteria_num']
    
    # Interacción Lag Específico 1 x ID Lotería
    df['interaccion_L1E_Loteria'] = df['lag_especifico_1'] * df['id_loteria_num']
    # ----------------------------------------------------------------------
    
    # 🆕 NUEVAS INTERACCIONES LAG ESPECÍFICO 1 vs. TIEMPO (Solución a sobregeneralización) 🆕
    df['interaccion_L1E_Hsin'] = df['lag_especifico_1'] * df['hora_sin']
    df['interaccion_L1E_Hcos'] = df['lag_especifico_1'] * df['hora_cos']
    df['interaccion_L1E_DSsin'] = df['lag_especifico_1'] * df['dia_semana_sin']
    df['interaccion_L1E_DScos'] = df['lag_especifico_1'] * df['dia_semana_cos']
    # -------------------------------------------------------------------------------------

    # 3. FEATURE DE FRECUENCIA Y ANTIGÜEDAD
    df['frecuencia_reciente_global'] = df[target_col].shift(1).rolling(window=5).apply(
        lambda x: (x == x.iloc[-1]).sum(), raw=False
    ).fillna(0)
    
    df['frecuencia_30_sorteos'] = df[target_col].shift(1).rolling(window=30).apply(
        lambda x: (x == x.iloc[-1]).sum(), raw=False
    ).fillna(0)
    
    df['frecuencia_especifica_animal_30'] = df.groupby(['id_loteria', target_col])['id_loteria'].transform(
        lambda x: x.shift(1).rolling(window=30, min_periods=1).count()
    ).fillna(0)

    # Días sin Salir Exclusiva por Lotería
    df['datetime_sorteo'] = pd.to_datetime(df['fecha_sorteo'].dt.strftime('%Y-%m-%d') + ' ' + df['hora_sorteo_str'])
    df['last_hit_dt'] = df.groupby(['id_loteria', target_col])['datetime_sorteo'].shift(1)
    df['time_since_last_hit'] = df['datetime_sorteo'] - df['last_hit_dt']
    df['dias_sin_salir_exclusivo'] = df['time_since_last_hit'].dt.total_seconds() / (24 * 3600)
    df['dias_sin_salir_exclusivo'] = df['dias_sin_salir_exclusivo'].fillna(999) 
    
    # Antigüedad Cruzada (días sin salir en OTRA lotería)
    df['last_global_hit_dt'] = df.groupby(target_col)['datetime_sorteo'].shift(1)
    df['time_since_last_global_hit'] = df['datetime_sorteo'] - df['last_global_hit_dt']
    df['dias_sin_salir_otra_loteria'] = df['time_since_last_global_hit'].dt.total_seconds() / (24 * 3600)
    df['dias_sin_salir_otra_loteria'] = df['dias_sin_salir_otra_loteria'].fillna(999)
    
    # Días sin Salir Global (se calcula después)

    # Antigüedad del Lag Específico 1 en la Lotería Target
    df['lag_especifico_1_key'] = df['id_loteria'].astype(str) + '_' + df['lag_especifico_1'].astype(str)
    df['last_hit_lag1_dt'] = df.groupby(['id_loteria', 'lag_especifico_1'])['datetime_sorteo'].shift(1)
    df['time_since_last_hit_lag1'] = df['datetime_sorteo'] - df['last_hit_lag1_dt']
    df['antiguedad_lag_especifico_1_target'] = df['time_since_last_hit_lag1'].dt.total_seconds() / (24 * 3600)
    df['antiguedad_lag_especifico_1_target'] = df['antiguedad_lag_especifico_1_target'].fillna(999)
    
    # 4. FEATURE DE PARES / TERMINACIONES
    # Asegurarse de que 'numero_animalito' no sea NaN para el cálculo
    df['numero_animalito_str'] = df['numero_animalito'].astype(str)
    lag_num_ganador_1_str = df['lag_global_1'].astype(str)
    df['lag_terminacion_1'] = lag_num_ganador_1_str.apply(lambda x: calcular_terminacion(x.split('.')[0] if '.' in x else x))
    df['lag_terminacion_2'] = lag_num_ganador_1_str.apply(lambda x: calcular_decena(x.split('.')[0] if '.' in x else x))
    df['frecuencia_term_50'] = df['lag_terminacion_1'].shift(1).rolling(window=50).apply(
        lambda x: (x == x.iloc[-1]).sum() / 50, raw=False
    ).fillna(0)
    
    # 5. FEATURE DE CORRELACIÓN CRUZADA 
    df['lag_global_loteria_id'] = df['id_loteria'].shift(1)
    df['es_lag_cruzado'] = (df['id_loteria'] != df['lag_global_loteria_id']).astype(int)
    # Rellenamos NaN para evitar errores en la multiplicación antes del cálculo de la terminación
    lag_global_1_filled = df['lag_global_1'].fillna(-1) 
    df['lag_animal_cruzado'] = lag_global_1_filled * df['es_lag_cruzado']
    df['lag_terminacion_cruzada'] = df['lag_animal_cruzado'].astype(str).apply(
        lambda x: calcular_terminacion(x.split('.')[0] if '.' in x else x)
    )
    # Si lag_animal_cruzado era 0 o -1, la terminación es irrelevante, volvemos a 99 si no hay lag cruzado
    df.loc[df['es_lag_cruzado'] == 0, 'lag_terminacion_cruzada'] = 99
    df.loc[df['lag_animal_cruzado'] == -1, 'lag_animal_cruzado'] = np.nan # Vuelve a NaN para la limpieza final
    df.loc[df['lag_animal_cruzado'].isna(), 'lag_terminacion_cruzada'] = np.nan # Vuelve a NaN si no hay lag global 1
    
    # 6. Codificación OHE (Lotería y Cluster de Hora)
    dummies_loteria = pd.get_dummies(df['id_loteria'], prefix='loteria')
    dummies_cluster = pd.get_dummies(df['loteria_hora_cluster'], prefix='LH') 
    
    df = pd.concat([df, dummies_loteria, dummies_cluster], axis=1)
    
    # 7. Placeholder para features de runtime (necesarias para la coherencia en la predicción)
    
    # 🚀 REFUERZO CLAVE 2: REPETICIÓN HISTÓRICA ESPECÍFICA L-H (placeholder)
    # Esta es la feature MÁS CRÍTICA para la discriminación. Se calculará en runtime.
    df['repeticion_historica_L1E_L_H'] = 0.0 # 👈 NUEVO PLACEHOLDER
    
    # Placeholders existentes (Mantenidos)
    df['dias_sin_salir_global'] = 0.0
    df['frecuencia_repeticion_lag1'] = 0.0
    df['frecuencia_animal_loteria_hora'] = 0.0 
    df['es_lag_especifico_1_bool'] = 0.0 
    df['es_lag_especifico_2_bool'] = 0.0 
    df['frecuencia_repeticion_terminacion'] = 0.0 
    df['antiguedad_terminacion_lag1'] = 0.0 
    df['frecuencia_repeticion_local'] = 0.0 
    df['frecuencia_influencia_global'] = 0.0 
    df['fidelidad_score'] = 0.0 
    # Interacciones L1E vs. Tiempo ya calculadas en la sección 2, pero inicializadas como 0.0 en el código original, las mantenemos como están.
    
    # 8. LIMPIEZA FINAL 
    df = df.drop(columns=['sorteo_key', 'hora_sorteo_str', 'numero_animalito_str',
                          'lag_global_loteria_id', 'datetime_sorteo',
                          'last_hit_dt', 'time_since_last_hit', 'last_global_hit_dt',
                          'time_since_last_global_hit',
                          'lag_especifico_1_key', 'last_hit_lag1_dt', 'time_since_last_hit_lag1',
                          'hora_dt', 'hora_cluster', 'loteria_hora_cluster', 
                          'hora_fraccional' 
                          ], errors='ignore')
    
    # ⚠️ CRÍTICO: Eliminar solo las filas con valores NaN en las features CLAVE
    df = df.dropna().copy()
        
    return df

# ==============================================================================
# 2. FUNCIÓN DE ENTRENAMIENTO
# ==============================================================================

def entrenar_modelo_loterias():
    """
    Carga datos históricos y entrena un modelo XGBoost SEPARADO para cada lotería.
    ACTUALIZADO: Incluye TODAS las nuevas features de discriminación por lotería.
    """
    conn_global = obtener_conexion_db() 
    if not conn_global:
        print("❌ Error: No se pudo conectar a la DB para iniciar el entrenamiento.")
        return {}
    
    modelos_entrenados = {}
    query = """
    SELECT 
        s.fecha AS fecha_sorteo, s.hora AS hora_sorteo, s.id_loteria, 
        a.numero_asociado AS id_target, a.numero_asociado AS numero_animalito 
    FROM sorteos s
    INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
    ORDER BY s.fecha ASC, s.hora ASC;
    """
    
    try:
        # Uso de un DataFrame de ejemplo si la conexión falla (Solo para debug/test)
        if conn_global:
             with conn_global.cursor(dictionary=True) as cursor:
                cursor.execute(query)
                datos = cursor.fetchall()
             df_full = pd.DataFrame(datos)
        else:
             # Generación de datos simulados para prueba
             print("⚠️ Usando datos simulados para entrenamiento.")
             data = {
                 'fecha_sorteo': pd.to_datetime(['2023-01-01'] * 300),
                 'hora_sorteo': [f'{h:02d}:00:00' for h in range(10, 20)] * 30,
                 'id_loteria': [101, 102] * 150,
                 'id_target': [i % 37 for i in range(300)],
                 'numero_animalito': [f'{i % 37:02d}' for i in range(300)]
             }
             df_full = pd.DataFrame(data)

        # Asegura que el animalito '00' (Ballena) se mapee a 0
        df_full['id_target'] = df_full['id_target'].replace('00', '0').astype(int) 
        
        # 1. Generar todas las features (incluyendo los OHE y las Interacciones)
        df_full = generar_features_avanzadas(df_full, target_col='id_target')
        df_full = df_full.dropna().copy()
        
        loterias_unicas = df_full['id_loteria'].unique()
        
        # 🚨 LISTA DE FEATURES CRÍTICAS (AÑADIENDO REFUERZOS DE DISCRIMINACIÓN) 🚨
        features_a_usar = [
            'lag_global_1', 'lag_global_2', 'lag_global_3', 'lag_global_4', 'lag_global_5', 
            'lag_especifico_1', 'lag_especifico_2', 'lag_especifico_3', 
            'lag_especifico_4', 'lag_especifico_5', 'lag_especifico_6', 
            'lag_semanal_7', 'frecuencia_30_sorteos', 'frecuencia_especifica_animal_30', 
            'lag_terminacion_1', 'lag_terminacion_2', 'frecuencia_term_50',
            'hora_sin', 'hora_cos', 'dia_semana_sin', 'dia_semana_cos',
            'dias_sin_salir_exclusivo',
            'lag_animal_cruzado', 'lag_terminacion_cruzada', 'es_lag_cruzado',
            'frecuencia_reciente_global', 
            'dias_sin_salir_otra_loteria', 
            'antiguedad_lag_especifico_1_target',
            # 👈 FEATURES GLOBALES Y DE INTERACCIÓN LOTERÍA-LAG (EXISTENTES)
            'dias_sin_salir_global', 
            'frecuencia_repeticion_lag1', 
            'interaccion_L1G_Loteria', 
            'interaccion_L1E_Loteria',
            # 🚀 REFUERZO CLAVE 2: REPETICIÓN HISTÓRICA ESPECÍFICA L-H (placeholder de runtime)
            'repeticion_historica_L1E_L_H', # 👈 NUEVA FEATURE
            # 🆕 NUEVAS INTERACCIONES CRÍTICAS LAG ESPECÍFICO 1 vs. TIEMPO 
            'interaccion_L1E_Hsin',
            'interaccion_L1E_Hcos',
            'interaccion_L1E_DSsin',
            'interaccion_L1E_DScos',
            # 👈 LAS NUEVAS FEATURES DE DISCRIMINACIÓN (Estrategia 1 y 2)
            'frecuencia_animal_loteria_hora', 
            'es_lag_especifico_1_bool',
            'es_lag_especifico_2_bool',
            # 🆕 ESTRATEGIA 4 & 5: NUEVAS FEATURES (Terminación) 
            'frecuencia_repeticion_terminacion', 
            'antiguedad_terminacion_lag1', 
            # 🆕 OTRAS ESTRATEGIAS AVANZADAS
            'frecuencia_repeticion_local', 
            'frecuencia_influencia_global', 
            'fidelidad_score'

        ]
        
        # Identificar todas las columnas OHE generadas
        ohe_cols = [col for col in df_full.columns if col.startswith(('loteria_', 'LH_'))]
        
        print(f"\n--- INICIANDO ENTRENAMIENTO SEPARADO PARA {len(loterias_unicas)} LOTERÍAS ---")
        
        for id_loteria in loterias_unicas:
            df_loteria = df_full[df_full['id_loteria'] == id_loteria].copy()
            
            if len(df_loteria) < 100:
                print(f"⚠️ Advertencia: Lotería {id_loteria} tiene pocos datos ({len(df_loteria)}). Saltando.")
                continue

            # CRÍTICO: Se asegura que todas las features definidas existan antes de la reindexación
            features_loteria_final = [f for f in features_a_usar if f in df_full.columns] + ohe_cols
            
            # Se asegura que todas las columnas OHE necesarias existan en X, rellenando con 0 si es necesario
            X = df_loteria.reindex(columns=features_loteria_final, fill_value=0)
            Y = df_loteria['id_target'].astype(int) 
            
            if X.empty or Y.empty:
                print(f"❌ Error: El conjunto de datos para la Lotería {id_loteria} está vacío después de la limpieza.")
                continue

            # Usar todas las filas para el entrenamiento si el dataset es pequeño, o un simple split si es grande
            X_train = X; Y_train = Y # Entrenar con todo
            
            nombre_archivo = f'modelo_loterias_xgb_{id_loteria}.pkl'
            
            # Configuración del modelo XGBoost
            modelo = XGBClassifier(
                n_estimators=1000, learning_rate=0.02, max_depth=7, subsample=0.7, 
                colsample_bytree=0.7, eval_metric='mlogloss', random_state=42, tree_method='hist' 
            )
            
            modelo.fit(X_train, Y_train)
            
            joblib.dump(modelo, nombre_archivo)
            modelos_entrenados[id_loteria] = modelo
            print(f"✅ Modelo para ID {id_loteria} guardado como: {nombre_archivo}")
    
    except Exception as e:
        print(f"Error inesperado durante el entrenamiento: {e}")
    finally:
        if conn_global and conn_global.is_connected():
            conn_global.close()
            
    print("\n🎉 ¡ENTRENAMIENTO COMPLETADO! Los modelos están listos para predecir.")
    return modelos_entrenados


# -------------------------------------------------------------------
# 🚀 PREDICCIÓN DE ANIMALITOS (MODIFICADA)
# -------------------------------------------------------------------

def obtener_ultimos_resultados(id_loteria_prediccion, hora_sorteo_str):
    """
    Obtiene los últimos resultados necesarios para calcular las features 'lag',
    incluyendo lags globales y específicos.
    ACTUALIZADO: Inicializa y devuelve las variables de Interacción Lags-Lotería.
    CRÍTICO: Sincroniza el 21er valor de retorno con la nueva feature de discriminación.
    """
    
    conn_a_usar = obtener_conexion_db()
    cursor = None
    
    # Inicialización de 21 valores (los lags originales)
    # Globales/Correlación
    lag_global_1, lag_global_2, lag_global_3, lag_global_4, lag_global_5 = 0, 0, 0, 0, 0
    es_lag_cruzado, lag_animal_cruzado, lag_terminacion_cruzada = 0, 0, 0
    # Específicos/Frecuencia/Semanal
    lag_especifico_1, lag_especifico_2, lag_especifico_3, lag_especifico_4 = 0, 0, 0, 0 
    lag_especifico_5, lag_especifico_6 = 0, 0 
    lag_semanal_7, frecuencia_30_sorteos = 0, 0
    lag_terminacion_1, lag_terminacion_2, frecuencia_term_50 = 0, 0, 0 
    frecuencia_especifica_animal_30 = 0 
    
    # 🚨 CRÍTICO: Este valor de retorno corresponde al placeholder en predecir_animalito_ganador
    # antes era 'dummy_final'. Ahora lo renombramos por claridad para alinearlo con
    # 'repeticion_historica_L1E_L_H' que se calculará después.
    repeticion_historica_L1E_L_H = 0 
    
    # 🆕 NUEVAS VARIABLES DE INTERACCIÓN
    id_loteria_num = int(id_loteria_prediccion) # ID numérico de la lotería a predecir
    interaccion_L1G_Loteria = 0
    interaccion_L1E_Loteria = 0

    # Retorna un total de 24 valores: 21 originales + 3 nuevos
    if conn_a_usar is None: return (0,) * 24 
    
    try:
        cursor = conn_a_usar.cursor(dictionary=True)
        
        # 1. Lags Globales y Correlación Cruzada (LIMIT 5)
        query_global = """
        SELECT a.numero_asociado, s.id_loteria
        FROM sorteos s
        INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito 
        ORDER BY s.fecha DESC, s.hora DESC 
        LIMIT 5; 
        """ 
        cursor.execute(query_global)
        lag_global_data = cursor.fetchall()
        
        if len(lag_global_data) > 0: 
            ultimo_ganador_str = lag_global_data[0]['numero_asociado']
            ultimo_id_loteria = lag_global_data[0]['id_loteria']
            lag_global_1 = int(ultimo_ganador_str.replace('00', '0'))

            if len(lag_global_data) > 1: lag_global_2 = int(lag_global_data[1]['numero_asociado'].replace('00', '0'))
            if len(lag_global_data) > 2: lag_global_3 = int(lag_global_data[2]['numero_asociado'].replace('00', '0'))
            if len(lag_global_data) > 3: lag_global_4 = int(lag_global_data[3]['numero_asociado'].replace('00', '0'))
            if len(lag_global_data) > 4: lag_global_5 = int(lag_global_data[4]['numero_asociado'].replace('00', '0'))
            
            # CÁLCULO DE CORRELACIÓN CRUZADA (Solo Lag 1)
            if ultimo_id_loteria != id_loteria_prediccion:
                es_lag_cruzado = 1
                lag_animal_cruzado = lag_global_1 
                lag_terminacion_cruzada = calcular_terminacion(ultimo_ganador_str)
            
            # CÁLCULO DE TERMINACIONES
            num_ganador_lag_1_int = lag_global_1
            lag_terminacion_1 = num_ganador_lag_1_int % 10
            lag_terminacion_2 = (num_ganador_lag_1_int // 10) % 10
            
            # 🆕 CÁLCULO DE INTERACCIÓN L1G_LOTERIA
            interaccion_L1G_Loteria = lag_global_1 * id_loteria_num
        
        # 2. Lags Específicos (LIMIT 6)
        query_especifico = """
        SELECT a.numero_asociado
        FROM sorteos s
        INNER JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito 
        WHERE s.id_loteria = %s 
        ORDER BY s.fecha DESC, s.hora DESC 
        LIMIT 6; 
        """ 
        cursor.execute(query_especifico, (id_loteria_prediccion,))
        lag_especifico_data = cursor.fetchall()

        if len(lag_especifico_data) > 0: 
            lag_especifico_1 = int(lag_especifico_data[0]['numero_asociado'].replace('00', '0'))
            
            # 🆕 CÁLCULO DE INTERACCIÓN L1E_LOTERIA
            interaccion_L1E_Loteria = lag_especifico_1 * id_loteria_num

        if len(lag_especifico_data) > 1: lag_especifico_2 = int(lag_especifico_data[1]['numero_asociado'].replace('00', '0'))
        if len(lag_especifico_data) > 2: lag_especifico_3 = int(lag_especifico_data[2]['numero_asociado'].replace('00', '0'))
        if len(lag_especifico_data) > 3: lag_especifico_4 = int(lag_especifico_data[3]['numero_asociado'].replace('00', '0'))
        if len(lag_especifico_data) > 4: lag_especifico_5 = int(lag_especifico_data[4]['numero_asociado'].replace('00', '0'))
        if len(lag_especifico_data) > 5: lag_especifico_6 = int(lag_especifico_data[5]['numero_asociado'].replace('00', '0'))

    except Exception as e:
        print(f"❌ Error en obtener_ultimos_resultados al consultar la DB: {e}")
        return (0,) * 24 # Retorna 24 ceros si falla
        
    finally:
        if cursor: cursor.close()
        if conn_a_usar and conn_a_usar.is_connected(): conn_a_usar.close()
    
    # 4. Retorno de 24 valores (21 originales + 3 nuevos)
    return (
        lag_global_1, lag_global_2, lag_global_3, lag_global_4, lag_global_5,
        lag_especifico_1, lag_especifico_2, lag_especifico_3, lag_especifico_4,
        lag_especifico_5, lag_especifico_6, 
        lag_semanal_7, frecuencia_30_sorteos, 
        lag_terminacion_1, lag_terminacion_2, frecuencia_term_50,
        frecuencia_especifica_animal_30,
        es_lag_cruzado, lag_animal_cruzado, lag_terminacion_cruzada,
        repeticion_historica_L1E_L_H, # 👈 Valor sincronizado con la nueva feature
        # 🆕 VALORES AGREGADOS
        id_loteria_num,
        interaccion_L1G_Loteria,
        interaccion_L1E_Loteria
    )
# -------------------------------------------------------------------
# 🚀 PREDICCIÓN DE ANIMALITOS (MODIFICADA CON ESTRATEGIAS 4 y 5)
# -------------------------------------------------------------------

def predecir_animalito_ganador(id_loteria, hora_sorteo_str, top_n=5):
    """
    Carga el modelo ENTRENADO ESPECÍFICAMENTE para id_loteria y realiza la predicción.
    ACTUALIZADO: Incluye TODAS las nuevas features, incluyendo la CRÍTICA
    repeticion_historica_L1E_L_H.
    """
    import joblib 
    import pandas as pd
    import numpy as np
    from datetime import datetime, timedelta, time
    
    nombre_archivo_modelo = f'modelo_loterias_xgb_{id_loteria}.pkl'
    try:
        # Se asume que el archivo del modelo está en el directorio de ejecución.
        modelo = joblib.load(nombre_archivo_modelo)
        print(f"✅ Modelo {nombre_archivo_modelo} cargado correctamente.")
    except (FileNotFoundError, Exception) as e:
        print(f"❌ Error al cargar el modelo: {e}. Entrene el modelo primero.")
        return None

    # 2. Obtener features dinámicas (Lags y Correlación)
    try:
        (
            lag_global_1, lag_global_2, lag_global_3, lag_global_4, lag_global_5,
            lag_especifico_1, lag_especifico_2, lag_especifico_3, lag_especifico_4, 
            lag_especifico_5, lag_especifico_6, 
            lag_semanal_7, frecuencia_30_sorteos, 
            lag_terminacion_1, lag_terminacion_2, frecuencia_term_50,
            frecuencia_especifica_animal_30,
            es_lag_cruzado, lag_animal_cruzado, lag_terminacion_cruzada,
            _,
            # DESEMPAQUETANDO LAS FEATURES DE obtener_ultimos_resultados
            id_loteria_num,
            interaccion_L1G_Loteria,
            interaccion_L1E_Loteria
        ) = obtener_ultimos_resultados(id_loteria, hora_sorteo_str)
    except Exception as e:
        print(f"❌ Error al obtener los últimos resultados (Lags/Correlación/Interacción): {e}")
        return None
    
    # 🆕 CÁLCULO DE FEATURES GLOBALES ESTRATÉGICOS (Fuera del Bucle)
    frecuencia_repeticion_lag1 = obtener_frecuencia_repeticion(id_loteria, n_sorteos=150)
    last_hit_lag_1_dt = obtener_antiguedad_lag_especifico_1(lag_especifico_1, id_loteria)

    # 3. Preparar features de tiempo y lags
    historial_hits = obtener_ultimo_hit(id_loteria) 
    ahora = datetime.now()
    try: hora_dt = datetime.strptime(hora_sorteo_str, '%H:%M:%S')
    except ValueError: hora_dt = pd.to_datetime(hora_sorteo_str).to_pydatetime()
        
    hora_time = hora_dt.time()
        
    hora_fraccional = hora_dt.hour + hora_dt.minute / 60
    hora_sin = np.sin(2 * np.pi * hora_fraccional / 24)
    hora_cos = np.cos(2 * np.pi * hora_fraccional / 24)
    dia_semana_sin = np.sin(2 * np.pi * ahora.weekday() / 7)
    dia_semana_cos = np.cos(2 * np.pi * ahora.weekday() / 7)
    datetime_actual = datetime.combine(ahora.date(), hora_dt.time())
    all_predictions = []
    
    # 🚨 CRÍTICO: Obtener el listado de features del modelo cargado
    if not hasattr(modelo, 'feature_names_in_'):
        print("❌ Error: El modelo cargado no tiene 'feature_names_in_'. Asegúrate de que fue entrenado correctamente.")
        return None
        
    features_modelo = modelo.feature_names_in_.tolist() 

    # 🆕 CÁLCULO DE LA FEATURE: Antigüedad del lag_especifico_1 en la lotería target
    dias_antiguedad_lag_1_target = 999 
    if last_hit_lag_1_dt:
        time_diff_lag_1 = datetime_actual - last_hit_lag_1_dt
        dias_antiguedad_lag_1_target = time_diff_lag_1.total_seconds() / (24 * 3600)
    
    if dias_antiguedad_lag_1_target < 0.01:
        dias_antiguedad_lag_1_target = 0.0

    # === CÁLCULO DE CLUSTER LOTERÍA-HORA ===
    hora_cluster = crear_cluster_hora(hora_dt.time())
    loteria_hora_cluster_str = f'LH_{id_loteria}_{hora_cluster}'
    
    # 🚨 CÁLCULO DE INTERACCIONES CRÍTICAS LAG ESPECÍFICO 1 vs. TIEMPO 🚨
    interaccion_L1E_Hsin = lag_especifico_1 * hora_sin
    interaccion_L1E_Hcos = lag_especifico_1 * hora_cos
    interaccion_L1E_DSsin = lag_especifico_1 * dia_semana_sin
    interaccion_L1E_DScos = lag_especifico_1 * dia_semana_cos
    # ------------------------------------------------------------------

    # 🚨 ESTRATEGIA 4: Frecuencia de Repetición por Terminación (CRÍTICA) 🚨
    frecuencia_repeticion_terminacion = obtener_frecuencia_repeticion_terminacion(
        lag_terminacion_1, id_loteria, n_sorteos=150
    )

    # 🚨 ESTRATEGIA 5: Antigüedad de la Terminación del Lag 1 (CRÍTICA) 🚨
    last_hit_terminacion_dt = obtener_antiguedad_lag_terminacion(lag_terminacion_1, id_loteria) 
    dias_antiguedad_terminacion_lag1 = 999 
    if last_hit_terminacion_dt:
        time_diff_term = datetime_actual - last_hit_terminacion_dt
        dias_antiguedad_terminacion_lag1 = max(0.0, time_diff_term.total_seconds() / (24 * 3600))
        
    # 🚨 OTRAS ESTRATEGIAS AVANZADAS (Calculadas fuera del bucle para optimización)
    frecuencia_repeticion_local_lag1 = obtener_frecuencia_repeticion_local(id_loteria, hora_time)
    frecuencia_influencia_global = obtener_frecuencia_influencia_global(lag_especifico_1, datetime_actual)
    fidelidad_score = calcular_fidelidad_score(lag_especifico_1, id_loteria, hora_time)
    
    # 🚀 REFUERZO CLAVE 2: REPETICIÓN HISTÓRICA ESPECÍFICA L-H (CRÍTICO) 🚀
    try:
        repeticion_historica_L1E_L_H = obtener_repeticion_L1E_L_H(
            lag_especifico_1, id_loteria, hora_time, n_sorteos=50
        )
    except Exception as e:
        print(f"❌ Advertencia: Error en obtener_repeticion_L1E_L_H: {e}. Usando 0.0.")
        repeticion_historica_L1E_L_H = 0.0

    # 4. BUCLE CRÍTICO: Itera sobre todos los posibles animalitos (0 a 36)
    animales_recientes = [lag_global_1, lag_global_2, lag_global_3, lag_global_4, lag_global_5] 
    
    # 🚨 Identificar columnas OHE del modelo
    loteria_cols = [col for col in features_modelo if col.startswith('loteria_')]
    cluster_cols = [col for col in features_modelo if col.startswith('LH_')]

    for animalito_id in range(37): 
        # === CÁLCULO DE DIAS_SIN_SALIR_EXCLUSIVO ===
        last_hit_dt = historial_hits.get(animalito_id)
        if last_hit_dt:
            time_diff = datetime_actual - last_hit_dt
            dias_sin_salir = time_diff.total_seconds() / (24 * 3600)
        else:
            dias_sin_salir = 999 

        # === CÁLCULO DE LA NUEVA FEATURE: FRECUENCIA RECIENTE GLOBAL ===
        frecuencia_reciente_global = animales_recientes.count(animalito_id)

        # 🚨 NUEVA FEATURE: DÍAS SIN SALIR EN OTRAS LOTERÍAS (Antigüedad Cruzada) 🚨
        last_cross_hit_dt = obtener_ultimo_hit_cruzado(animalito_id, id_loteria) 
        if last_cross_hit_dt:
            time_diff_cross = datetime_actual - last_cross_hit_dt
            dias_sin_salir_cruzado = time_diff_cross.total_seconds() / (24 * 3600)
        else:
            dias_sin_salir_cruzado = 999 
        
        # 🚨 NUEVA FEATURE: DÍAS SIN SALIR GLOBAL (Antigüedad Global) 🚨
        last_hit_global_dt = obtener_ultimo_hit_global(animalito_id) 
        if last_hit_global_dt:
            time_diff_global = datetime_actual - last_hit_global_dt
            dias_sin_salir_global = time_diff_global.total_seconds() / (24 * 3600)
            if dias_sin_salir_global < 0: dias_sin_salir_global = 0.0
        else:
            dias_sin_salir_global = 999 

        # 🚨 ESTRATEGIA 1: FRECUENCIA ESPECÍFICA POR LOTERÍA-HORA (CRÍTICA) 🚨
        frecuencia_animal_loteria_hora = obtener_frecuencia_animal_loteria_hora(
            animalito_id, id_loteria, hora_time, n_sorteos=100
        )
        
        # 🚨 ESTRATEGIA 2: LAGS ESPECÍFICOS BOOLEANOS (Para Repetición Local) 🚨
        es_lag_especifico_1_bool = 1 if animalito_id == lag_especifico_1 else 0
        es_lag_especifico_2_bool = 1 if animalito_id == lag_especifico_2 else 0
        
        # === CREACIÓN DE LA FILA BASE ===
        base_data = {
            'lag_global_1': lag_global_1, 'lag_global_2': lag_global_2, 'lag_global_3': lag_global_3,
            'lag_global_4': lag_global_4, 'lag_global_5': lag_global_5,
            'lag_especifico_1': lag_especifico_1, 'lag_especifico_2': lag_especifico_2, 
            'lag_especifico_3': lag_especifico_3, 'lag_especifico_4': lag_especifico_4,
            'lag_especifico_5': lag_especifico_5, 'lag_especifico_6': lag_especifico_6, 
            'lag_semanal_7': lag_semanal_7, 
            'frecuencia_30_sorteos': frecuencia_30_sorteos,
            'frecuencia_especifica_animal_30': frecuencia_especifica_animal_30, 
            'lag_terminacion_1': lag_terminacion_1, 
            'lag_terminacion_2': lag_terminacion_2, 
            'frecuencia_term_50': frecuencia_term_50,
            'hora_sin': hora_sin, 'hora_cos': hora_cos,
            'dia_semana_sin': dia_semana_sin, 'dia_semana_cos': dia_semana_cos,
            'dias_sin_salir_exclusivo': dias_sin_salir,
            'es_lag_cruzado': es_lag_cruzado,
            'lag_animal_cruzado': lag_animal_cruzado,
            'lag_terminacion_cruzada': lag_terminacion_cruzada,
            'frecuencia_reciente_global': frecuencia_reciente_global,
            'dias_sin_salir_otra_loteria': dias_sin_salir_cruzado,
            'antiguedad_lag_especifico_1_target': dias_antiguedad_lag_1_target,
            'dias_sin_salir_global': dias_sin_salir_global, 
            'frecuencia_repeticion_lag1': frecuencia_repeticion_lag1,
            'interaccion_L1G_Loteria': interaccion_L1G_Loteria, 
            'interaccion_L1E_Loteria': interaccion_L1E_Loteria,
            # 🚀 REFUERZO CLAVE 2: REPETICIÓN HISTÓRICA ESPECÍFICA L-H 🚀
            'repeticion_historica_L1E_L_H': repeticion_historica_L1E_L_H, # ¡NUEVA!
            # 🆕 NUEVAS INTERACCIONES CRÍTICAS LAG ESPECÍFICO 1 vs. TIEMPO 
            'interaccion_L1E_Hsin': interaccion_L1E_Hsin,
            'interaccion_L1E_Hcos': interaccion_L1E_Hcos,
            'interaccion_L1E_DSsin': interaccion_L1E_DSsin,
            'interaccion_L1E_DScos': interaccion_L1E_DScos,
            # 👈 NUEVAS FEATURES DE DISCRIMINACIÓN (Estrategia 1 y 2)
            'frecuencia_animal_loteria_hora': frecuencia_animal_loteria_hora, 
            'es_lag_especifico_1_bool': es_lag_especifico_1_bool,
            'es_lag_especifico_2_bool': es_lag_especifico_2_bool,
            # 🆕 ESTRATEGIA 4 & 5: NUEVAS FEATURES DE TERMINACIÓN (CRÍTICO) 
            'frecuencia_repeticion_terminacion': frecuencia_repeticion_terminacion, 
            'antiguedad_terminacion_lag1': dias_antiguedad_terminacion_lag1, 
            # OTRAS ESTRATEGIAS AVANZADAS
            'frecuencia_repeticion_local': frecuencia_repeticion_local_lag1, 
            'frecuencia_influencia_global': frecuencia_influencia_global, 
            'fidelidad_score': fidelidad_score 
        }
        
        X_pred_base = pd.DataFrame([base_data])
        
        # 🛑 SOLUCIÓN CRÍTICA AL ERROR 'object': CONVERSIÓN EXPLÍCITA A NUMÉRICO
        cols_a_convertir = [
            'frecuencia_repeticion_local', 'frecuencia_influencia_global', 'fidelidad_score',
            'frecuencia_repeticion_terminacion', 'antiguedad_terminacion_lag1',
            # Asegurar que la nueva feature sea numérica
            'repeticion_historica_L1E_L_H'
        ]
        for col in cols_a_convertir:
            X_pred_base[col] = pd.to_numeric(X_pred_base[col], errors='coerce').fillna(0.0).astype(float)
        
        # 🚨 GENERACIÓN DE OHE (Lotería y Cluster de Hora) 🚨
        
        # 1. OHE de Lotería
        loteria_ohe = pd.DataFrame(0, index=[0], columns=loteria_cols)
        target_loteria_col = f'loteria_{id_loteria}'
        if target_loteria_col in loteria_ohe.columns:
            loteria_ohe[target_loteria_col] = 1

        # 2. OHE de Lotería-Hora Cluster
        cluster_ohe = pd.DataFrame(0, index=[0], columns=cluster_cols)
        if loteria_hora_cluster_str in cluster_ohe.columns:
            cluster_ohe[loteria_hora_cluster_str] = 1
            
        # 3. Combinación Final
        X_pred = pd.concat([
            X_pred_base.reset_index(drop=True), 
            loteria_ohe.reset_index(drop=True),
            cluster_ohe.reset_index(drop=True)
        ], axis=1)

        # 4. Reindexar y Predecir
        # CRÍTICO: Usa features_modelo (las columnas del modelo entrenado)
        X_pred = X_pred.reindex(columns=features_modelo, fill_value=0) 
        
        # La predicción es un paso crucial y se mantiene.
        probabilidad = modelo.predict_proba(X_pred)[0][animalito_id]
        
        all_predictions.append({
            'id_clase': animalito_id,
            'probabilidad': probabilidad
        })

    # 5. Formatear y mostrar resultados
    mapa_clase_a_datos = obtener_mapa_animalitos()
    
    resultados = []
    for pred in all_predictions:
        id_target = pred['id_clase']
        prob = pred['probabilidad']
        datos_animal = mapa_clase_a_datos.get(id_target)
        
        if datos_animal:
            resultados.append({
                'id_clase': id_target,
                'animalito': datos_animal['nombre'],
                'numero': datos_animal['numero'],
                'probabilidad': prob
            })

    df_resultados = pd.DataFrame(resultados).sort_values(by='probabilidad', ascending=False)
    
    print("\n==============================================")
    print(f"🔮 TOP {top_n} PREDICCIONES PARA LOTERÍA ID {id_loteria} ({hora_sorteo_str}) 🔮")
    print("==============================================")
    
    df_final = df_resultados.head(top_n).copy()
    df_final['probabilidad'] = (df_final['probabilidad'] * 100).round(2).astype(str) + '%'
    
    print(df_final[['numero', 'animalito', 'probabilidad']].to_string(index=False))

    return df_final


# -------------------------------------------------------------------
# 🏆 PREDICCIÓN DE TRIPLETAS (MODIFICADA)
# -------------------------------------------------------------------

# ... (imports y otras funciones)

import joblib 
import pandas as pd
import numpy as np
from datetime import datetime, time, timedelta 
from itertools import combinations
# ASUMIR QUE TODAS LAS FUNCIONES AUXILIARES (obtener_horarios_sorteo_diarios, obtener_ultimos_resultados, etc.) EXISTEN.

def predecir_tripletas_diarias(id_loteria, top_n=5):
    """
    Predice los animalitos con mayor probabilidad acumulada diaria.
    ACTUALIZADO: Incluye las features de Interacción Lag Específico 1 vs. Tiempo 
                 Y las Interacciones Lotería-Lag.
    """
    nombre_archivo_modelo = f'modelo_loterias_xgb_{id_loteria}.pkl' 
    try:
        modelo = joblib.load(nombre_archivo_modelo)
        print(f"✅ Modelo {nombre_archivo_modelo} cargado correctamente para tripletas.")
    except (FileNotFoundError, Exception) as e:
        print(f"❌ Error al cargar el modelo específico: {e}. Entrene el modelo primero.")
        return None

    # 2. OBTENER HORARIOS Y LAGS
    # Se asume que las funciones auxiliares están definidas en tu entorno.
    try:
        horarios_del_dia = obtener_horarios_sorteo_diarios(id_loteria)
    except Exception as e:
        print(f"❌ Error al obtener horarios: {e}")
        return None
        
    if not horarios_del_dia: 
        print(f"⚠️ No hay horarios para la lotería {id_loteria}.")
        return None
    
    hora_referencia = horarios_del_dia[0] 
    try:
        # Se asume que obtener_ultimos_resultados está definido
        (
            lag_global_1, lag_global_2, lag_global_3, lag_global_4, lag_global_5,
            lag_especifico_1, lag_especifico_2, lag_especifico_3, lag_especifico_4, 
            lag_especifico_5, lag_especifico_6, 
            lag_semanal_7, frecuencia_30_sorteos, 
            lag_terminacion_1, lag_terminacion_2, frecuencia_term_50,
            frecuencia_especifica_animal_30,
            es_lag_cruzado, lag_animal_cruzado, lag_terminacion_cruzada,
            dummy_final,
            # Variables recibidas de obtener_ultimos_resultados
            id_loteria_num,
            interaccion_L1G_Loteria,
            interaccion_L1E_Loteria 
        ) = obtener_ultimos_resultados(id_loteria, hora_referencia)
    except Exception as e:
        print(f"❌ Error al obtener los últimos resultados (Lags/Frecuencia) para tripletas: {e}")
        return None

    # ... (Pre-cálculo de Frecuencias y Antigüedad - Mantenido) ...
    try:
        frecuencia_repeticion_lag1 = obtener_frecuencia_repeticion(id_loteria, n_sorteos=150)
        last_hit_lag_1_dt = obtener_antiguedad_lag_especifico_1(lag_especifico_1, id_loteria)
        frecuencia_repeticion_terminacion = obtener_frecuencia_repeticion_terminacion(
            lag_terminacion_1, id_loteria, n_sorteos=150
        )
        last_hit_terminacion_dt = obtener_antiguedad_lag_terminacion(lag_terminacion_1, id_loteria)
        hora_ref_dt_time = datetime.strptime(hora_referencia, '%H:%M:%S').time()
        frecuencia_repeticion_local_lag1 = obtener_frecuencia_repeticion_local(id_loteria, hora_ref_dt_time)
        fidelidad_score_lag1 = calcular_fidelidad_score(lag_especifico_1, id_loteria, hora_ref_dt_time)
        historial_hits = obtener_ultimo_hit(id_loteria)
    except Exception as e:
        print(f"❌ Error en pre-cálculo de features: {e}")
        return None


    daily_total_probabilities = {i: 0.0 for i in range(37)}
    
    features_modelo = modelo.feature_names_in_.tolist()
    loteria_cols = [col for col in features_modelo if col.startswith('loteria_')]
    cluster_cols = [col for col in features_modelo if col.startswith('LH_')]

    ahora_ref = datetime.now()
    datetime_actual_ref = datetime.combine(ahora_ref.date(), time(0, 0, 0))
    
    dias_antiguedad_lag_1_target = 999 
    if last_hit_lag_1_dt:
        time_diff_lag_1 = datetime_actual_ref - last_hit_lag_1_dt
        dias_antiguedad_lag_1_target = max(0.0, time_diff_lag_1.total_seconds() / (24 * 3600))
    
    dias_antiguedad_terminacion_lag1 = 999 
    if last_hit_terminacion_dt:
        time_diff_term = datetime_actual_ref - last_hit_terminacion_dt
        dias_antiguedad_terminacion_lag1 = max(0.0, time_diff_term.total_seconds() / (24 * 3600))

    animales_recientes = [lag_global_1, lag_global_2, lag_global_3, lag_global_4, lag_global_5]

    for hora_sorteo_str in horarios_del_dia:
        
        ahora = datetime.now()
        try: hora_dt = pd.to_datetime(hora_sorteo_str).to_pydatetime()
        except ValueError: hora_dt = datetime.strptime(hora_sorteo_str, '%H:%M:%S') 
        
        hora_time = hora_dt.time()
        
        # === CÁLCULO DE FEATURES CÍCLICAS DE TIEMPO ===
        hora_fraccional = hora_dt.hour + hora_dt.minute / 60
        hora_sin = np.sin(2 * np.pi * hora_fraccional / 24)
        hora_cos = np.cos(2 * np.pi * hora_fraccional / 24)
        dia_semana_sin = np.sin(2 * np.pi * ahora.weekday() / 7)
        dia_semana_cos = np.cos(2 * np.pi * ahora.weekday() / 7)
        datetime_prediccion = datetime.combine(ahora.date(), hora_dt.time())
        
        # 🆕 INTEGRACIÓN CLAVE 1: CÁLCULO DE LAS INTERACCIONES LAG 1 VS TIEMPO
        interaccion_L1E_Hsin = lag_especifico_1 * hora_sin
        interaccion_L1E_Hcos = lag_especifico_1 * hora_cos
        interaccion_L1E_DSsin = lag_especifico_1 * dia_semana_sin
        interaccion_L1E_DScos = lag_especifico_1 * dia_semana_cos

        # === CÁLCULO DE CLUSTER LOTERÍA-HORA (MANTENIDO) ===
        hora_cluster = crear_cluster_hora(hora_dt.time())
        loteria_hora_cluster_str = f'LH_{id_loteria}_{hora_cluster}'

        frecuencia_influencia_global_raw = obtener_frecuencia_influencia_global(lag_especifico_1, datetime_prediccion)
        try:
            frecuencia_influencia_global = float(frecuencia_influencia_global_raw)
        except (ValueError, TypeError):
            frecuencia_influencia_global = 0.0 
        
        last_cross_hits = {a: obtener_ultimo_hit_cruzado(a, id_loteria) for a in range(37)}
        last_global_hits = {a: obtener_ultimo_hit_global(a) for a in range(37)}
        
        for animalito_id in range(37):
            
            # ... (Cálculo de dias_sin_salir, frecuencias, etc. - Mantenido) ...
            last_hit_dt = historial_hits.get(animalito_id)
            dias_sin_salir = (datetime_prediccion - last_hit_dt).total_seconds() / (24 * 3600) if last_hit_dt else 999 
            dias_sin_salir = max(0.0, dias_sin_salir)
            frecuencia_reciente_global = animales_recientes.count(animalito_id)
            last_cross_hit_dt = last_cross_hits.get(animalito_id)
            dias_sin_salir_cruzado = (datetime_prediccion - last_cross_hit_dt).total_seconds() / (24 * 3600) if last_cross_hit_dt else 999
            dias_sin_salir_cruzado = max(0.0, dias_sin_salir_cruzado)
            last_hit_global_dt = last_global_hits.get(animalito_id)
            dias_sin_salir_global = (datetime_prediccion - last_hit_global_dt).total_seconds() / (24 * 3600) if last_hit_global_dt else 999 
            dias_sin_salir_global = max(0.0, dias_sin_salir_global)
            frecuencia_animal_loteria_hora = obtener_frecuencia_animal_loteria_hora(
                animalito_id, id_loteria, hora_time, n_sorteos=100
            )
            es_lag_especifico_1_bool = 1 if animalito_id == lag_especifico_1 else 0
            es_lag_especifico_2_bool = 1 if animalito_id == lag_especifico_2 else 0

            # Creación de la Fila de Features
            base_data = {
                'lag_global_1': lag_global_1, 'lag_global_2': lag_global_2, 'lag_global_3': lag_global_3, 
                'lag_global_4': lag_global_4, 'lag_global_5': lag_global_5, 
                'lag_especifico_1': lag_especifico_1, 'lag_especifico_2': lag_especifico_2, 
                'lag_especifico_3': lag_especifico_3, 'lag_especifico_4': lag_especifico_4,
                'lag_especifico_5': lag_especifico_5, 'lag_especifico_6': lag_especifico_6,
                'lag_semanal_7': lag_semanal_7, 'frecuencia_30_sorteos': frecuencia_30_sorteos,
                'frecuencia_especifica_animal_30': frecuencia_especifica_animal_30, 
                'lag_terminacion_1': lag_terminacion_1, 'lag_terminacion_2': lag_terminacion_2, 
                'frecuencia_term_50': frecuencia_term_50,
                'hora_sin': hora_sin, 'hora_cos': hora_cos, 
                'dia_semana_sin': dia_semana_sin, 'dia_semana_cos': dia_semana_cos,
                'dias_sin_salir_exclusivo': dias_sin_salir,
                'es_lag_cruzado': es_lag_cruzado,
                'lag_animal_cruzado': lag_animal_cruzado,
                'lag_terminacion_cruzada': lag_terminacion_cruzada,
                'frecuencia_reciente_global': frecuencia_reciente_global,
                'dias_sin_salir_otra_loteria': dias_sin_salir_cruzado,
                'antiguedad_lag_especifico_1_target': dias_antiguedad_lag_1_target,
                'dias_sin_salir_global': dias_sin_salir_global, 
                'frecuencia_repeticion_lag1': frecuencia_repeticion_lag1,
                'id_loteria_num': id_loteria_num,
                # === IMPLEMENTACIÓN SOLICITADA: INCLUSIÓN DE INTERACCIONES LOTERÍA-LAG ===
                'interaccion_L1G_Loteria': interaccion_L1G_Loteria,
                'interaccion_L1E_Loteria': interaccion_L1E_Loteria,
                # =======================================================================
                # 🆕 INTEGRACIÓN CLAVE 2: INCLUSIÓN DE LAS NUEVAS INTERACCIONES
                'interaccion_L1E_Hsin': interaccion_L1E_Hsin, 
                'interaccion_L1E_Hcos': interaccion_L1E_Hcos,
                'interaccion_L1E_DSsin': interaccion_L1E_DSsin,
                'interaccion_L1E_DScos': interaccion_L1E_DScos,
                # 🚀 NUEVAS ESTRATEGIAS (4, 5 y Avanzadas) IMPLEMENTADAS 🚀
                'frecuencia_animal_loteria_hora': frecuencia_animal_loteria_hora,
                'es_lag_especifico_1_bool': es_lag_especifico_1_bool,
                'es_lag_especifico_2_bool': es_lag_especifico_2_bool,
                'frecuencia_repeticion_terminacion': frecuencia_repeticion_terminacion,
                'antiguedad_terminacion_lag1': dias_antiguedad_terminacion_lag1,
                'frecuencia_repeticion_local': frecuencia_repeticion_local_lag1, 
                'frecuencia_influencia_global': frecuencia_influencia_global, 
                'fidelidad_score': fidelidad_score_lag1 
            }
            
            # ... (Lógica de OHE, reindexar y predicción - Mantenido) ...
            X_pred_base = pd.DataFrame([base_data])
            
            loteria_ohe = pd.DataFrame(0, index=[0], columns=loteria_cols)
            target_loteria_col = f'loteria_{id_loteria}'
            if target_loteria_col in loteria_ohe.columns:
                loteria_ohe[target_loteria_col] = 1

            cluster_ohe = pd.DataFrame(0, index=[0], columns=cluster_cols)
            if loteria_hora_cluster_str in cluster_ohe.columns:
                cluster_ohe[loteria_hora_cluster_str] = 1 
                
            X_pred = pd.concat([
                X_pred_base.reset_index(drop=True), 
                loteria_ohe.reset_index(drop=True),
                cluster_ohe.reset_index(drop=True)
            ], axis=1)

            X_pred = X_pred.reindex(columns=features_modelo, fill_value=0)
            
            probabilidad = modelo.predict_proba(X_pred)[0][animalito_id] 
            daily_total_probabilities[animalito_id] += probabilidad
            
    # 4. Mapear Animalitos y Reportar (MANTENIDO)
    mapa_clase_a_datos = obtener_mapa_animalitos()
    if mapa_clase_a_datos is None: return None

    resultados = []
    for id_target, total_prob in daily_total_probabilities.items():
        datos_animal = mapa_clase_a_datos.get(id_target)
        if datos_animal:
            resultados.append({
                'animalito': datos_animal['nombre'],
                'numero': datos_animal['numero'],
                'probabilidad_diaria': total_prob 
            })

    df_resultados = pd.DataFrame(resultados).sort_values(by='probabilidad_diaria', ascending=False)
    
    print("\n==============================================")
    print(f"🏆 PREDICCIÓN TRIPLETA DIARIA para Lotería ID {id_loteria} 🏆")
    print(f"Basado en {len(horarios_del_dia)} sorteos en el día.")
    print("==============================================")
    
    df_final = df_resultados.head(top_n).copy()
    
    if len(horarios_del_dia) > 0:
        df_final['probabilidad_diaria'] = (df_final['probabilidad_diaria'] / len(horarios_del_dia) * 100).round(2).astype(str) + '% (Media)'
    else:
        df_final['probabilidad_diaria'] = '0% (Media)'

    print(df_final[['numero', 'animalito', 'probabilidad_diaria']].to_string(index=False))

    return df_final

# --------------------------------------------------------------------------------------------------

# === FUNCIÓN DE REPORTE DE TRIPLETA COMBINADA (DONDE ESTABA EL ERROR) ===

def generar_reporte_tripletas_combinadas(lista_loterias):
    """
    Genera el reporte de las 5 mejores combinaciones de tripletas para cada lotería,
    basado en el Top 5 de animalitos predichos por la probabilidad diaria acumulada.
    """
    print("\n=======================================================")
    print("🔥 GENERANDO REPORTE DE LAS MEJORES 5 TRIPLETA DIARIAS 🔥")
    print("=======================================================\n")
    
    reporte_final = {}
    
    for id_loteria in lista_loterias:
        df_top_5 = predecir_tripletas_diarias(id_loteria, top_n=5)
        
        # ❌ CORRECCIÓN DEL FALLO CRÍTICO: 'list' object has no attribute 'tolist'
        # Se asegura que el resultado no solo sea distinto de None/vacío, sino que sea un DataFrame de Pandas.
        if df_top_5 is None or df_top_5.empty or not isinstance(df_top_5, pd.DataFrame):
            print(f"❌ Fallo al obtener el DataFrame de predicciones para Lotería ID {id_loteria}. Saltando combinaciones.")
            continue

        top_animalitos = df_top_5['animalito'].tolist()
        top_numeros = df_top_5['numero'].tolist()
        
        # 3. GENERAR TODAS LAS COMBINACIONES DE 3
        # Se asume que 'combinations' ha sido importado desde 'itertools'.
        combinaciones_con_numeros = list(combinations(zip(top_animalitos, top_numeros), 3))
        
        # 4. PREPARAR EL REPORTE FINAL 
        resultados_combinados = []
        
        for i, combo in enumerate(combinaciones_con_numeros):
            if i >= 5: break
            
            nombres = [c[0] for c in combo]
            numeros = [c[1] for c in combo]
            nombre_loteria = f"Lotería ID {id_loteria}" 
            
            resultados_combinados.append({
                'Lotería': nombre_loteria,
                'Animalito 1': f"{nombres[0]} ({numeros[0]})",
                'Animalito 2': f"{nombres[1]} ({numeros[1]})",
                'Animalito 3': f"{nombres[2]} ({numeros[2]})"
            })
            
        # 5. IMPRIMIR EL REPORTE
        print(f"\n--- 🥇 Combinaciones TOP 5 para {nombre_loteria} 🥇 ---")
        df_reporte = pd.DataFrame(resultados_combinados)
        df_reporte.index = range(1, len(df_reporte) + 1) 
        
        print(df_reporte.to_string())
        
        reporte_final[id_loteria] = df_reporte
            
    return reporte_final

# --------------------------------------------------------------------------------------------------

# === FUNCIÓN DE TRIPLETA GLOBAL (MANTENIDO) ===

def generar_tripleta_consolidada_global(lista_id_loterias, hora_prediccion_str, top_n=3):
    """
    Consolida las probabilidades de un animalito específico a través de múltiples 
    loterías para generar una "Tripleta Global".
    ACTUALIZADO: Incluye las features de Interacción Lag Específico 1 vs. Tiempo
                 Y las Interacciones Lotería-Lag.
    """
    
    global_total_probabilities = {i: 0.0 for i in range(37)}
    conteo_predicciones = 0
    
    # 2. Iterar sobre cada lotería y obtener sus probabilidades (MANTENIDO)
    
    # Pre-parseo de la hora (MANTENIDO)
    try: hora_dt = pd.to_datetime(hora_prediccion_str).to_pydatetime()
    except: hora_dt = datetime.strptime(hora_prediccion_str, '%H:%M:%S')

    hora_time = hora_dt.time()
    
    # Calcular features cíclicas (MANTENIDO)
    hora_fraccional = hora_dt.hour + hora_dt.minute / 60
    hora_sin = np.sin(2 * np.pi * hora_fraccional / 24)
    hora_cos = np.cos(2 * np.pi * hora_fraccional / 24)
    ahora = datetime.now()
    dia_semana_sin = np.sin(2 * np.pi * ahora.weekday() / 7)
    dia_semana_cos = np.cos(2 * np.pi * ahora.weekday() / 7)
    datetime_prediccion = datetime.combine(ahora.date(), hora_dt.time())


    for id_loteria in lista_id_loterias:
        nombre_archivo_modelo = f'modelo_loterias_xgb_{id_loteria}.pkl'
        
        try:
            modelo = joblib.load(nombre_archivo_modelo)
            features_modelo = modelo.feature_names_in_.tolist()
            loteria_cols = [col for col in features_modelo if col.startswith('loteria_')]
            cluster_cols = [col for col in features_modelo if col.startswith('LH_')]
        except:
            print(f"❌ Modelo {nombre_archivo_modelo} no encontrado. Saltando Lotería {id_loteria}.")
            continue
            
        # 3. Obtener features dinámicas (Lags y Correlación) SOLO UNA VEZ POR HORA (MANTENIDO)
        try:
            # Se asume que obtener_ultimos_resultados está definido
            (
                lag_global_1, lag_global_2, lag_global_3, lag_global_4, lag_global_5,
                lag_especifico_1, lag_especifico_2, lag_especifico_3, lag_especifico_4, 
                lag_especifico_5, lag_especifico_6, 
                lag_semanal_7, frecuencia_30_sorteos, 
                lag_terminacion_1, lag_terminacion_2, frecuencia_term_50,
                frecuencia_especifica_animal_30,
                es_lag_cruzado, lag_animal_cruzado, lag_terminacion_cruzada,
                dummy_final,
                id_loteria_num, interaccion_L1G_Loteria, interaccion_L1E_Loteria
            ) = obtener_ultimos_resultados(id_loteria, hora_prediccion_str)
        except Exception as e:
            print(f"❌ Error al obtener los lags para Lotería {id_loteria}: {e}. Saltando.")
            continue
        
        # 🆕 INTEGRACIÓN CLAVE 1: CÁLCULO DE LAS INTERACCIONES LAG 1 VS TIEMPO
        interaccion_L1E_Hsin = lag_especifico_1 * hora_sin
        interaccion_L1E_Hcos = lag_especifico_1 * hora_cos
        interaccion_L1E_DSsin = lag_especifico_1 * dia_semana_sin
        interaccion_L1E_DScos = lag_especifico_1 * dia_semana_cos
            
        # 4. Pre-cálculo de Features Constantes para esta hora/lotería (MANTENIDO)
        frecuencia_repeticion_lag1 = obtener_frecuencia_repeticion(id_loteria, n_sorteos=150)
        last_hit_lag_1_dt = obtener_antiguedad_lag_especifico_1(lag_especifico_1, id_loteria)
        historial_hits = obtener_ultimo_hit(id_loteria)
        
        # 🚨 ESTRATEGIA 4 y 5 de Terminación (NUEVO) 🚨
        frecuencia_repeticion_terminacion = obtener_frecuencia_repeticion_terminacion(
            lag_terminacion_1, id_loteria, n_sorteos=150
        )
        last_hit_terminacion_dt = obtener_antiguedad_lag_terminacion(lag_terminacion_1, id_loteria)
        
        # 🚨 OTRAS ESTRATEGIAS AVANZADAS (NUEVO) 🚨
        frecuencia_repeticion_local_lag1 = obtener_frecuencia_repeticion_local(id_loteria, hora_time)
        fidelidad_score_lag1 = calcular_fidelidad_score(lag_especifico_1, id_loteria, hora_time)

        # Antigüedad del lag_especifico_1
        dias_antiguedad_lag_1_target = 999 
        if last_hit_lag_1_dt:
            time_diff_lag_1 = datetime_prediccion - last_hit_lag_1_dt
            dias_antiguedad_lag_1_target = max(0.0, time_diff_lag_1.total_seconds() / (24 * 3600))

        # Antigüedad de la terminación
        dias_antiguedad_terminacion_lag1 = 999 
        if last_hit_terminacion_dt:
            time_diff_term = datetime_prediccion - last_hit_terminacion_dt
            dias_antiguedad_terminacion_lag1 = max(0.0, time_diff_term.total_seconds() / (24 * 3600))

        animales_recientes = [lag_global_1, lag_global_2, lag_global_3, lag_global_4, lag_global_5]
        
        # CÁLCULO DE OHE
        hora_cluster = crear_cluster_hora(hora_dt.time())
        loteria_hora_cluster_str = f'LH_{id_loteria}_{hora_cluster}'
        
        # --- Pre-cálculo de Antigüedad Cruzada y Global (MANTENIDO) ---
        last_cross_hits = {a: obtener_ultimo_hit_cruzado(a, id_loteria) for a in range(37)}
        last_global_hits = {a: obtener_ultimo_hit_global(a) for a in range(37)}
        
        # 5. Iterar sobre los animalitos y acumular la probabilidad
        for animalito_id in range(37): 
            conteo_predicciones += 1
            
            # ... (Cálculo de features específicas para el animalito - MANTENIDO) ...
            last_hit_dt = historial_hits.get(animalito_id)
            dias_sin_salir = (datetime_prediccion - last_hit_dt).total_seconds() / (24 * 3600) if last_hit_dt else 999 
            dias_sin_salir = max(0.0, dias_sin_salir)
            frecuencia_reciente_global = animales_recientes.count(animalito_id)
            last_cross_hit_dt = last_cross_hits.get(animalito_id)
            dias_sin_salir_cruzado = (datetime_prediccion - last_cross_hit_dt).total_seconds() / (24 * 3600) if last_cross_hit_dt else 999
            dias_sin_salir_cruzado = max(0.0, dias_sin_salir_cruzado)
            last_hit_global_dt = last_global_hits.get(animalito_id)
            dias_sin_salir_global = (datetime_prediccion - last_hit_global_dt).total_seconds() / (24 * 3600) if last_hit_global_dt else 999
            dias_sin_salir_global = max(0.0, dias_sin_salir_global)

            frecuencia_animal_loteria_hora = obtener_frecuencia_animal_loteria_hora(
                animalito_id, id_loteria, hora_time, n_sorteos=100
            )
            es_lag_especifico_1_bool = 1 if animalito_id == lag_especifico_1 else 0
            es_lag_especifico_2_bool = 1 if animalito_id == lag_especifico_2 else 0

            # 🚨 CÁLCULO DE INFLUENCIA GLOBAL (Robustez de Tipo: float) 🚨
            frecuencia_influencia_global_raw = obtener_frecuencia_influencia_global(lag_especifico_1, datetime_prediccion)
            try:
                frecuencia_influencia_global = float(frecuencia_influencia_global_raw)
            except (ValueError, TypeError):
                frecuencia_influencia_global = 0.0

            # --- CREACIÓN Y PREDICCIÓN DE LA FILA ---
            base_data = {
                'lag_global_1': lag_global_1, 'lag_global_2': lag_global_2, 'lag_global_3': lag_global_3, 
                'lag_global_4': lag_global_4, 'lag_global_5': lag_global_5, 
                'lag_especifico_1': lag_especifico_1, 'lag_especifico_2': lag_especifico_2, 
                'lag_especifico_3': lag_especifico_3, 'lag_especifico_4': lag_especifico_4,
                'lag_especifico_5': lag_especifico_5, 'lag_especifico_6': lag_especifico_6,
                'lag_semanal_7': lag_semanal_7, 'frecuencia_30_sorteos': frecuencia_30_sorteos,
                'frecuencia_especifica_animal_30': frecuencia_especifica_animal_30, 
                'lag_terminacion_1': lag_terminacion_1, 'lag_terminacion_2': lag_terminacion_2, 
                'frecuencia_term_50': frecuencia_term_50,
                'hora_sin': hora_sin, 'hora_cos': hora_cos, 
                'dia_semana_sin': dia_semana_sin, 'dia_semana_cos': dia_semana_cos,
                'dias_sin_salir_exclusivo': dias_sin_salir,
                'es_lag_cruzado': es_lag_cruzado,
                'lag_animal_cruzado': lag_animal_cruzado,
                'lag_terminacion_cruzada': lag_terminacion_cruzada,
                'frecuencia_reciente_global': frecuencia_reciente_global,
                'dias_sin_salir_otra_loteria': dias_sin_salir_cruzado,
                'antiguedad_lag_especifico_1_target': dias_antiguedad_lag_1_target,
                'dias_sin_salir_global': dias_sin_salir_global, 
                'frecuencia_repeticion_lag1': frecuencia_repeticion_lag1,
                'id_loteria_num': id_loteria_num,
                # === IMPLEMENTACIÓN SOLICITADA: INCLUSIÓN DE INTERACCIONES LOTERÍA-LAG ===
                'interaccion_L1G_Loteria': interaccion_L1G_Loteria,
                'interaccion_L1E_Loteria': interaccion_L1E_Loteria,
                # =======================================================================

                # 🆕 INTEGRACIÓN CLAVE 2: INCLUSIÓN DE LAS NUEVAS INTERACCIONES
                'interaccion_L1E_Hsin': interaccion_L1E_Hsin, 
                'interaccion_L1E_Hcos': interaccion_L1E_Hcos,
                'interaccion_L1E_DSsin': interaccion_L1E_DSsin,
                'interaccion_L1E_DScos': interaccion_L1E_DScos,
                
                'frecuencia_animal_loteria_hora': frecuencia_animal_loteria_hora,
                'es_lag_especifico_1_bool': es_lag_especifico_1_bool,
                'es_lag_especifico_2_bool': es_lag_especifico_2_bool,
                'frecuencia_repeticion_terminacion': frecuencia_repeticion_terminacion,
                'antiguedad_terminacion_lag1': dias_antiguedad_terminacion_lag1,
                'frecuencia_repeticion_local': frecuencia_repeticion_local_lag1, 
                'frecuencia_influencia_global': frecuencia_influencia_global, 
                'fidelidad_score': fidelidad_score_lag1 
            }
            
            # ... (Lógica de OHE, concatenación y reindexación - MANTENIDO) ...
            X_pred_base = pd.DataFrame([base_data])
            
            loteria_ohe = pd.DataFrame(0, index=[0], columns=loteria_cols)
            target_loteria_col = f'loteria_{id_loteria}'
            if target_loteria_col in loteria_ohe.columns: loteria_ohe[target_loteria_col] = 1

            cluster_ohe = pd.DataFrame(0, index=[0], columns=cluster_cols)
            if loteria_hora_cluster_str in cluster_ohe.columns: cluster_ohe[loteria_hora_cluster_str] = 1 
                
            X_pred = pd.concat([X_pred_base, loteria_ohe, cluster_ohe], axis=1).reindex(columns=features_modelo, fill_value=0)
            
            # 6. Predecir y ACUMULAR
            probabilidad = modelo.predict_proba(X_pred)[0][animalito_id] 
            global_total_probabilities[animalito_id] += probabilidad
            
    # 7. Formatear y reportar resultados (MANTENIDO)
    mapa_clase_a_datos = obtener_mapa_animalitos()
    if mapa_clase_a_datos is None: return None

    resultados = []
    for id_target, total_prob in global_total_probabilities.items():
        datos_animal = mapa_clase_a_datos.get(id_target)
        if datos_animal:
            resultados.append({
                'id_clase': id_target,
                'animalito': datos_animal['nombre'],
                'numero': datos_animal['numero'],
                'probabilidad_total_acumulada': total_prob 
            })

    df_resultados = pd.DataFrame(resultados).sort_values(by='probabilidad_total_acumulada', ascending=False)
    
    print("\n=========================================================================")
    print(f"🥇 TRIPLETA GLOBAL CONSOLIDADA para el sorteo de las {hora_prediccion_str} 🥇")
    print(f"Acumulada de {len(lista_id_loterias)} loterías. Total de predicciones: {conteo_predicciones}.")
    print("=========================================================================")
    
    df_final = df_resultados.head(top_n).copy()
    
    if len(lista_id_loterias) > 0:
        df_final['probabilidad_media'] = (df_final['probabilidad_total_acumulada'] / len(lista_id_loterias) * 100).round(2).astype(str) + '%'
    else:
        df_final['probabilidad_media'] = '0%'

    print(df_final[['numero', 'animalito', 'probabilidad_media']].to_string(index=False))

    return df_final
# -------------------------------------------------------------
# 🟪 CLASE PRINCIPAL DE LA APLICACIÓN GUI
# -------------------------------------------------------------




class App(customtkinter.CTk):
    def __init__(self):
        super().__init__()

        self.title("Sistema de Análisis de Loterías")
        self.geometry("1000x800")

        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(2, weight=3) 
        self.grid_rowconfigure(10, weight=7) 

        self.modelo_prediccion = None
        self.animalitos_mapa = {} 
        self.load_initial_data() 
        
        # ==========================================================
        # 1. FRAME SUPERIOR (RECOLECCIÓN DE DATOS) - FILA 0
        # ==========================================================
        self.top_frame = customtkinter.CTkFrame(self)
        self.top_frame.grid(row=0, column=0, padx=10, pady=10, sticky="ew")
        self.top_frame.grid_columnconfigure((0, 1, 2), weight=1) 
        
        self.run_daily_button = customtkinter.CTkButton(
            self.top_frame,
            text="Ejecutar Scraper Diario",
            command=self.run_daily_scraper_in_thread
        )
        self.run_daily_button.grid(row=0, column=0, padx=5, pady=10, sticky="ew")
        
        self.historical_frame = customtkinter.CTkFrame(self.top_frame, fg_color="transparent")
        self.historical_frame.grid(row=0, column=1, columnspan=2, padx=5, pady=10, sticky="ew")
        self.historical_frame.grid_columnconfigure((0, 1, 2), weight=1)

        self.days_label = customtkinter.CTkLabel(self.historical_frame, text="Días a recolectar:")
        self.days_label.grid(row=0, column=0, padx=(0,5))
        
        self.days_entry = customtkinter.CTkEntry(self.historical_frame, placeholder_text="Ej: 30")
        self.days_entry.grid(row=0, column=1, padx=(0,5), sticky="ew")

        self.run_historical_button = customtkinter.CTkButton(
            self.historical_frame,
            text="Recolectar Datos Históricos",
            command=self.run_historical_scraper_in_thread
        )
        self.run_historical_button.grid(row=0, column=2, padx=5, sticky="ew")
        
        # ==========================================================
        # 2. LOG DE OPERACIONES - FILA 1 y 2
        # ==========================================================
        self.output_label = customtkinter.CTkLabel(self, text="Log de Operaciones:")
        self.output_label.grid(row=1, column=0, padx=10, pady=(0,5), sticky="w") 

        self.text_output = scrolledtext.ScrolledText(
            self,
            wrap=tk.WORD,
            width=80,
            height=15,
            bg="#2B2B2B",
            fg="#FFFFFF",
            insertbackground="#FFFFFF"
        )
        self.text_output.grid(row=2, column=0, padx=10, pady=(0,10), sticky="nsew") 
        
        
        # ==========================================================
        # 3. CONTROLES DE PREDICCIÓN - FILAS 3, 4, 5, 6, 7, 8
        # ==========================================================

        # === 3.1 Carga de Opciones REALES desde la Base de Datos ===
        # Asume que obtener_conexion_db y obtener_opciones_combobox_db están definidas
        conexion_db = obtener_conexion_db()
        if conexion_db:
            self.opciones_loterias_display, self.opciones_horas = obtener_opciones_combobox_db(conexion_db)
            conexion_db.close()
            if not self.opciones_loterias_display or not self.opciones_horas:
                print("Advertencia: La DB está vacía o faltan datos. Usando valores de ejemplo.")
                self.opciones_loterias_display = ["1 - Lotto Activo (VACÍO)", "2 - Granjita (VACÍO)"]
                self.opciones_horas = ["13:00:00", "19:00:00"]
        else:
            print("Error: No se pudo conectar a la DB. Usando valores de ejemplo.")
            self.opciones_loterias_display = ["1 - Lotto Activo (ERROR DB)", "2 - Granjita (ERROR DB)"]
            self.opciones_horas = ["13:00:00", "19:00:00"]

        # === 3.2 CREACIÓN DEL FRAME CONTENEDOR - FILA 3 ===
        self.prediction_frame = customtkinter.CTkFrame(self, fg_color="transparent")
        self.prediction_frame.grid(row=3, column=0, padx=10, pady=10, sticky="ew")
        self.prediction_frame.grid_columnconfigure((0, 1), weight=1)
        
        # === 3.3 WIDGETS DE CONTROL (Dentro del self.prediction_frame) ===
        
        # Selección de Lotería (Usado para la predicción individual)
        self.loteria_label = customtkinter.CTkLabel(self.prediction_frame, text="Lotería (Individual):")
        self.loteria_label.grid(row=0, column=0, padx=10, pady=5, sticky="w")
        self.loteria_combobox = customtkinter.CTkComboBox(self.prediction_frame, values=self.opciones_loterias_display) 
        self.loteria_combobox.set(self.opciones_loterias_display[0] if self.opciones_loterias_display else "")
        self.loteria_combobox.grid(row=0, column=1, padx=10, pady=5, sticky="ew")

        # Selección de Hora (Usado para todas las predicciones por tiempo)
        self.hora_label = customtkinter.CTkLabel(self.prediction_frame, text="Hora Sorteo (Todas):")
        self.hora_label.grid(row=1, column=0, padx=10, pady=5, sticky="w")
        self.hora_combobox = customtkinter.CTkComboBox(self.prediction_frame, values=self.opciones_horas)
        self.hora_combobox.set(self.opciones_horas[0] if self.opciones_horas else "")
        self.hora_combobox.grid(row=1, column=1, padx=10, pady=5, sticky="ew")

        # Botón de Predicción Individual - FILA 4
        self.predict_button = customtkinter.CTkButton(self, text="🔮 Predecir Animalito Ganador", command=self.predict_animalito_button_command)
        self.predict_button.grid(row=4, column=0, padx=10, pady=(0, 10), sticky="ew")
        
        # NUEVO BOTÓN: PREDICCIÓN DE TRIPLETAS DIARIAS - FILA 5
        self.predict_tripletas_button = customtkinter.CTkButton(
            self, 
            text="🃏 Predecir Tripletas Diarias (TOP 5)", 
            command=self.predict_tripletas_button_command
        )
        self.predict_tripletas_button.grid(row=5, column=0, padx=10, pady=(0, 10), sticky="ew")
        
        # 🆕 NUEVO BOTÓN: TRIPLETA GLOBAL CONSOLIDADA - FILA 6 🆕
        self.predict_global_tripletas_button = customtkinter.CTkButton(
            self, 
            text="🌟 Tripleta Global Consolidada (TOP 3 por Hora)", 
            command=self.predict_global_tripletas_button_command
        )
        self.predict_global_tripletas_button.grid(row=6, column=0, padx=10, pady=(0, 20), sticky="ew")
        
        # Etiqueta de Resultado - FILA 7
        self.resultado_prediccion_label = customtkinter.CTkLabel(self, text="Predicción: En espera...", font=customtkinter.CTkFont(size=18, weight="bold"))
        self.resultado_prediccion_label.grid(row=7, column=0, padx=10, pady=(0, 10), sticky="ew") 

        # Botón para Entrenar el Modelo - FILA 8
        self.entrenar_button = customtkinter.CTkButton(
            self, 
            text="⚙️ Entrenar Modelo (XGBoost)", 
            command=self.entrenar_modelo_thread
        )
        self.entrenar_button.grid(row=8, column=0, padx=10, pady=10, sticky="ew") 

        # ==========================================================
        # 4. TABS DE ANÁLISIS - FILA 9 y 10
        # ==========================================================
        self.analysis_label = customtkinter.CTkLabel(self, text="Resultados del Análisis:")
        self.analysis_label.grid(row=9, column=0, padx=10, pady=(10,5), sticky="w") 
        
        self.analysis_tabview = customtkinter.CTkTabview(self)
        self.analysis_tabview.grid(row=10, column=0, padx=10, pady=(0,10), sticky="nsew") 

        self.global_tab_name = "Resumen Global"
        self.analysis_tabview.add(self.global_tab_name)
        
        self.global_results_text = scrolledtext.ScrolledText(
            self.analysis_tabview.tab(self.global_tab_name),
            wrap=tk.WORD,
            bg="#2B2B2B",
            fg="#FFFFFF",
            insertbackground="#FFFFFF"
        )
        self.global_results_text.pack(fill="both", expand=True, padx=5, pady=5)
    
    # --- MÉTODOS EXISTENTES (omitiendo la implementación para brevedad) ---
    
    def run_daily_scraper_in_thread(self):
        print("Ejecutando scraper diario...")

    def run_historical_scraper_in_thread(self):
        print("Ejecutando scraper histórico...")
        
    def load_initial_data(self):
        # Asume que obtener_conexion_db y obtener_mapa_animalitos están definidas
        conexion = obtener_conexion_db()
        if conexion:
            self.animalitos_mapa = obtener_mapa_animalitos()
            conexion.close()
            if self.animalitos_mapa:
                print("✅ Mapa de animalitos cargado desde la DB.")
            else:
                print("⚠️ Advertencia: No se pudo cargar el mapa de animalitos.")
        else:
            print("❌ No se pudo establecer la conexión a la DB para cargar el mapa de animalitos.")
            
    def entrenar_modelo_thread(self):
        """Ejecuta el entrenamiento en un hilo."""
        def run_training():
            # Asume que obtener_conexion_db y entrenar_modelo_loterias están definidas
            conexion = obtener_conexion_db() 
            if conexion:
                self.modelo_prediccion = entrenar_modelo_loterias()
                conexion.close()
                if self.modelo_prediccion:
                    print("\n🎉 ¡ENTRENAMIENTO COMPLETADO! El modelo está listo para predecir.")
                else:
                    print("\n❌ El entrenamiento falló. Revise los datos y la DB.")

        threading.Thread(target=run_training).start()

    def predict_animalito_button_command(self):
        """Inicia la predicción de animalito individual en un hilo separado."""
        self.predict_button.configure(state="disabled", text="Prediciendo...")
        self.resultado_prediccion_label.configure(text="Predicción: Calculando...", text_color="orange")

        try:
            seleccion_loteria = self.loteria_combobox.get()
            id_loteria = int(seleccion_loteria.split(' ')[0]) 
            hora_sorteo_str = self.hora_combobox.get()
        except ValueError:
            print("❌ Error: Seleccione un ID de Lotería y Hora válidos.")
            self.predict_button.configure(state="normal", text="🔮 Predecir Animalito Ganador")
            return
            
        hilo_prediccion = threading.Thread(target=self.run_prediction, args=(id_loteria, hora_sorteo_str))
        hilo_prediccion.start()

    def run_prediction(self, id_loteria, hora_sorteo_str):
        """Función ejecutada por el hilo para correr la lógica de predicción individual."""
        # Asume que predecir_animalito_ganador está definida
        resultado = None 

        try:
            resultado = predecir_animalito_ganador(id_loteria, hora_sorteo_str, top_n=5)
            
            if resultado is not None and not resultado.empty:
                nombre_animalito = resultado['animalito'].iloc[0]
                numero_ganador = resultado['numero'].iloc[0] 
                self.resultado_prediccion_label.configure(
                    text=f"Predicción: ¡{nombre_animalito} ({numero_ganador})!", 
                    text_color="yellow"
                )
            else:
                self.resultado_prediccion_label.configure(text="Predicción: Fallida 😥", text_color="red")
            
        except Exception as e:
            print(f"❌ Error en la predicción individual: {e}")
            self.resultado_prediccion_label.configure(text="Predicción: Error interno 😥", text_color="red")
            
        finally:
            self.predict_button.configure(state="normal", text="🔮 Predecir Animalito Ganador")

    def predict_tripletas_button_command(self):
        """Comando que se ejecuta al presionar el botón de Tripletas Diarias."""
        self.predict_tripletas_button.configure(state="disabled", text="Generando Tripletas...")
        print("\n--- INICIANDO PREDICCIÓN DE TRIPLETAS DIARIAS ---")

        try:
            # Obtiene todos los IDs de las loterías disponibles en el combobox
            id_loterias = [int(s.split(' ')[0]) for s in self.opciones_loterias_display]
        except ValueError:
            print("❌ Error: No se pudieron parsear los IDs de lotería.")
            self.predict_tripletas_button.configure(state="normal", text="🃏 Predecir Tripletas Diarias (TOP 5)")
            return
            
        # Asume que generar_reporte_tripletas_combinadas está definida
        hilo_tripletas = threading.Thread(target=self.run_tripletas_prediction, args=(id_loterias,))
        hilo_tripletas.start()

    def run_tripletas_prediction(self, id_loterias):
        """Función ejecutada por el hilo para correr la lógica de generación de Tripletas Diarias."""
        try:
            reporte = generar_reporte_tripletas_combinadas(id_loterias)
            
            if reporte:
                print("\n✅ Reporte de Tripletas TOP 5 generado correctamente. Vea el Log para los detalles.")
            else:
                print("\n⚠️ Advertencia: El reporte de Tripletas se generó vacío.")
            
        except Exception as e:
            print(f"\n❌ Fallo crítico al generar el reporte de tripletas: {e}")
            
        finally:
            self.predict_tripletas_button.configure(state="normal", text="🃏 Predecir Tripletas Diarias (TOP 5)")
            print("--- FINALIZADO EL PROCESO DE TRIPLETAS DIARIAS ---")


    # ------------------------------------------------------------------
    # 🆕 NUEVOS MÉTODOS PARA TRIPLETA GLOBAL CONSOLIDADA
    # ------------------------------------------------------------------
    
    def predict_global_tripletas_button_command(self):
        """Comando que se ejecuta al presionar el botón de Tripleta Global."""
        self.predict_global_tripletas_button.configure(state="disabled", text="Generando Tripleta Global...")
        print("\n--- INICIANDO TRIPLETA GLOBAL CONSOLIDADA ---")

        try:
            # 1. Obtiene los IDs de todas las loterías
            id_loterias = [int(s.split(' ')[0]) for s in self.opciones_loterias_display]
            # 2. Obtiene la hora seleccionada
            hora_sorteo_str = self.hora_combobox.get()
        except ValueError:
            print("❌ Error: No se pudieron obtener los IDs de lotería o la hora.")
            self.predict_global_tripletas_button.configure(state="normal", text="🌟 Tripleta Global Consolidada (TOP 3 por Hora)")
            return
            
        # 3. Inicia la predicción en un hilo
        hilo_global = threading.Thread(target=self.run_global_tripletas_prediction, args=(id_loterias, hora_sorteo_str))
        hilo_global.start()

    def run_global_tripletas_prediction(self, id_loterias, hora_sorteo_str):
        """Función ejecutada por el hilo para correr la lógica de la Tripleta Global."""
        try:
            # Asume que generar_tripleta_consolidada_global está definida
            df_global = generar_tripleta_consolidada_global(id_loterias, hora_sorteo_str, top_n=3)
            
            if df_global is not None and not df_global.empty:
                # 4. Actualiza la etiqueta de resultado principal con el TOP 1 Global
                top_animalito = df_global['animalito'].iloc[0]
                top_numero = df_global['numero'].iloc[0]
                self.resultado_prediccion_label.configure(
                    text=f"PREDICCIÓN GLOBAL: {top_animalito} ({top_numero})", 
                    text_color="#00FFFF" # Color Aqua para destacar la predicción global
                )
                print("\n✅ Tripleta Global generada correctamente. Vea el Log para los detalles.")
            else:
                self.resultado_prediccion_label.configure(text="Predicción: Fallida 😥", text_color="red")
                print("\n⚠️ Advertencia: La Tripleta Global se generó vacía.")
            
        except Exception as e:
            print(f"\n❌ Fallo crítico al generar la Tripleta Global: {e}")
            
        finally:
            self.predict_global_tripletas_button.configure(state="normal", text="🌟 Tripleta Global Consolidada (TOP 3 por Hora)")
            print("--- FINALIZADO EL PROCESO DE TRIPLETA GLOBAL ---")

    def run_daily_scraper_in_thread(self):
        self.run_daily_button.configure(state="disabled", text="Ejecutando...")
        self.run_historical_button.configure(state="disabled")
        self.days_entry.configure(state="disabled")
        self.clear_all_tabs()
        self.analysis_tabview.set(self.global_tab_name)
        
        scraper_thread = threading.Thread(target=self._execute_scraper_and_analysis_task)
        scraper_thread.start()

    def run_historical_scraper_in_thread(self):
        try:
            dias_a_recolectar = int(self.days_entry.get())
            if dias_a_recolectar <= 0:
                self.text_output.insert(tk.END, "El número de días debe ser mayor que cero.\n")
                return
        except ValueError:
            self.text_output.insert(tk.END, "Entrada inválida. Por favor, ingresa un número de días válido.\n")
            return
            
        self.run_daily_button.configure(state="disabled")
        self.run_historical_button.configure(state="disabled", text="Ejecutando...")
        self.days_entry.configure(state="disabled")
        self.clear_all_tabs()
        self.analysis_tabview.set(self.global_tab_name)
        
        scraper_thread = threading.Thread(target=self._execute_historical_scraper_task, args=(dias_a_recolectar,))
        scraper_thread.start()
        
    def _execute_scraper_and_analysis_task(self):
        try:
            # Redirige la salida de la consola a la caja de texto
            original_stdout = sys.stdout
            original_stderr = sys.stderr
            sys.stdout = TextRedirector(self.text_output)
            sys.stderr = TextRedirector(self.text_output, "stderr")
            
            # Ejecuta la función principal
            all_analysis_results = ejecutar_scraper(self.text_output)

            # Usa `after` para pasar los resultados al hilo principal de Tkinter
            self.after(0, lambda: self.display_analysis_results(all_analysis_results))

        except Exception as e:
            print(f"Error en el hilo de análisis: {e}")
            import traceback
            traceback.print_exc(file=sys.stdout)
        finally:
            # Vuelve a redirigir la salida a la consola
            sys.stdout = original_stdout
            sys.stderr = original_stderr
            # Habilita los botones al finalizar, también en el hilo principal
            self.after(0, lambda: self.run_daily_button.configure(state="normal", text="Ejecutar Scraper Diario"))
            self.after(0, lambda: self.run_historical_button.configure(state="normal", text="Recolectar Datos Históricos"))
            self.after(0, lambda: self.days_entry.configure(state="normal"))

    def _execute_historical_scraper_task(self, dias_a_recolectar):
        ejecutar_scraper_historico(self.text_output, dias_a_recolectar)
        self.after(0, lambda: self._execute_scraper_and_analysis_task())
        self.run_daily_button.configure(state="normal", text="Ejecutar Scraper Diario")
        self.run_historical_button.configure(state="normal", text="Recolectar Datos Históricos")
        self.days_entry.configure(state="normal")


    def clear_all_tabs(self):
        tabs_to_delete = [
            tab_name for tab_name in list(self.analysis_tabview._tab_dict.keys()) 
            if tab_name != self.global_tab_name
        ]
        
        for tab_name in tabs_to_delete:
            self.analysis_tabview.delete(tab_name)
        
        self.global_results_text.delete("1.0", tk.END)

    def display_analysis_results(self, all_results):
        # --- PARTE 1: MOSTRAR RESULTADOS GLOBALES (EN EL WIDGET PRINCIPAL) ---
        self.global_results_text.configure(state='normal')
        self.global_results_text.delete("1.0", tk.END)
        
        if not all_results:
            self.global_results_text.insert(tk.END, "No se obtuvieron resultados de análisis.\n")
            self.global_results_text.configure(state='disabled')
            return

        self.global_results_text.insert(tk.END, "### Análisis de Saltos Matutinos (Global) ###\n\n")
        saltos_data = all_results.get('Saltos Matutinos', {}).get('saltos_encontrados', [])
        if saltos_data:
            for salto in saltos_data:
                self.global_results_text.insert(tk.END, f"  ¡Salto detectado! {salto['animal']} ({salto['numero']})\n")
                self.global_results_text.insert(tk.END, f"    Origen: {salto['origen_loteria_manana']} a las {salto['origen_hora_manana']}\n")
                self.global_results_text.insert(tk.END, f"    Destino: {salto['destino_loteria']} a las {salto['destino_hora']}\n")
                self.global_results_text.insert(tk.END, "\n")
        else:
            self.global_results_text.insert(tk.END, "  No se detectaron saltos matutinos para el día.\n")

        self.global_results_text.insert(tk.END, "\n" + "="*80)
        self.global_results_text.insert(tk.END, "\n### Análisis de Patrones Interloterías (Global) ###\n\n")
        patrones_interloterias_data = all_results.get('Patrones Interloterias', {}).get('patrones_interloterias', [])
        if patrones_interloterias_data:
            for patron, conteo in patrones_interloterias_data:
                animales_base = ', '.join(patron[:-1])
                animal_repeticion = patron[-1]
                self.global_results_text.insert(tk.END, f"  - Patrón: {animales_base} -> Repetición de {animal_repeticion} ({conteo} veces)\n")
        else:
            self.global_results_text.insert(tk.END, "  No se encontraron patrones de repetición significativos en los últimos 30 días.\n")
        self.global_results_text.insert(tk.END, "\n")
        
        self.global_results_text.insert(tk.END, "="*80 + "\n\n")
        self.global_results_text.insert(tk.END, "### PREDICCIONES DEL DÍA ###\n\n")
        predicciones = all_results.get('Predicciones', [])
        if predicciones:
            for i, p in enumerate(predicciones[:5], 1):
                self.global_results_text.insert(tk.END, f"  {i}. {p['animal']} ({p['numero']}) - Probabilidad: {p['score']:.2f}\n")
                for razon in set(p['razones']):
                    self.global_results_text.insert(tk.END, f"    - Razón: {razon}\n")
                self.global_results_text.insert(tk.END, "\n")
        else:
            self.global_results_text.insert(tk.END, "  No se pudieron generar predicciones con los datos actuales.\n")
        
        self.global_results_text.see(tk.END)
        self.global_results_text.configure(state='disabled')

        # --- PARTE 2: CREAR Y POBLAR LAS PESTAÑAS DE ANÁLISIS INDIVIDUALES ---
        
        # Limpiar las pestañas existentes (excepto la global) antes de crearlas de nuevo
        for tab in list(self.analysis_tabview._tab_dict.keys()):
            if tab != self.global_tab_name:
                self.analysis_tabview.delete(tab)

        for loteria, data in all_results.items():
            # Excluir los análisis globales para que no tengan su propia pestaña
            if loteria in ['Saltos Matutinos', 'Patrones Interloterias', 'Predicciones']:
                continue
            
            # Agregar la pestaña si no existe
            self.analysis_tabview.add(loteria)
            
            # Obtener o crear el widget de texto para la pestaña
            lottery_output_text = scrolledtext.ScrolledText(
                self.analysis_tabview.tab(loteria),
                wrap=tk.WORD,
                bg="#2B2B2B",
                fg="#FFFFFF",
                insertbackground="#FFFFFF"
            )
            lottery_output_text.pack(fill="both", expand=True, padx=5, pady=5)
            
            lottery_output_text.insert(tk.END, f"--- Resumen de Análisis para {loteria} ---\n\n")

            # ----------------------------------------------------------------------
            # AHORA AÑADIMOS TODO EL CONTENIDO PARA CADA PESTAÑA INDIVIDUAL
            # ----------------------------------------------------------------------

            # Tendencias de Posibles Resultados
            lottery_output_text.insert(tk.END, "Tendencias de Posibles Resultados:\n")
            if data.get('tendencias') and data['tendencias'].get('top_n_animales_mas_frecuentes'):
                for item in data['tendencias']['top_n_animales_mas_frecuentes']:
                    lottery_output_text.insert(tk.END, f"  - {item['animalito']} ({item['numero']}): {item['frecuencia']} veces (Última vez: {item['ultima_vez']})\n")
            else:
                lottery_output_text.insert(tk.END, "  No hay datos de tendencias.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Frecuencia por Horario
            lottery_output_text.insert(tk.END, "Frecuencia por Horario:\n")
            if data.get('frecuencia_horario'):
                for hora, animales in data['frecuencia_horario'].items():
                    lottery_output_text.insert(tk.END, f"  Horario {hora}:\n")
                    for animal_data in animales:
                        lottery_output_text.insert(tk.END, f"    - {animal_data['animalito']} ({animal_data['numero']}): {animal_data['frecuencia']} veces\n")
            else:
                lottery_output_text.insert(tk.END, "  No hay datos de frecuencia por horario.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Análisis de Rachas
            lottery_output_text.insert(tk.END, "Análisis de Rachas:\n")
            lottery_output_text.insert(tk.END, "  Animales Fríos (Top 5):\n")
            if data.get('rachas') and data['rachas'].get('animales_frios'):
                for item in data['rachas']['animales_frios'][:5]:
                    if item.get('ultima_vez'):
                        lottery_output_text.insert(tk.END, f"    - {item['animalito']} ({item['numero']}): Última vez hace {item['dias_sin_salir']} días.\n")
                    else:
                        lottery_output_text.insert(tk.END, f"    - {item['animalito']} ({item['numero']}): No ha salido en el período analizado.\n")
            else:
                lottery_output_text.insert(tk.END, "    No hay datos de animales fríos.\n")
            lottery_output_text.insert(tk.END, "  Animales en Racha Caliente:\n")
            if data.get('rachas') and data['rachas'].get('animales_en_racha'):
                for animal_data in data['rachas']['animales_en_racha']:
                    animal = animal_data['animalito']
                    count = animal_data['conteo']
                    numero = animal_data['numero']
                    lottery_output_text.insert(tk.END, f"    - {animal} ({numero}): Salió {count} veces recientemente.\n")
            else:
                lottery_output_text.insert(tk.END, "    No hay animales en racha caliente.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Patrones Secuenciales
            lottery_output_text.insert(tk.END, "Patrones Secuenciales:\n")
            if data.get('patrones') and data['patrones'].get('patrones_frecuentes'):
                for patron, count in data['patrones']['patrones_frecuentes']:
                    lottery_output_text.insert(tk.END, f"  - {' -> '.join(patron)}: {count} veces\n")
            else:
                lottery_output_text.insert(tk.END, "  No se encontraron patrones secuenciales significativos.\n")
            lottery_output_text.insert(tk.END, "\n")
            
            # Frecuencia por Día de la Semana
            lottery_output_text.insert(tk.END, "Frecuencia por Día de la Semana:\n")
            if data.get('frecuencia_dia_semana'):
                for dia_nombre, animales in data['frecuencia_dia_semana'].items():
                    lottery_output_text.insert(tk.END, f"  Día {dia_nombre}:\n")
                    for animal_data in animales:
                        lottery_output_text.insert(tk.END, f"    - {animal_data['animalito']}: {animal_data['frecuencia']} veces\n")
            else:
                lottery_output_text.insert(tk.END, "  No hay datos de frecuencia por día de la semana.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Terminaciones
            lottery_output_text.insert(tk.END, "Análisis de Terminaciones:\n")
            if data.get('terminaciones') and data['terminaciones'].get('terminaciones_frecuentes'):
                for term, freq in data['terminaciones']['terminaciones_frecuentes']:
                    lottery_output_text.insert(tk.END, f"  - Terminación '{term}': {freq} veces\n")
            else:
                lottery_output_text.insert(tk.END, "  No hay datos de terminaciones.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Grupos
            lottery_output_text.insert(tk.END, "Análisis de Grupos:\n")
            if data.get('grupos') and data['grupos'].get('grupos_frecuentes'):
                for grupo, freq in data['grupos']['grupos_frecuentes']:
                    lottery_output_text.insert(tk.END, f"  - Grupo {grupo}: {freq} veces\n")
            else:
                lottery_output_text.insert(tk.END, "  No hay datos de grupos.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Ciclo de Salida
            lottery_output_text.insert(tk.END, "Análisis de Ciclo de Salida:\n")
            if data.get('ciclo_salida') and data['ciclo_salida'].get('animales_fuera_de_ciclo'):
                lottery_output_text.insert(tk.END, "  Animales fuera del ciclo promedio:\n")
                for animal_data in data['ciclo_salida']['animales_fuera_de_ciclo']:
                    animal, info = animal_data
                    lottery_output_text.insert(tk.END, f"    - {animal}: {info['diferencia_dias']} días por encima del promedio ({info['promedio_dias']:.2f})\n")
            else:
                lottery_output_text.insert(tk.END, "  No se encontraron animales fuera del ciclo de salida.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Patrones Profundos
            lottery_output_text.insert(tk.END, "Patrones Secuenciales Profundos:\n")
            if data.get('patrones_profundos') and data['patrones_profundos'].get('patrones_frecuentes_profundo'):
                for patron, count in data['patrones_profundos']['patrones_frecuentes_profundo']:
                    lottery_output_text.insert(tk.END, f"  - {' -> '.join(patron)}: {count} veces\n")
            else:
                lottery_output_text.insert(tk.END, "  No se encontraron patrones profundos.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Paridad
            lottery_output_text.insert(tk.END, "Análisis de Paridad:\n")
            if data.get('paridad'):
                par_info = data['paridad'].get('par', {})
                impar_info = data['paridad'].get('impar', {})
                lottery_output_text.insert(tk.END, f"  - Números Pares: {par_info.get('conteo', 0)} veces ({par_info.get('porcentaje', '0.00%')})\n")
                lottery_output_text.insert(tk.END, f"  - Números Impares: {impar_info.get('conteo', 0)} veces ({impar_info.get('porcentaje', '0.00%')})\n")
            else:
                lottery_output_text.insert(tk.END, "  No hay datos de paridad.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Correlación
            lottery_output_text.insert(tk.END, "Análisis de Correlación:\n")
            if data.get('correlacion') and data['correlacion'].get('pares_correlacionados'):
                for (animal1, animal2), conteo in data['correlacion']['pares_correlacionados']:
                    lottery_output_text.insert(tk.END, f"  - {animal1} -> {animal2}: {conteo} veces\n")
            else:
                lottery_output_text.insert(tk.END, "  No hay datos de correlación.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Decenas
            lottery_output_text.insert(tk.END, "Análisis de Decenas Frecuentes:\n")
            if data.get('decenas') and data['decenas'].get('decenas_frecuentes'):
                for decena, conteo in data['decenas']['decenas_frecuentes']:
                    lottery_output_text.insert(tk.END, f"  - Decena {decena}-{decena+9}: {conteo} veces\n")
            else:
                lottery_output_text.insert(tk.END, "  No hay datos de decenas frecuentes.\n")
            lottery_output_text.insert(tk.END, "\n")

            # Modelo Predictivo por Hora
            lottery_output_text.insert(tk.END, "Modelo Predictivo por Hora:\n")
            if data.get('modelo_hora') and data['modelo_hora'].get('predicciones'):
                hora_actual = datetime.now().strftime('%I:%M %p')
                predicciones_actuales = data['modelo_hora']['predicciones'].get(hora_actual, [])
                if predicciones_actuales:
                    lottery_output_text.insert(tk.END, f"  Predicciones para las {hora_actual}:\n")
                    for animal_predicho, conteo in predicciones_actuales:
                        lottery_output_text.insert(tk.END, f"    - {animal_predicho}: {conteo} veces\n")
                else:
                    lottery_output_text.insert(tk.END, "  No hay predicciones para la hora actual.\n")
            else:
                lottery_output_text.insert(tk.END, "  No hay datos del modelo por hora.\n")
            lottery_output_text.insert(tk.END, "\n")

            lottery_output_text.configure(state='disabled')
            lottery_output_text.see(tk.END)





# --- Configuración de la Base de Datos ---
CONFIG_DB = {
    'host': '127.0.0.1',
    'database': 'loterias',
    'user': 'root',
    'password': ''
}

# --- Configuración de Selenium ---
RUTA_CHROMEDRIVER = 'C:\\Users\\monster\\Desktop\\src\\chromedriver-win64\\chromedriver.exe'

# Horarios permitidos para cada lotería
LOTERIAS_PERMITIDAS_HORARIOS = {
    'Lotto Activo': ['08:00 AM', '09:00 AM', '10:00 AM', '11:00 AM', '12:00 PM', '01:00 PM', '02:00 PM', '03:00 PM', '04:00 PM', '05:00 PM', '06:00 PM', '07:00 PM', '08:00 PM', '09:00 PM'],
    'Granjita': ['08:00 AM', '09:00 AM', '10:00 AM', '11:00 AM', '12:00 PM', '01:00 PM', '02:00 PM', '03:00 PM', '04:00 PM', '05:00 PM', '06:00 PM', '07:00 PM'],
    'Selva Plus': ['08:00 AM', '09:00 AM', '10:00 AM', '11:00 AM', '12:00 PM', '01:00 PM', '02:00 PM', '03:00 PM', '04:00 PM', '05:00 PM', '06:00 PM', '07:00 PM']
}

def obtener_conexion_db():
    try:
        conexion = mysql.connector.connect(**CONFIG_DB)
        if conexion.is_connected():
            return conexion
    except Error as error:
        print(f"Error al conectar a la base de datos: {error}")
        return None
def obtener_mapa_animalitos():
    """
    Consulta la tabla 'animalitos' y devuelve un mapa donde la clave es 
    el ID de CLASE de XGBoost (0-36) y el valor es el nombre real y el número.
    Ahora es autocontenida: maneja su propia conexión a la DB.
    """
    conn_a_usar = obtener_conexion_db()
    cursor = None
    mapa_clase_a_datos = {}
    
    if conn_a_usar is None:
        print("Error: No se pudo establecer la conexión a la base de datos para mapear animalitos.")
        return None
        
    try:
        cursor = conn_a_usar.cursor(dictionary=True)
        query = "SELECT nombre, numero_asociado FROM animalitos ORDER BY CAST(REPLACE(numero_asociado, '00', '0') AS UNSIGNED) ASC;"
        cursor.execute(query)
        resultados = cursor.fetchall()
        
        for row in resultados:
            id_numerico = int(row['numero_asociado'].replace('00', '0'))
            
            if id_numerico not in mapa_clase_a_datos:
                 mapa_clase_a_datos[id_numerico] = {
                    'numero': row['numero_asociado'], 
                    'nombre': row['nombre']
                }
            elif id_numerico == 0 and row['numero_asociado'] == '00':
                 mapa_clase_a_datos[id_numerico] = {
                    'numero': '0/00', 
                    'nombre': 'Delfin / Ballena'
                }
            
    except Error as e:
        print(f"❌ Error al obtener el mapa de animalitos de la DB: {e}")
        return None
    finally:
        if cursor:
            cursor.close()
        if conn_a_usar and conn_a_usar.is_connected():
            conn_a_usar.close()
            
    print("✅ Mapa de animalitos cargado desde la DB.")
    return mapa_clase_a_datos

def obtener_opciones_combobox_db(conexion):
    """
    Consulta la DB para obtener IDs y Nombres de loterías 
    y horarios únicos de sorteos.
    Retorna una tupla: (lista_ids_loteria_display, lista_horas_sorteo)
    """
    if not conexion:
        print("Error: No se pudo establecer la conexión a la base de datos para cargar opciones.")
        return [], []
        
    cursor = conexion.cursor()
    
    
    # 1. Obtener IDs y Nombres de Lotería
    # ESTA ES LA LÍNEA CORREGIDA: Usamos 'id_loteria' en lugar de 'id'
    query_loterias = "SELECT id_loteria, nombre FROM loterias ORDER BY id_loteria ASC;"
    try:
        cursor.execute(query_loterias)
    except Exception as e:
        print(f"Error al ejecutar query de loterías: {e}")
        return [], []
    
    # Creamos una lista con el formato "ID - Nombre" (ej: "1 - LOTTO ACTIVO")
    ids_loterias_con_nombre = [f"{row[0]} - {row[1]}" for row in cursor.fetchall()]

    # 2. Obtener Horarios Únicos de Sorteo
    # Esto obtiene todos los horarios distintos de la columna 'hora' en la tabla 'sorteos'
    query_horas = "SELECT DISTINCT hora FROM sorteos ORDER BY hora ASC;"
    try:
        cursor.execute(query_horas)
    except Exception as e:
        print(f"Error al ejecutar query de horas: {e}")
        return ids_loterias_con_nombre, [] # Retorna lo que tenga
    
    # Convertimos los objetos de tiempo a strings 'HH:MM:SS'
    horas_sorteo = [str(row[0]) for row in cursor.fetchall()]
    
    cursor.close()
    return ids_loterias_con_nombre, horas_sorteo

def obtener_id_y_numero_animalito(conexion, nombre_animal):
    cursor = None
    try:
        cursor = conexion.cursor()
        query = "SELECT id_animalito, numero_asociado FROM animalitos WHERE nombre = %s"
        cursor.execute(query, (nombre_animal,))
        resultado = cursor.fetchone()
        return resultado
    except Error as error:
        print(f"Error al obtener ID/Número de animalito '{nombre_animal}': {error}")
        return None
    finally:
        if cursor:
            cursor.close()
            
def obtener_numero_animalito(conexion, nombre_animal):
    cursor = None
    try:
        cursor = conexion.cursor()
        query = "SELECT numero_asociado FROM animalitos WHERE nombre = %s"
        cursor.execute(query, (nombre_animal,))
        resultado = cursor.fetchone()
        return resultado[0] if resultado else 'N/A'
    except Error as error:
        print(f"Error al obtener número de animalito '{nombre_animal}': {error}")
        return 'N/A'
    finally:
        if cursor:
            cursor.close()

def obtener_id_loteria(conexion, nombre_loteria):
    cursor = None
    try:
        cursor = conexion.cursor()
        query = "SELECT id_loteria FROM loterias WHERE nombre = %s"
        cursor.execute(query, (nombre_loteria,))
        resultado = cursor.fetchone()
        return resultado[0] if resultado else None
    except Error as error:
        print(f"Error al obtener ID de lotería '{nombre_loteria}': {error}")
        return None
    finally:
        if cursor:
            cursor.close()
def obtener_ultimo_resultado_por_loteria(conexion, nombre_loteria):
    """
    Obtiene el animalito ganador del último sorteo registrado para una lotería específica.
    """
    cursor = None
    try:
        cursor = conexion.cursor(dictionary=True)
        query = """
        SELECT nombre_animalito_ganador, numero_ganador, hora, fecha
        FROM sorteos s
        JOIN loterias l ON s.id_loteria = l.id_loteria
        WHERE l.nombre = %s
        ORDER BY s.fecha DESC, s.hora DESC
        LIMIT 1
        """
        cursor.execute(query, (nombre_loteria,))
        resultado = cursor.fetchone()
        
        if resultado:
            return {
                'animalito_nombre': resultado['nombre_animalito_ganador'],
                'animalito_numero': resultado['numero_ganador'],
                'hora': resultado['hora'],
                'fecha': resultado['fecha']
            }
        return None
    except Error as error:
        print(f"Error al obtener el último resultado para {nombre_loteria}: {error}")
        return None
    finally:
        if cursor:
            cursor.close()

def insertar_resultado_sorteo(conexion, fecha, hora, id_loteria, id_animalito, numero_animalito, nombre_animalito):
    cursor = None
    try:
        cursor = conexion.cursor()
        consulta_verificacion = """
        SELECT id_sorteo FROM sorteos
        WHERE fecha = %s AND hora = %s AND id_loteria = %s
        """
        cursor.execute(consulta_verificacion, (fecha.strftime('%Y-%m-%d'), hora, id_loteria))
        sorteo_existente = cursor.fetchone()

        if sorteo_existente:
            print(f"Resultado ya existe para {fecha.strftime('%Y-%m-%d')} a las {hora}. No se insertó.")
            return

        consulta_insercion = """
        INSERT INTO sorteos (fecha, hora, id_loteria, id_animalito_ganador, numero_ganador, nombre_animalito_ganador)
        VALUES (%s, %s, %s, %s, %s, %s)
        """
        cursor.execute(consulta_insercion, (fecha.strftime('%Y-%m-%d'), hora, id_loteria, id_animalito, numero_animalito, nombre_animalito))
        conexion.commit()
        print(f"Resultado insertado: {fecha.strftime('%Y-%m-%d')} {hora} - {nombre_animalito} ({numero_animalito}) para Lotería ID {id_loteria}")
    except Error as error:
        print(f"Error al insertar resultado del sorteo: {error}")
    finally:
        if cursor:
            cursor.close()

def obtener_html_con_selenium(url, driver=None):
    """
    Obtiene el contenido HTML de una URL usando Selenium.
    Reutiliza un driver si se le pasa, o crea uno nuevo.
    """
    driver_local = None
    try:
        if driver is None:
            servicio = Service(RUTA_CHROMEDRIVER)
            opciones_chrome = webdriver.ChromeOptions()
            opciones_chrome.add_argument('user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36')
            opciones_chrome.add_argument("--headless")
            driver_local = webdriver.Chrome(service=servicio, options=opciones_chrome)
        else:
            driver_local = driver
        
        print(f"Abriendo página: {url}")
        driver_local.get(url)

        WebDriverWait(driver_local, 30).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, ".counter-wrapper"))
        )
        
        contenido_html_renderizado = driver_local.page_source
        print(f"HTML obtenido con Selenium de {driver_local.current_url}")
        return contenido_html_renderizado

    except WebDriverException as e:
        print(f"Error de WebDriver al acceder a {url}: {e}")
        print("Asegúrate que ChromeDriver está actualizado y en la ruta correcta.")
        return None
    except Exception as e:
        print(f"Ocurrió un error inesperado con Selenium en {url}: {e}")
        return None
    finally:
        if driver_local and driver is None:
            driver_local.quit()

# --- FUNCIÓN DE PARSING PARA LA PÁGINA lotoven.com ---
def parsear_resultados_lotoven(contenido_html, fecha_esperada=None):
    """
    Parsea los resultados de la página lotoven.com.
    Si se proporciona una fecha, verifica que la página corresponde a esa fecha.
    """
    resultados = []
    if not contenido_html:
        return resultados

    sopa = BeautifulSoup(contenido_html, 'html.parser')
    
    # NUEVA VERIFICACIÓN DE FECHA
    if fecha_esperada:
        fecha_en_pagina_element = sopa.find('h3', string=lambda s: s and "Resultados de la fecha" in s)
        if not fecha_en_pagina_element:
            # Nueva regex para el otro formato de fecha
            fecha_en_pagina_element = sopa.find('h3', string=re.compile(r'Monday, \d{1,2} of \w+ de \d{4}')) 
        
        if fecha_en_pagina_element:
            fecha_str_en_pagina = fecha_en_pagina_element.get_text(strip=True).split(': ')[-1]
            try:
                # Intenta parsear la fecha en la página
                fecha_encontrada = datetime.strptime(fecha_str_en_pagina, '%d-%m-%Y').date()
                if fecha_encontrada != fecha_esperada:
                    print(f"AVISO: La fecha de la página ({fecha_encontrada}) no coincide con la fecha solicitada ({fecha_esperada}). Saltando.")
                    return resultados
            except ValueError:
                print(f"AVISO: No se pudo parsear la fecha '{fecha_str_en_pagina}' de la página.")
                return resultados
    
    bloques_sorteo = sopa.find_all('div', class_='counter-wrapper')
    
    if not bloques_sorteo:
        print("No se encontraron bloques de sorteo con la clase 'counter-wrapper'.")
        return resultados

    for bloque in bloques_sorteo:
        try:
            img_tag = bloque.find('img')
            loteria_completa = img_tag.get('title', 'Desconocida')
            
            coincidencia_loteria = re.search(r'Animalito\s+(Lotto Activo|La Granjita|Selva Plus)\b', loteria_completa)
            nombre_loteria = coincidencia_loteria.group(1) if coincidencia_loteria else 'Desconocida'
            
            if nombre_loteria == 'La Granjita':
                nombre_loteria = 'Granjita'
            
            span_animal = bloque.find('span', class_=re.compile(r'info'))
            texto_animal = span_animal.get_text(strip=True) if span_animal else 'N/A'
            
            span_hora = bloque.find('span', class_=re.compile(r'horario'))
            hora_texto = span_hora.get_text(strip=True) if span_hora else 'N/A'
            
            if nombre_loteria != 'Desconocida' and texto_animal != 'N/A' and hora_texto != 'N/A':
                # Nuevo filtro para horarios en punto
                if nombre_loteria not in LOTERIAS_PERMITIDAS_HORARIOS or hora_texto not in LOTERIAS_PERMITIDAS_HORARIOS[nombre_loteria]:
                    # print(f"Saltando resultado de {nombre_loteria} en horario no oficial: {hora_texto}")
                    continue

                partes = texto_animal.split(' ', 1)
                numero_animal = partes[0]
                nombre_animal = partes[1].title()
                
                resultados.append({
                    'loteria': nombre_loteria,
                    'hora': hora_texto,
                    'animalito': nombre_animal,
                    'numero': numero_animal
                })
        except Exception as e:
            print(f"Advertencia: Error al parsear un bloque de sorteo: {e}")
            continue

    return resultados




def buscar_patrones_secuenciales(conexion, id_loteria, longitud_patron=2, dias_atras=730, top_n_patrones=5):
    print(f"\nBuscando patrones secuenciales (longitud {longitud_patron}) para Lotería ID {id_loteria} (últimos {dias_atras} días)...")
    
    resultados_historicos_raw = []
    cursor = None
    try:
        cursor = conexion.cursor(dictionary=True)
        fecha_limite = datetime.now().date() - timedelta(days=dias_atras)

        query = """
        SELECT s.fecha, s.hora, a.nombre AS animalito_nombre
        FROM sorteos s
        JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
        WHERE s.id_loteria = %s AND s.fecha >= %s
        ORDER BY s.fecha ASC, s.hora ASC
        """
        cursor.execute(query, (id_loteria, fecha_limite))
        resultados_historicos_raw = cursor.fetchall()
    except Error as error:
        print(f"Error al obtener resultados para búsqueda de patrones: {error}")
        return {}
    finally:
        if cursor:
            cursor.close()

    if not resultados_historicos_raw or len(resultados_historicos_raw) < longitud_patron:
        print(f"No hay suficientes datos históricos ({len(resultados_historicos_raw)} resultados) para buscar patrones de longitud {longitud_patron}.")
        return {}

    secuencia_animalitos = [res['animalito_nombre'] for res in resultados_historicos_raw]
    conteo_patrones = Counter()
    for i in range(len(secuencia_animalitos) - longitud_patron + 1):
        patron = tuple(secuencia_animalitos[i : i + longitud_patron])
        conteo_patrones[patron] += 1
    
    patrones_frecuentes = {patron: count for patron, count in conteo_patrones.items() if count > 1}

    if not patrones_frecuentes:
        print(f"No se encontraron patrones de longitud {longitud_patron} que se repitan.")
        return {}

    print(f"\n--- Patrones Secuenciales más Frecuentes (longitud {longitud_patron}): ---")
    patrones_ordenados = sorted(patrones_frecuentes.items(), key=lambda item: item[1], reverse=True)[:top_n_patrones]

    for patron, count in patrones_ordenados:
        print(f"  - {' -> '.join(patron)}: {count} veces")
    
    return {'patrones_frecuentes': patrones_ordenados}

def obtener_resultados_de_un_dia(conexion, fecha):
    resultados_del_dia = []
    cursor = None
    try:
        cursor = conexion.cursor(dictionary=True)
        query = """
        SELECT s.fecha, s.hora, l.nombre AS nombre_loteria, 
               a.nombre AS animalito_nombre, a.numero_asociado AS animalito_numero
        FROM sorteos s
        JOIN loterias l ON s.id_loteria = l.id_loteria
        JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
        WHERE s.fecha = %s
        ORDER BY s.hora ASC
        """
        cursor.execute(query, (fecha.strftime('%Y-%m-%d'),))
        resultados_del_dia = cursor.fetchall()
        return resultados_del_dia
    except Error as error:
        print(f"Error al obtener resultados para la fecha {fecha}: {error}")
        return []
    finally:
        if cursor:
            cursor.close()

def analizar_saltos_matutinos(conexion, dias_analisis=1):
    """
    Analiza si un animalito que salió en la mañana vuelve a salir en la tarde del mismo día.
    """
    print("\n================================================================================")
    print("                 ANÁLISIS GLOBAL DE SALTOS MATUTINOS                          ")
    print("================================================================================")
    
    fecha_analisis = datetime.now().date() - timedelta(days=dias_analisis - 1)
    print(f"\n--- Analizando patrón de 'saltos matutinos' para el {fecha_analisis.strftime('%Y-%m-%d')} ---")
    
    todos_los_resultados_del_dia = obtener_resultados_de_un_dia(conexion, fecha_analisis)

    if not todos_los_resultados_del_dia:
        print("No hay resultados para el día especificado para realizar el análisis de saltos.")
        return {'saltos_encontrados': []}

    # Definimos el límite de tiempo. Los sorteos de 1:00 PM en adelante son de la tarde.
    hora_limite_manana = timedelta(hours=12, minutes=59)

    pool_manana = {}
    print("\nResultados de la mañana (hasta las 12:59 PM):")
    for res in todos_los_resultados_del_dia:
        # La 1:00 PM se almacena como 1:00:00. Debemos excluirla del pool de la mañana.
        if res['hora'] <= hora_limite_manana and res['hora'] != timedelta(hours=1):
            animal = (res['animalito_nombre'], res['animalito_numero'])
            if animal not in pool_manana:
                pool_manana[animal] = {
                    'origen_loteria_manana': res['nombre_loteria'],
                    'origen_hora_manana': str(res['hora']),
                }
            print(f"  - {str(res['hora'])} {res['nombre_loteria']}: {res['animalito_nombre']} ({res['animalito_numero']})")

    if not pool_manana:
        print("No se encontraron animalitos ganadores en el rango horario de la mañana especificado.")
        return {'saltos_encontrados': []}

    saltos_encontrados = []
    print("\nComprobando 'saltos' en sorteos posteriores del día:")
    for res in todos_los_resultados_del_dia:
        # Filtramos resultados de la tarde (1:00 PM en adelante)
        if res['hora'] > hora_limite_manana or res['hora'] == timedelta(hours=1):
            animal_actual = (res['animalito_nombre'], res['animalito_numero'])
            
            if animal_actual in pool_manana:
                info_origen = pool_manana[animal_actual]
                
                salto_info = {
                    'animal': animal_actual[0],
                    'numero': animal_actual[1],
                    'origen_loteria_manana': info_origen['origen_loteria_manana'],
                    'origen_hora_manana': info_origen['origen_hora_manana'],
                    'destino_loteria': res['nombre_loteria'],
                    'destino_hora': str(res['hora']),
                    'fecha': res['fecha'].strftime('%Y-%m-%d')
                }
                
                if salto_info not in saltos_encontrados:
                    saltos_encontrados.append(salto_info)
                    print(f"  ¡Salto detectado! {animal_actual[0]} ({animal_actual[1]})")
                    print(f"    Salió en la mañana ({info_origen['origen_hora_manana']} en {info_origen['origen_loteria_manana']})")
                    print(f"    Reapareció en la tarde ({str(res['hora'])} en {res['nombre_loteria']})")

    if not saltos_encontrados:
        print("No se detectaron saltos de animalitos de la mañana a sorteos posteriores del día.")
    
    return {'saltos_encontrados': saltos_encontrados}


def obtener_resultados_anteriores(conexion, id_loteria, dias_atras=730):
    resultados_historicos = []
    cursor = None
    try:
        cursor = conexion.cursor(dictionary=True)
        
        fecha_limite = datetime.now().date() - timedelta(days=dias_atras)

        query = """
        SELECT s.fecha, s.hora, a.nombre as animalito_nombre, a.numero_asociado as animalito_numero
        FROM sorteos s
        JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
        WHERE s.id_loteria = %s AND s.fecha >= %s
        ORDER BY s.fecha DESC, s.hora DESC
        """
        cursor.execute(query, (id_loteria, fecha_limite))
        resultados_historicos = cursor.fetchall()
        print(f"Obtenidos {len(resultados_historicos)} resultados históricos para Lotería ID {id_loteria} en los últimos {dias_atras} días.")
        return resultados_historicos
    except Error as error:
        print(f"Error al obtener resultados anteriores: {error}")
        return []
    finally:
        if cursor:
            cursor.close()

def analizar_posibles_resultados(conexion, id_loteria, dias_analisis=730, top_n=5):
    print(f"\nAnalizando posibles resultados para Lotería ID {id_loteria} (últimos {dias_analisis} días)...")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)
    if not resultados_historicos:
        print("No hay suficientes datos históricos para el análisis.")
        return {
            'top_n_animales_mas_frecuentes': [],
            'animales_que_no_han_salido_recientemente': []
        }

    conteo_animalitos = Counter()
    ultima_fecha_salida = {}
    
    # Ordenar por fecha para encontrar la última salida
    resultados_historicos.sort(key=lambda x: x['fecha'], reverse=True)

    for res in resultados_historicos:
        animal_nombre = res['animalito_nombre']
        conteo_animalitos[animal_nombre] += 1
        if animal_nombre not in ultima_fecha_salida:
            ultima_fecha_salida[animal_nombre] = res['fecha']

    cursor = conexion.cursor(dictionary=True)
    query_animalitos = "SELECT nombre, numero_asociado FROM animalitos ORDER BY numero_asociado"
    cursor.execute(query_animalitos)
    todos_los_animalitos_db = {a['nombre']: a['numero_asociado'] for a in cursor.fetchall()}
    cursor.close()

    top_n_animales_mas_frecuentes_gui = []
    mas_frecuentes_raw = conteo_animalitos.most_common(top_n)
    
    print(f"Top {top_n} animales más frecuentes en el período:")
    for animal, freq in mas_frecuentes_raw:
        ultima_vez_str = "N/A"
        if animal in ultima_fecha_salida:
            ultima_vez_str = ultima_fecha_salida[animal].strftime('%Y-%m-%d')
        
        top_n_animales_mas_frecuentes_gui.append({
            'animalito': animal,
            'numero': todos_los_animalitos_db.get(animal, 'N/A'),
            'frecuencia': freq,
            'ultima_vez': ultima_vez_str
        })
        print(f" - {animal} ({todos_los_animalitos_db.get(animal, 'N/A')}) - {freq} veces (Última vez: {ultima_vez_str})")


    animales_que_no_han_salido_recientemente = []
    animalitos_no_salidos = [
        nombre for nombre in todos_los_animalitos_db if nombre not in conteo_animalitos
    ]
    
    if animalitos_no_salidos:
        print("\nAnimales que NO HAN SALIDO en el período de análisis (potencialmente 'fríos'):")
        for animal in animalitos_no_salidos:
             animales_que_no_han_salido_recientemente.append({
                'animalito': animal,
                'numero': todos_los_animalitos_db.get(animal, 'N/A'),
                'dias_sin_salir': dias_analisis,
                'ultima_vez': 'Nunca en este período'
            })
             print(f" - {animal} ({todos_los_animalitos_db.get(animal, 'N/A')})")
    else:
        hoy = datetime.now().date()
        animales_frios_calculados = []
        for animal in todos_los_animalitos_db.keys():
            if animal in ultima_fecha_salida:
                dias_sin_salir = (hoy - ultima_fecha_salida[animal]).days
                animales_frios_calculados.append({
                    'animalito': animal,
                    'numero': todos_los_animalitos_db.get(animal, 'N/A'),
                    'dias_sin_salir': dias_sin_salir,
                    'ultima_vez': ultima_fecha_salida[animal].strftime('%Y-%m-%d')
                })
        
        animales_frios_calculados.sort(key=lambda x: x['dias_sin_salir'], reverse=True)
        animales_que_no_han_salido_recientemente = animales_frios_calculados[:5]

        print(f"\nTop 5 animales con más días sin salir (pero salieron al menos una vez en el historia):")
        for animal_info in animales_que_no_han_salido_recientemente:
             print(f" - {animal_info['animalito']} ({animal_info['numero']}): Última vez {animal_info['ultima_vez']} ({animal_info['dias_sin_salir']} días sin salir)")

    return {
        'top_n_animales_mas_frecuentes': top_n_animales_mas_frecuentes_gui,
        'animales_que_no_han_salido_recientemente': animales_que_no_han_salido_recientemente,
    }


def analizar_frecuencia_por_horario(conexion, id_loteria, dias_analisis=730, top_n_horarios=3, top_n_animales_por_horario=3):
    print(f"\nAnalizando frecuencia y ciclo de repetición por horario para Lotería ID {id_loteria} (últimos {dias_analisis} días)...")
    
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos:
        print("No hay suficientes datos históricos para el análisis por horario.")
        return {}
    
    cursor = conexion.cursor(dictionary=True)
    query_animalitos = "SELECT nombre, numero_asociado FROM animalitos"
    cursor.execute(query_animalitos)
    animalitos_map = {a['nombre']: a['numero_asociado'] for a in cursor.fetchall()}
    cursor.close()

    fechas_por_animalito_y_horario = {}
    
    for res in resultados_historicos:
        hora = res['hora']
        animalito = res['animalito_nombre']
        fecha = res['fecha']
        
        numero = animalitos_map.get(animalito, 'N/A')
        
        if (hora, animalito) not in fechas_por_animalito_y_horario:
            fechas_por_animalito_y_horario[(hora, animalito)] = {'fechas': [], 'numero': numero}
        fechas_por_animalito_y_horario[(hora, animalito)]['fechas'].append(fecha)

    frecuencia_y_ciclo = {}
    fecha_actual = datetime.now().date()
    for (hora, animalito), data in fechas_por_animalito_y_horario.items():
        if hora not in frecuencia_y_ciclo:
            frecuencia_y_ciclo[hora] = {}
        
        fechas = sorted(data['fechas'])
        frecuencia = len(fechas)
        dias_promedio = 0
        
        # Calcular días promedio de repetición
        if frecuencia > 1:
            diferencia_total = (fechas[-1] - fechas[0]).days
            if diferencia_total > 0:
                dias_promedio = diferencia_total / (frecuencia - 1)
        
        # Calcular días desde la última salida y propensión
        ultima_salida = fechas[-1]
        dias_sin_salir = (fecha_actual - ultima_salida).days
        propenso = dias_sin_salir >= dias_promedio if dias_promedio > 0 else False
        
        frecuencia_y_ciclo[hora][animalito] = {
            'frecuencia': frecuencia,
            'numero': data['numero'],
            'dias_promedio_repeticion': dias_promedio,
            'ultima_salida': ultima_salida,
            'dias_desde_ultima_salida': dias_sin_salir,
            'propenso_a_salir': propenso
        }

    horarios_ordenados = sorted(frecuencia_y_ciclo.keys())
    print("\nFrecuencia y ciclo de repetición por horario:")

    analisis_detallado = {}
    for hora in horarios_ordenados:
        conteo_animales_en_hora = frecuencia_y_ciclo[hora]
        top_animales_hora = sorted(conteo_animales_en_hora.items(), key=lambda x: x[1]['frecuencia'], reverse=True)[:top_n_animales_por_horario]

        if top_animales_hora:
            print(f"  Horario {hora}:")
            analisis_detallado[hora] = []
            for animal, data in top_animales_hora:
                propenso_str = "Sí" if data['propenso_a_salir'] else "No"
                analisis_detallado[hora].append({
                    'animalito': animal,
                    'numero': data['numero'],
                    'frecuencia': data['frecuencia'],
                    'dias_promedio_repeticion': data['dias_promedio_repeticion'],
                    'ultima_salida': data['ultima_salida'],
                    'dias_desde_ultima_salida': data['dias_desde_ultima_salida'],
                    'propenso_a_salir': propenso_str
                })
                dias_prom_str = f"{data['dias_promedio_repeticion']:.2f}"
                print(f"    - {animal} ({data['numero']}): {data['frecuencia']} veces (repite en promedio cada {dias_prom_str} días)")
                print(f"      - Última salida en este horario: {data['ultima_salida'].strftime('%Y-%m-%d')} ({data['dias_desde_ultima_salida']} días sin salir)")
                print(f"      - Propensión a salir hoy: {propenso_str}")
    
    return analisis_detallado

def analizar_frecuencia_por_horario_interloterias(conexion, dias_analisis=730, top_n_animales_por_horario=3):
    """
    Analiza la frecuencia y el ciclo de repetición de los animalitos por horario,
    agrupando los resultados de todas las loterías.
    """
    print(f"\n--- Analizando frecuencia por horario (todas las loterías, últimos {dias_analisis} días) ---")
    
    fecha_fin = datetime.now().date()
    fecha_inicio = fecha_fin - timedelta(days=dias_analisis)

    cursor = conexion.cursor(dictionary=True)
    query = """
    SELECT s.hora AS hora_sorteo, a.nombre AS animalito_nombre, a.numero_asociado AS animalito_numero, s.fecha AS fecha_salida
    FROM sorteos s
    JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
    WHERE s.fecha BETWEEN %s AND %s
    ORDER BY s.hora, s.fecha
    """
    cursor.execute(query, (fecha_inicio, fecha_fin))
    resultados_historicos = cursor.fetchall()
    cursor.close()

    if not resultados_historicos:
        print("No hay suficientes datos históricos para el análisis de frecuencia inter-lotería.")
        return {}

    fechas_por_animalito_y_horario = {}
    
    for res in resultados_historicos:
        hora = res['hora_sorteo']
        animalito = res['animalito_nombre']
        fecha = res['fecha_salida']
        numero = res['animalito_numero']
        
        if (hora, animalito) not in fechas_por_animalito_y_horario:
            fechas_por_animalito_y_horario[(hora, animalito)] = {'fechas': [], 'numero': numero}
        fechas_por_animalito_y_horario[(hora, animalito)]['fechas'].append(fecha)

    frecuencia_y_ciclo = {}
    fecha_actual = datetime.now().date()
    for (hora, animalito), data in fechas_por_animalito_y_horario.items():
        if hora not in frecuencia_y_ciclo:
            frecuencia_y_ciclo[hora] = {}
        
        fechas = sorted(data['fechas'])
        frecuencia = len(fechas)
        dias_promedio = 0
        if frecuencia > 1:
            diferencia_total = (fechas[-1] - fechas[0]).days
            if diferencia_total > 0:
                dias_promedio = diferencia_total / (frecuencia - 1)
        
        ultima_salida = fechas[-1]
        dias_sin_salir = (fecha_actual - ultima_salida).days
        propenso = dias_sin_salir >= dias_promedio if dias_promedio > 0 else False

        frecuencia_y_ciclo[hora][animalito] = {
            'frecuencia': frecuencia,
            'numero': data['numero'],
            'dias_promedio_repeticion': dias_promedio,
            'ultima_salida': ultima_salida,
            'dias_desde_ultima_salida': dias_sin_salir,
            'propenso_a_salir': propenso
        }

    horarios_ordenados = sorted(frecuencia_y_ciclo.keys())
    print("\nFrecuencia global y ciclo de repetición de animalitos por horario:")
    analisis_detallado = {}
    for hora in horarios_ordenados:
        conteo_animales_en_hora = frecuencia_y_ciclo[hora]
        top_animales_hora = sorted(conteo_animales_en_hora.items(), key=lambda x: x[1]['frecuencia'], reverse=True)[:top_n_animales_por_horario]

        if top_animales_hora:
            print(f"  Horario {hora}:")
            analisis_detallado[hora] = []
            for animal, data in top_animales_hora:
                propenso_str = "Sí" if data['propenso_a_salir'] else "No"
                analisis_detallado[hora].append({
                    'animalito': animal,
                    'numero': data['numero'],
                    'frecuencia': data['frecuencia'],
                    'dias_promedio_repeticion': data['dias_promedio_repeticion'],
                    'ultima_salida': data['ultima_salida'],
                    'dias_desde_ultima_salida': data['dias_desde_ultima_salida'],
                    'propenso_a_salir': propenso_str
                })
                dias_prom_str = f"{data['dias_promedio_repeticion']:.2f}"
                print(f"    - {animal} ({data['numero']}): {data['frecuencia']} veces (repite en promedio cada {dias_prom_str} días)")
                print(f"      - Última salida en este horario: {data['ultima_salida'].strftime('%Y-%m-%d')} ({data['dias_desde_ultima_salida']} días sin salir)")
                print(f"      - Propensión a salir hoy: {propenso_str}")
    
    return analisis_detallado

def analizar_rachas_animalitos(conexion, id_loteria, dias_analisis=730):
    print(f"\nAnalizando rachas para Lotería ID {id_loteria}...")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)
    
    if not resultados_historicos:
        print("No hay suficientes datos históricos para analizar rachas.")
        return {'animales_en_racha': [], 'animales_frios': []}
    
    hoy = datetime.now().date()
    ultima_fecha_salida = {}
    conteo_reciente = Counter()

    # Invertir el orden para contar las rachas calientes de forma eficiente
    resultados_historicos.sort(key=lambda x: (x['fecha'], x['hora']), reverse=True)

    # Contar ocurrencias recientes para rachas calientes
    for res in resultados_historicos:
        conteo_reciente[res['animalito_nombre']] += 1
    
    # Identificar animales en racha caliente (ej. salieron 2 o más veces en el período)
    animales_en_racha = []
    for animal, conteo in conteo_reciente.items():
        if conteo >= 2:
            numero = obtener_numero_animalito(conexion, animal)
            animales_en_racha.append({'animalito': animal, 'numero': numero, 'conteo': conteo})
    
    # Ordenar por el conteo
    animales_en_racha.sort(key=lambda x: x['conteo'], reverse=True)

    # Analizar animales fríos (días sin salir)
    resultados_historicos.sort(key=lambda x: x['fecha'], reverse=True)
    
    for res in resultados_historicos:
        animal = res['animalito_nombre']
        if animal not in ultima_fecha_salida:
            ultima_fecha_salida[animal] = res['fecha']

    animales_frios = []
    cursor = conexion.cursor(dictionary=True)
    query_animalitos = "SELECT nombre, numero_asociado FROM animalitos ORDER BY numero_asociado"
    cursor.execute(query_animalitos)
    todos_los_animalitos = [a['nombre'] for a in cursor.fetchall()]
    cursor.close()

    for animal in todos_los_animalitos:
        if animal in ultima_fecha_salida:
            dias_sin_salir = (hoy - ultima_fecha_salida[animal]).days
            numero = obtener_numero_animalito(conexion, animal)
            animales_frios.append({
                'animalito': animal,
                'numero': numero,
                'dias_sin_salir': dias_sin_salir,
                'ultima_vez': ultima_fecha_salida[animal].strftime('%Y-%m-%d')
            })
        else:
            numero = obtener_numero_animalito(conexion, animal)
            animales_frios.append({
                'animalito': animal,
                'numero': numero,
                'dias_sin_salir': dias_analisis, # No salió en el período
                'ultima_vez': 'Nunca en este período'
            })
    
    animales_frios.sort(key=lambda x: x['dias_sin_salir'], reverse=True)
    
    print("\nAnálisis de Rachas Calientes:")
    if animales_en_racha:
        for racha in animales_en_racha:
            print(f" - {racha['animalito']} ({racha['numero']}): Salió {racha['conteo']} veces recientemente.")
    else:
        print(" - No se encontraron rachas calientes.")

    print("\nAnálisis de Animales Fríos:")
    if animales_frios:
        for frio in animales_frios[:5]:
            print(f" - {frio['animalito']} ({frio['numero']}): Última vez {frio['ultima_vez']} ({frio['dias_sin_salir']} días sin salir).")
    else:
        print(" - No hay datos de animales fríos.")

    return {'animales_en_racha': animales_en_racha, 'animales_frios': animales_frios}

def analizar_patrones_secuenciales(conexion, id_loteria, dias_analisis=730, min_frecuencia=2):
    print(f"\nAnalizando patrones secuenciales para Lotería ID {id_loteria}...")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos:
        print("No hay suficientes datos históricos para el análisis de patrones.")
        return {'patrones_frecuentes': []}

    resultados_historicos.sort(key=lambda x: (x['fecha'], x['hora']))
    
    secuencias = []
    
    # Generar secuencias de dos animales consecutivos
    for i in range(len(resultados_historicos) - 1):
        actual = resultados_historicos[i]['animalito_nombre']
        siguiente = resultados_historicos[i+1]['animalito_nombre']
        secuencias.append((actual, siguiente))

    conteo_patrones = Counter(secuencias)
    
    patrones_frecuentes = []
    for patron, conteo in conteo_patrones.items():
        if conteo >= min_frecuencia:
            patrones_frecuentes.append((patron, conteo))

    patrones_frecuentes.sort(key=lambda x: x[1], reverse=True)

    print("\nPatrones secuenciales frecuentes:")
    if patrones_frecuentes:
        for patron, conteo in patrones_frecuentes:
            print(f" - {patron[0]} -> {patron[1]}: {conteo} veces")
    else:
        print(" - No se encontraron patrones secuenciales significativos.")
        
    return {'patrones_frecuentes': patrones_frecuentes}


def obtener_animalitos_con_grupo(conexion):
    """Obtiene todos los animalitos con su número y grupo asociado."""
    animalitos_con_grupo = {}
    cursor = None
    try:
        cursor = conexion.cursor(dictionary=True)
        query = "SELECT nombre, numero_asociado, grupo_id FROM animalitos"
        cursor.execute(query)
        resultados = cursor.fetchall()
        for res in resultados:
            animalitos_con_grupo[res['nombre']] = {
                'numero': res['numero_asociado'],
                'grupo_id': res['grupo_id']
            }
    except Error as error:
        print(f"Error al obtener animalitos con grupo: {error}")
    finally:
        if cursor:
            cursor.close()
    return animalitos_con_grupo
def obtener_ultimo_resultado_global(conexion):
    """
    Obtiene el último animalito ganador a nivel global, sin importar la lotería.
    """
    try:
        cursor = conexion.cursor(dictionary=True)
        query = """
        SELECT a.nombre AS animalito_nombre
        FROM sorteos s
        JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
        ORDER BY s.fecha DESC, s.hora DESC
        LIMIT 1
        """
        cursor.execute(query)
        resultado = cursor.fetchone()
        cursor.close()
        return resultado
    except Error as e:
        print(f"Error al obtener el último resultado global: {e}")
        return None


def analizar_frecuencia_por_dia_semana(conexion, id_loteria, dias_analisis=730, top_n_dias=3, top_n_animales=3):
    print(f"\n--- Analizando frecuencia por día de la semana para Lotería ID {id_loteria} ---")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos:
        print("No hay suficientes datos para este análisis.")
        return {}

    frecuencia_por_dia = {i: Counter() for i in range(7)}
    dias_nombres = ["Lunes", "Martes", "Miércoles", "Jueves", "Viernes", "Sábado", "Domingo"]

    for res in resultados_historicos:
        dia_semana = res['fecha'].weekday()
        animalito = res['animalito_nombre']
        frecuencia_por_dia[dia_semana][animalito] += 1
    
    analisis_detallado = {}
    for dia_numero, conteo_animales in frecuencia_por_dia.items():
        if not conteo_animales:
            continue
            
        dia_nombre = dias_nombres[dia_numero]
        top_animales = conteo_animales.most_common(top_n_animales)
        
        analisis_detallado[dia_nombre] = []
        for animal, freq in top_animales:
            numero = obtener_numero_animalito(conexion, animal)
            analisis_detallado[dia_nombre].append({
                'animalito': animal,
                'numero': numero,
                'frecuencia': freq
            })
    
    print("Análisis de frecuencia por día de la semana completado.")
    return analisis_detallado
def analizar_frecuencia_global_por_dia_semana(conexion, dias_analisis=730):
    """
    Analiza la frecuencia de salida de cada animalito por día de la semana a nivel global.
    """
    print(f"\n--- Analizando frecuencia por día de la semana (todas las loterías, últimos {dias_analisis} días) ---")

    fecha_fin = datetime.now().date()
    fecha_inicio = fecha_fin - timedelta(days=dias_analisis)

    cursor = conexion.cursor(dictionary=True)
    query = """
    SELECT DAYOFWEEK(fecha) as dia_semana_num, a.nombre as animalito_nombre, COUNT(*) as frecuencia
    FROM sorteos s
    JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
    WHERE s.fecha BETWEEN %s AND %s
    GROUP BY dia_semana_num, animalito_nombre
    ORDER BY dia_semana_num, frecuencia DESC
    """
    cursor.execute(query, (fecha_inicio, fecha_fin))
    resultados = cursor.fetchall()
    cursor.close()

    dias_nombres = {
        1: 'Domingo', 2: 'Lunes', 3: 'Martes', 4: 'Miércoles',
        5: 'Jueves', 6: 'Viernes', 7: 'Sábado'
    }

    frecuencia_por_dia = {}
    for res in resultados:
        dia_nombre = dias_nombres.get(res['dia_semana_num'])
        if dia_nombre not in frecuencia_por_dia:
            frecuencia_por_dia[dia_nombre] = []
        frecuencia_por_dia[dia_nombre].append({
            'animalito': res['animalito_nombre'],
            'frecuencia': res['frecuencia']
        })
    
    # Imprimir los resultados en el log
    if frecuencia_por_dia:
        print("\nResultados del análisis global de frecuencia por día de la semana:")
        for dia, animales in frecuencia_por_dia.items():
            print(f"  - Día {dia}:")
            for i, animal_data in enumerate(animales[:5]):  # Mostrar los top 5 de cada día
                print(f"    - {animal_data['animalito']}: {animal_data['frecuencia']} veces")

    return {'frecuencia_global_dia': frecuencia_por_dia}



def analizar_terminaciones(conexion, id_loteria, dias_analisis=730, top_n=5):
    print(f"\n--- Analizando frecuencia de terminaciones para Lotería ID {id_loteria} ---")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos:
        print("No hay suficientes datos para este análisis.")
        return {}
    
    conteo_terminaciones = Counter()
    for res in resultados_historicos:
        if res['animalito_numero'] and res['animalito_numero'].isdigit():
            terminacion = res['animalito_numero'][-1]
            conteo_terminaciones[terminacion] += 1
    
    top_terminaciones = conteo_terminaciones.most_common(top_n)
    
    print("Top terminaciones más frecuentes:")
    for term, freq in top_terminaciones:
        print(f"  - Terminación '{term}': {freq} veces.")

    return {'terminaciones_frecuentes': top_terminaciones}


def analizar_grupos(conexion, id_loteria, dias_analisis=730, top_n=3):
    print(f"\n--- Analizando frecuencia de grupos para Lotería ID {id_loteria} ---")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)
    
    if not resultados_historicos:
        print("No hay suficientes datos para este análisis.")
        return {}
        
    animalitos_con_grupo = obtener_animalitos_con_grupo(conexion)
    conteo_grupos = Counter()
    
    for res in resultados_historicos:
        animal = res['animalito_nombre']
        if animal in animalitos_con_grupo:
            grupo_id = animalitos_con_grupo[animal]['grupo_id']
            conteo_grupos[grupo_id] += 1
    
    top_grupos = conteo_grupos.most_common(top_n)
    
    print("Top grupos más frecuentes:")
    for grupo_id, freq in top_grupos:
        print(f"  - Grupo {grupo_id}: {freq} veces.")
    
    return {'grupos_frecuentes': top_grupos}
def analizar_ciclo_salida(conexion, id_loteria, dias_analisis=730, top_n=5):
    print(f"\n--- Analizando ciclo de salida para Lotería ID {id_loteria} ---")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos:
        print("No hay suficientes datos para este análisis.")
        return {}

    fechas_aparicion = {}
    for res in resultados_historicos:
        animal = res['animalito_nombre']
        fecha = res['fecha']
        if animal not in fechas_aparicion:
            fechas_aparicion[animal] = []
        fechas_aparicion[animal].append(fecha)

    ciclo_promedio = {}
    dias_sin_salir = {}
    fecha_hoy = datetime.now().date()
    
    for animal, fechas in fechas_aparicion.items():
        if len(fechas) > 1:
            diferencias = [(fechas[i] - fechas[i-1]).days for i in range(1, len(fechas))]
            if diferencias:
                ciclo_promedio[animal] = sum(diferencias) / len(diferencias)
        
        ultima_fecha = max(fechas)
        dias_sin_salir[animal] = (fecha_hoy - ultima_fecha).days
    
    animales_ciclo = {}
    for animal, dias_actuales in dias_sin_salir.items():
        promedio = ciclo_promedio.get(animal, 0)
        if promedio > 0:
            diferencia = dias_actuales - promedio
            if diferencia > 0:
                animales_ciclo[animal] = {'dias_sin_salir': dias_actuales, 'ciclo_promedio': promedio, 'diferencia_dias': diferencia}
                
    animales_ordenados = sorted(animales_ciclo.items(), key=lambda x: x[1]['diferencia_dias'], reverse=True)
    
    print("Análisis de ciclo de salida completado.")
    return {'animales_fuera_de_ciclo': animales_ordenados[:top_n]}
def analizar_patrones_secuenciales_profundo(conexion, id_loteria, dias_analisis=730, longitud_patron=3, top_n=5):
    print(f"\n--- Analizando patrones secuenciales de longitud {longitud_patron} para Lotería ID {id_loteria} ---")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos:
        print("No hay suficientes datos para este análisis.")
        return {}

    secuencia = []
    patrones_encontrados = Counter()
    
    for res in resultados_historicos:
        secuencia.append(res['animalito_nombre'])
        if len(secuencia) >= longitud_patron:
            patron = tuple(secuencia[-longitud_patron:])
            patrones_encontrados[patron] += 1
            
    top_patrones = patrones_encontrados.most_common(top_n)
    
    print(f"Top {top_n} patrones secuenciales más frecuentes:")
    for patron, conteo in top_patrones:
        print(f"  - {' -> '.join(patron)}: {conteo} veces.")
    
    return {'patrones_frecuentes_profundo': top_patrones}
def analizar_paridad_numeros(conexion, id_loteria, dias_analisis=730):
    print(f"\n--- Analizando paridad de números para Lotería ID {id_loteria} ---")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos:
        print("No hay suficientes datos para este análisis.")
        return {}
    
    conteo_paridad = Counter()
    for res in resultados_historicos:
        if res['animalito_numero'] and res['animalito_numero'].isdigit():
            numero = int(res['animalito_numero'])
            if numero % 2 == 0:
                conteo_paridad['par'] += 1
            else:
                conteo_paridad['impar'] += 1
    
    total_sorteos = sum(conteo_paridad.values())
    if total_sorteos == 0:
        return {}
        
    porcentaje_par = (conteo_paridad['par'] / total_sorteos) * 100
    porcentaje_impar = (conteo_paridad['impar'] / total_sorteos) * 100
    
    analisis_paridad = {
        'total_sorteos': total_sorteos,
        'par': {'conteo': conteo_paridad['par'], 'porcentaje': f"{porcentaje_par:.2f}%"},
        'impar': {'conteo': conteo_paridad['impar'], 'porcentaje': f"{porcentaje_impar:.2f}%"}
    }
    
    print(f"Análisis de paridad: {analisis_paridad}")
    return analisis_paridad
def analizar_correlacion_animalitos(conexion, id_loteria, dias_analisis=730, rango_sorteos=5, top_n=5):
    print(f"\n--- Analizando correlación de animalitos para Lotería ID {id_loteria} ---")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos or len(resultados_historicos) < 2:
        print("No hay suficientes datos para este análisis.")
        return {}

    correlaciones = Counter()
    for i in range(len(resultados_historicos) - 1):
        animal_actual = resultados_historicos[i]['animalito_nombre']
        for j in range(1, min(rango_sorteos + 1, len(resultados_historicos) - i)):
            animal_siguiente = resultados_historicos[i+j]['animalito_nombre']
            if animal_actual != animal_siguiente:
                correlaciones[(animal_actual, animal_siguiente)] += 1
    
    top_correlaciones = correlaciones.most_common(top_n)
    
    print(f"Top {top_n} pares de animalitos correlacionados:")
    for (animal1, animal2), conteo in top_correlaciones:
        print(f"  - {animal1} -> {animal2}: {conteo} veces.")

    return {'pares_correlacionados': top_correlaciones}
def analizar_correlacion_interloterias(conexion, dias_analisis=730, rango_sorteos=5, top_n=5):
    """
    Analiza la correlación secuencial entre animalitos en la secuencia unificada
    de todos los sorteos, sin importar la lotería.
    """
    print(f"\n--- Analizando correlación secuencial inter-loterías (últimos {dias_analisis} días) ---")
    
    fecha_fin = datetime.now().date()
    fecha_inicio = fecha_fin - timedelta(days=dias_analisis)

    cursor = conexion.cursor(dictionary=True)
    query = """
    SELECT a.nombre AS animalito_nombre
    FROM sorteos s
    JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
    WHERE s.fecha BETWEEN %s AND %s
    ORDER BY s.fecha, s.hora
    """
    cursor.execute(query, (fecha_inicio, fecha_fin))
    resultados_historicos = [res['animalito_nombre'] for res in cursor.fetchall()]
    cursor.close()

    if not resultados_historicos or len(resultados_historicos) < 2:
        print("No hay suficientes datos para este análisis.")
        return {'pares_correlacionados_interloterias': []}

    correlaciones = Counter()
    for i in range(len(resultados_historicos) - 1):
        animal_actual = resultados_historicos[i]
        for j in range(1, min(rango_sorteos + 1, len(resultados_historicos) - i)):
            animal_siguiente = resultados_historicos[i+j]
            if animal_actual != animal_siguiente:
                correlaciones[(animal_actual, animal_siguiente)] += 1
    
    top_correlaciones = correlaciones.most_common(top_n)
    
    print(f"Top {top_n} pares de animalitos correlacionados de forma secuencial (inter-loterías):")
    for (animal1, animal2), conteo in top_correlaciones:
        print(f"  - {animal1} -> {animal2}: {conteo} veces.")

    return {'pares_correlacionados_interloterias': top_correlaciones}

def analizar_decenas_frecuentes(conexion, id_loteria, dias_analisis=730, top_n=3):
    print(f"\n--- Analizando decenas frecuentes para Lotería ID {id_loteria} ---")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos:
        print("No hay suficientes datos para este análisis.")
        return {}

    conteo_decenas = Counter()
    for res in resultados_historicos:
        numero = int(res['animalito_numero'])
        if numero >= 0 and numero <= 9:
            decena = 0
        elif numero >= 10 and numero <= 19:
            decena = 10
        elif numero >= 20 and numero <= 29:
            decena = 20
        elif numero >= 30:
            decena = 30
        else:
            continue
        conteo_decenas[decena] += 1
    
    top_decenas = conteo_decenas.most_common(top_n)
    
    print(f"Top {top_n} decenas más frecuentes:")
    for decena, conteo in top_decenas:
        print(f"  - {decena}-{decena+9}: {conteo} veces.")
    
    return {'decenas_frecuentes': top_decenas}
def modelo_predictivo_por_hora(conexion, id_loteria, dias_analisis=730, top_n=5):
    print(f"\n--- Generando predicciones por hora para Lotería ID {id_loteria} ---")
    
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos:
        print("No hay suficientes datos para este análisis.")
        return {}

    # Agrupar los resultados por hora
    resultados_por_hora = {}
    for res in resultados_historicos:
        hora = res['hora'] # <-- CAMBIO AQUÍ
        animal = res['animalito_nombre']
        if hora not in resultados_por_hora:
            resultados_por_hora[hora] = Counter()
        resultados_por_hora[hora][animal] += 1
    
    predicciones_por_hora = {}
    for hora, conteo in resultados_por_hora.items():
        predicciones_por_hora[hora] = conteo.most_common(top_n)
    
    print("Modelo predictivo por hora generado.")
    return {'predicciones': predicciones_por_hora}
def analizar_patrones_interloterias(conexion, loterias_a_analizar=['Lotto Activo', 'Granjita', 'Selva Plus'], dias_analisis=730):
    print("\n--- Analizando patrones de resultados entre loterías ---")
    
    # 1. Obtener y agrupar todos los resultados por fecha y hora
    resultados_interloterias = {}
    resultados_por_dia_hora = {}
    
    for loteria in loterias_a_analizar:
        id_loteria = obtener_id_loteria(conexion, loteria)
        if id_loteria:
            resultados = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)
            for res in resultados:
                key = (res['fecha'].strftime('%Y-%m-%d'), res['hora'])
                if key not in resultados_por_dia_hora:
                    resultados_por_dia_hora[key] = {}
                resultados_por_dia_hora[key][loteria] = res['animalito_nombre']

    if not resultados_por_dia_hora:
        print("No hay suficientes datos para este análisis.")
        return {}

    # 2. Encontrar patrones de repetición de forma eficiente
    patrones_repeticion = Counter()
    
    # Ordenamos las claves para asegurarnos de que el análisis es secuencial
    fechas_unicas = sorted(list(set(k[0] for k in resultados_por_dia_hora.keys())))
    
    for fecha_actual in fechas_unicas:
        # Extraer los sorteos de la fecha actual
        sorteos_del_dia = {k: v for k, v in resultados_por_dia_hora.items() if k[0] == fecha_actual}
        
        # Ordenar los sorteos por hora
        horas_ordenadas = sorted(sorteos_del_dia.keys(), key=lambda x: datetime.strptime(str(x[1]), '%H:%M:%S').time())
        
        for i in range(len(horas_ordenadas)):
            key_actual = horas_ordenadas[i]
            animales_sorteo_actual = sorted(list(sorteos_del_dia[key_actual].values()))
            
            # Buscar si los animales del sorteo actual se repiten en sorteos posteriores del mismo día
            for j in range(i + 1, len(horas_ordenadas)):
                key_siguiente = horas_ordenadas[j]
                animales_sorteo_siguiente = list(sorteos_del_dia[key_siguiente].values())
                
                for animal_actual in animales_sorteo_actual:
                    if animal_actual in animales_sorteo_siguiente:
                        patron_key = tuple(animales_sorteo_actual) + (animal_actual,)
                        patrones_repeticion[patron_key] += 1
                        
    top_patrones = patrones_repeticion.most_common(5)
    
    print("Patrones de repetición inter-loterías encontrados:")
    if top_patrones:
        for patron, conteo in top_patrones:
            print(f"  - Animales {', '.join(patron[:-1])} llevaron a la repetición de {patron[-1]}: {conteo} veces.")
    else:
        print("  - No se encontraron patrones de repetición en el período analizado.")

    return {'patrones_interloterias': top_patrones}
def analizar_horarios_de_repeticion(conexion, id_loteria, dias_analisis=730):
    print(f"\n--- Analizando horarios y probabilidades de repetición para Lotería ID {id_loteria} ---")
    resultados_historicos = obtener_resultados_anteriores(conexion, id_loteria, dias_atras=dias_analisis)

    if not resultados_historicos or len(resultados_historicos) < 2:
        print("No hay suficientes datos para este análisis.")
        return {}
    
    repeticiones_por_hora = Counter()
    animal_repetido_conteo_historico = Counter() 
    animal_repetido_conteo_hoy = Counter()
    
    resultados_por_dia = {}
    for res in resultados_historicos:
        fecha_str = res['fecha'].strftime('%Y-%m-%d')
        if fecha_str not in resultados_por_dia:
            resultados_por_dia[fecha_str] = []
        resultados_por_dia[fecha_str].append(res)
    
    fecha_hoy_str = datetime.now().date().strftime('%Y-%m-%d')

    for fecha in resultados_por_dia:
        sorteos_del_dia = sorted(resultados_por_dia[fecha], key=lambda x: datetime.strptime(str(x['hora']), '%H:%M:%S').time())
        animales_previos = set()
        
        for i in range(len(sorteos_del_dia)):
            sorteo_actual = sorteos_del_dia[i]
            
            if sorteo_actual['animalito_nombre'] in animales_previos:
                repeticiones_por_hora[sorteo_actual['hora']] += 1
                animal_repetido_conteo_historico[sorteo_actual['animalito_nombre']] += 1
                
                if fecha == fecha_hoy_str:
                    animal_repetido_conteo_hoy[sorteo_actual['animalito_nombre']] += 1

            animales_previos.add(sorteo_actual['animalito_nombre'])
    
    top_horarios_repeticion = repeticiones_por_hora.most_common(3)
    animal_mas_propenso_repetir = animal_repetido_conteo_hoy.most_common(1)

    print("Top 3 horarios donde ocurren más repeticiones:")
    if top_horarios_repeticion:
        for hora, conteo in top_horarios_repeticion:
            print(f"  - {hora}: {conteo} repeticiones.")
    else:
        print("  - No se encontraron repeticiones en el período analizado.")

    print("\nAnimal más propenso a repetir del día de hoy:")
    if animal_mas_propenso_repetir:
        animal, conteo = animal_mas_propenso_repetir[0]
        print(f"  - {animal} (se repitió {conteo} veces hoy).")
    else:
        print("  - No hay suficientes datos para determinarlo el día de hoy.")
        
    return {
        'horarios_repeticion': top_horarios_repeticion,
        'animal_mas_propenso_repetir': animal_mas_propenso_repetir
    }

def analizar_patron_vecindad(conexion, dias_analisis=30):
    print(f"\n--- Analizando patrón de vecindad de animalitos (últimos {dias_analisis} días) ---")
    
    fecha_fin = datetime.now().date()
    fecha_inicio = fecha_fin - timedelta(days=dias_analisis)

    cursor = conexion.cursor(dictionary=True)
    try:
        query = """
        SELECT s.fecha, s.hora, a.numero_asociado AS numero_animalito, a.nombre AS nombre_animalito
        FROM sorteos s
        JOIN animalitos a ON s.id_animalito_ganador = a.id_animalito
        WHERE s.fecha BETWEEN %s AND %s
        ORDER BY s.fecha, s.hora
        """
        cursor.execute(query, (fecha_inicio, fecha_fin))
        resultados = cursor.fetchall()
    finally:
        cursor.close()

    if not resultados:
        print("No hay suficientes datos históricos para este análisis.")
        return {}

    patrones_vecinos = {}
    
    # Mapeo de número a nombre
    num_a_nombre = {int(r['numero_animalito']): r['nombre_animalito'] for r in resultados}
    # Nuevo mapeo de nombre a número para el final del bucle
    nombre_a_num = {r['nombre_animalito']: int(r['numero_animalito']) for r in resultados}

    for i in range(len(resultados) - 1):
        actual = resultados[i]
        siguiente = resultados[i+1]
        
        numero_actual = int(actual['numero_animalito'])
        numero_siguiente = int(siguiente['numero_animalito'])
        
        vecino_anterior = (numero_actual - 1 + 37) % 37
        vecino_siguiente = (numero_actual + 1) % 37
        
        # Corrección para el animalito 0 (Culebra)
        if numero_actual == 0:
            vecino_anterior = 36
        
        # Corrección para el animalito 36 (Paloma)
        if numero_actual == 36:
            vecino_siguiente = 0
            
        if numero_siguiente == vecino_anterior or numero_siguiente == vecino_siguiente:
            animal_actual = num_a_nombre.get(numero_actual)
            
            if animal_actual:
                if animal_actual not in patrones_vecinos:
                    patrones_vecinos[animal_actual] = 0
                patrones_vecinos[animal_actual] += 1

    patrones_ordenados = sorted(patrones_vecinos.items(), key=lambda item: item[1], reverse=True)
    
    print("\nFrecuencia con la que un animalito es seguido por un vecino:")
    analisis_patron = {}
    for animal, frecuencia in patrones_ordenados:
        # Corrección: ahora se usa el diccionario `nombre_a_num`
        numero = nombre_a_num.get(animal)
        analisis_patron[animal] = {
            'numero': numero,
            'frecuencia_patron_vecindad': frecuencia
        }
        print(f"  - {animal} ({numero}): {frecuencia} veces")
    
    return analisis_patron


def generar_predicciones(conexion, resultados_analisis):
    print("\nGenerando predicciones basadas en el análisis...")
    predicciones = []
    animalitos_potenciales = {}

    # Pre-cargar todos los animalitos y sus números en un diccionario para evitar múltiples consultas
    animalitos_cache = {}
    cursor_cache = conexion.cursor(dictionary=True)
    query_cache = "SELECT nombre, numero_asociado FROM animalitos"
    cursor_cache.execute(query_cache)
    for row in cursor_cache.fetchall():
        animalitos_cache[row['nombre']] = row['numero_asociado']
    cursor_cache.close()

    def agregar_prediccion(animal, razon, score=1.0):
        if animal not in animalitos_potenciales:
            numero = animalitos_cache.get(animal)
            if numero is None:
                print(f"Advertencia: Número para el animalito '{animal}' no encontrado.")
            animalitos_potenciales[animal] = {'score': 0, 'razones': set(), 'numero': numero}
        animalitos_potenciales[animal]['score'] += score
        animalitos_potenciales[animal]['razones'].add(razon)

    # Ponderar los resultados de los análisis individuales
    for loteria, analisis in resultados_analisis.items():
        if loteria in ['Saltos Matutinos', 'Correlacion Interloterias', 'Frecuencia Global por Horario', 'Frecuencia Global por Dia', 'Patron Vecindad']:
            continue
            
        # Rachas frías (mayor puntuación)
        if 'rachas' in analisis and 'animales_frios' in analisis['rachas']:
            for animal_frio in analisis['rachas']['animales_frios']:
                score = animal_frio['dias_sin_salir'] * 0.1
                agregar_prediccion(animal_frio['animalito'], f"Frío en {loteria} ({animal_frio['dias_sin_salir']} días)", score)

        # Frecuencia por horario (ponderación media)
        if 'frecuencia_horario' in analisis:
            for hora, animales in analisis['frecuencia_horario'].items():
                for animal_data in animales:
                    score = animal_data['frecuencia'] * 0.05
                    agregar_prediccion(animal_data['animalito'], f"Frecuencia alta en {loteria} a las {hora}", score)
        
        # Patrones secuenciales (ponderación alta)
        if 'patrones' in analisis and 'patrones_frecuentes' in analisis['patrones']:
            for patron, conteo in analisis['patrones']['patrones_frecuentes']:
                if conteo >= 3:
                    score = conteo * 0.2
                    agregar_prediccion(patron[1], f"Sale con frecuencia después de {patron[0]} en {loteria}", score)

        # Análisis de Frecuencia por Día de la Semana
        if 'frecuencia_dia_semana' in analisis:
            for dia_nombre, animales in analisis['frecuencia_dia_semana'].items():
                for animal_data in animales:
                    score = animal_data['frecuencia'] * 0.05
                    agregar_prediccion(animal_data['animalito'], f"Frecuencia alta en los días {dia_nombre} en {loteria}", score)
        
        # Análisis de Terminaciones
        if 'terminaciones' in analisis:
            animalitos_con_grupo = obtener_animalitos_con_grupo(conexion)
            for term, freq in analisis['terminaciones']['terminaciones_frecuentes']:
                for animal, datos in animalitos_con_grupo.items():
                    if datos['numero'] and str(datos['numero']).endswith(term):
                        score = freq * 0.1
                        agregar_prediccion(animal, f"Tendencia de terminación '{term}' en {loteria}", score)

        # Análisis de Grupos
        if 'grupos' in analisis:
            animalitos_con_grupo = obtener_animalitos_con_grupo(conexion)
            for grupo_id, freq in analisis['grupos']['grupos_frecuentes']:
                for animal, datos in animalitos_con_grupo.items():
                    if datos['grupo_id'] == grupo_id:
                        score = freq * 0.08
                        agregar_prediccion(animal, f"Tendencia de grupo ({grupo_id}) en {loteria}", score)
                        
        # Análisis de Ciclo de Salida
        if 'ciclo_salida' in analisis:
            for animal_data in analisis['ciclo_salida'].get('animales_fuera_de_ciclo', []):
                animal = animal_data[0]
                diferencia_dias = animal_data[1]['diferencia_dias']
                score = diferencia_dias * 0.5
                agregar_prediccion(animal, f"Fuera del ciclo promedio en {loteria} por {diferencia_dias} días", score)
                
        # Análisis de Patrones Secuenciales Profundos
        if 'patrones_profundos' in analisis:
            for patron, conteo in analisis['patrones_profundos'].get('patrones_frecuentes_profundo', []):
                if conteo >= 2:
                    animal_final = patron[-1]
                    score = conteo * 1.5
                    agregar_prediccion(animal_final, f"Patrón secuencial frecuente en {loteria}: {'->'.join(patron)}", score)

        # Análisis de Paridad de Números
        if 'paridad' in analisis:
            paridad_data = analisis['paridad']
            predominante = None
            score_base = 0.5
            if float(paridad_data['par']['porcentaje'].replace('%','')) > 60:
                predominante = 'par'
            elif float(paridad_data['impar']['porcentaje'].replace('%','')) > 60:
                predominante = 'impar'
            
            if predominante:
                for animal in animalitos_potenciales.keys():
                    numero = animalitos_potenciales[animal].get('numero')
                    if numero is not None and str(numero).isdigit():
                        if int(numero) % 2 == 0 and predominante == 'par':
                            agregar_prediccion(animal, f"Tendencia a la paridad en {loteria}", score_base)
                        elif int(numero) % 2 != 0 and predominante == 'impar':
                            agregar_prediccion(animal, f"Tendencia a la imparidad en {loteria}", score_base)
        
        # Análisis de Correlación
        if 'correlacion' in analisis and 'pares_correlacionados' in analisis['correlacion']:
            ultimo_sorteo = obtener_ultimo_resultado_por_loteria(conexion, loteria)
            if ultimo_sorteo:
                animal_reciente = ultimo_sorteo['animalito_nombre']
                for (animal_corr_a, animal_corr_b), conteo in analisis['correlacion']['pares_correlacionados']:
                    if animal_reciente == animal_corr_a:
                        score_correlacion = conteo * 0.8
                        agregar_prediccion(animal_corr_b, f"Correlación con {animal_reciente} en {loteria}", score_correlacion)

        # Análisis de Decenas
        if 'decenas' in analisis and 'decenas_frecuentes' in analisis['decenas']:
            decenas_frecuentes = [d[0] for d in analisis['decenas']['decenas_frecuentes']]
            animalitos_con_grupo = obtener_animalitos_con_grupo(conexion)
            for animal, datos in animalitos_con_grupo.items():
                if datos['numero'] is not None:
                    numero_str = str(datos['numero'])
                    if len(numero_str) > 1:
                        decena = int(numero_str[0]) * 10
                    elif numero_str == '0' or numero_str == '00':
                        decena = 0
                    else:
                        continue
                    if decena in decenas_frecuentes:
                        agregar_prediccion(animal, f"La decena {decena} está saliendo mucho en {loteria}", 1.0)
                        
        # Modelo Predictivo por Hora
        if 'modelo_hora' in analisis and 'predicciones' in analisis['modelo_hora']:
            hora_actual = datetime.now().strftime('%I:%M %p')
            predicciones_hora = analisis['modelo_hora']['predicciones'].get(hora_actual, [])
            for animal_predicho, conteo in predicciones_hora:
                score_modelo = conteo * 1.0
                agregar_prediccion(animal_predicho, f"Predicción del modelo por hora para las {hora_actual} en {loteria}", score_modelo)
        
        # NUEVO: Análisis de horarios de repetición
        if 'horarios_repeticion' in analisis and 'animal_mas_propenso_repetir' in analisis['horarios_repeticion']:
            animal_repetir_data = analisis['horarios_repeticion']['animal_mas_propenso_repetir']
            if animal_repetir_data:
                animal, conteo = animal_repetir_data[0]
                score = conteo * 1.5
                agregar_prediccion(animal, f"Animal más propenso a repetir en {loteria}", score)

    # Análisis Globales (fuera del bucle)
    if 'Correlacion Interloterias' in resultados_analisis and 'pares_correlacionados_interloterias' in resultados_analisis['Correlacion Interloterias']:
        print("Integrando correlación inter-loterías en las predicciones...")
        pares_correlacionados = resultados_analisis['Correlacion Interloterias']['pares_correlacionados_interloterias']
        if pares_correlacionados:
            ultimo_sorteo_global = obtener_ultimo_resultado_global(conexion)
            if ultimo_sorteo_global:
                animal_reciente = ultimo_sorteo_global['animalito_nombre']
                for (animal_corr_a, animal_corr_b), conteo in pares_correlacionados:
                    if animal_reciente == animal_corr_a:
                        score_correlacion = conteo * 0.8
                        agregar_prediccion(animal_corr_b, f"Correlación secuencial inter-loterías con {animal_reciente}", score_correlacion)
    
    if 'Saltos Matutinos' in resultados_analisis and 'saltos_encontrados' in resultados_analisis['Saltos Matutinos']:
        print("Integrando saltos matutinos en las predicciones...")
        for salto in resultados_analisis['Saltos Matutinos']['saltos_encontrados']:
            agregar_prediccion(salto['animal'], f"Salto de {salto['origen_loteria_manana']} a {salto['destino_loteria']}", score=5.0)

    if 'Frecuencia Global por Horario' in resultados_analisis and resultados_analisis['Frecuencia Global por Horario']:
        print("Integrando frecuencia global por horario en las predicciones...")
        frecuencia_global_por_hora = resultados_analisis['Frecuencia Global por Horario']
        for hora, animales in frecuencia_global_por_hora.items():
            for animal_data in animales:
                animal = animal_data['animalito']
                frecuencia = animal_data['frecuencia']
                score = frecuencia * 0.15 
                agregar_prediccion(animal, f"Frecuencia alta en todas las loterías a las {hora}", score)

    # NUEVO: Frecuencia Global por Día de la Semana
    if 'Frecuencia Global por Dia' in resultados_analisis and resultados_analisis['Frecuencia Global por Dia']:
        print("Integrando frecuencia global por día de la semana en las predicciones...")
        frecuencia_global_por_dia = resultados_analisis['Frecuencia Global por Dia']['frecuencia_global_dia']
        
        dia_actual_nombre = datetime.now().strftime('%A')
        
        # Mapeo de español a inglés si es necesario, o usar directamente en español
        dias_espanol = {'Monday': 'Lunes', 'Tuesday': 'Martes', 'Wednesday': 'Miércoles', 'Thursday': 'Jueves', 'Friday': 'Viernes', 'Saturday': 'Sábado', 'Sunday': 'Domingo'}
        dia_actual_nombre_es = dias_espanol.get(dia_actual_nombre, dia_actual_nombre)
        
        if dia_actual_nombre_es in frecuencia_global_por_dia:
            animales_del_dia = frecuencia_global_por_dia[dia_actual_nombre_es]
            for animal_data in animales:
                animal = animal_data['animalito']
                frecuencia = animal_data['frecuencia']
                score = frecuencia * 0.1
                agregar_prediccion(animal, f"Frecuencia alta en todas las loterías en los días {dia_actual_nombre_es}", score)
    
    # NUEVO: Análisis de Patrón de Vecindad
    if 'Patron Vecindad' in resultados_analisis and resultados_analisis['Patron Vecindad']:
        print("Integrando patrón de vecindad en las predicciones...")
        for animal, data in resultados_analisis['Patron Vecindad'].items():
            score = data['frecuencia_patron_vecindad'] * 0.5
            agregar_prediccion(animal, f"Patrón de Vecindad: seguido por un animalito vecino en {data['frecuencia_patron_vecindad']} ocasiones", score)


    # Convertir a formato de lista
    for animal, data in animalitos_potenciales.items():
        if data['numero'] is not None and data['score'] > 0:
            predicciones.append({
                'animal': animal,
                'numero': data['numero'],
                'score': data['score'],
                'razones': list(data['razones'])
            })

    # Ordenar por el score de mayor a menor
    predicciones.sort(key=lambda x: x['score'], reverse=True)

    print("\nPredicciones generadas:")
    if predicciones:
        for p in predicciones[:5]:
            print(f" - {p['animal']} ({p['numero']}) - Probabilidad: {p['score']:.2f}")
    else:
        print(" - No se generaron predicciones.")

    return predicciones



def ejecutar_scraper(text_output_widget):
    original_stdout = sys.stdout
    original_stderr = sys.stderr
    sys.stdout = TextRedirector(text_output_widget, "stdout")
    sys.stderr = sys.stderr

    text_output_widget.delete("1.0", tk.END)
    print("Iniciando proceso de extracción y análisis para el día de hoy...")

    conexion = obtener_conexion_db()
    if not conexion:
        print("No se pudo establecer conexión con la base de datos. Abortando scraping.")
        sys.stdout = original_stdout
        return None

    fecha_hoy = datetime.now().date()
    
    print("\n--- Procesando los resultados de Lotto Activo, Granjita y Selva Plus ---")
    
    url_principal = 'https://lotoven.com/animalitos/'
    contenido_html = obtener_html_con_selenium(url_principal)
    
    todos_los_analisis_resultados = {}
    
    if contenido_html:
        resultados_todos = parsear_resultados_lotoven(contenido_html)
        
        for resultado_sorteo in resultados_todos:
            nombre_loteria = resultado_sorteo['loteria']
            hora_sorteo = resultado_sorteo['hora']
            
            if nombre_loteria not in LOTERIAS_PERMITIDAS_HORARIOS or hora_sorteo not in LOTERIAS_PERMITIDAS_HORARIOS[nombre_loteria]:
                print(f"Advertencia: Lotería '{nombre_loteria}' no es oficial o el horario '{hora_sorteo}' no está permitido. Saltando.")
                continue
                
            nombre_animal_normalizado = resultado_sorteo['animalito'].title()
            
            id_loteria = obtener_id_loteria(conexion, nombre_loteria)
            if not id_loteria:
                print(f"No se encontró ID para la lotería '{nombre_loteria}'. Saltando resultado.")
                continue

            datos_animal = obtener_id_y_numero_animalito(conexion, nombre_animal_normalizado)
            if datos_animal:
                id_animalito, numero_animalito = datos_animal
                insertar_resultado_sorteo(conexion, fecha_hoy, resultado_sorteo['hora'], id_loteria, id_animalito, numero_animalito, nombre_animal_normalizado)
            else:
                print(f"Advertencia: Animalito '{nombre_animal_normalizado}' no encontrado en la DB. Saltando.")
    else:
        print("No se pudo obtener HTML de la página de Lotoven.")
        
    loterias_para_analisis = ['Lotto Activo', 'Granjita', 'Selva Plus']
    
    for nombre_loteria in loterias_para_analisis:
        id_loteria = obtener_id_loteria(conexion, nombre_loteria)
        if not id_loteria:
            continue
        
        print(f"\n--- Análisis de tendencias para {nombre_loteria} ---")
        analisis_resultados = analizar_posibles_resultados(conexion, id_loteria, dias_analisis=730, top_n=5)
        
        print(f"\n--- Análisis de frecuencia por horario para {nombre_loteria} ---")
        analisis_horario = analizar_frecuencia_por_horario(conexion, id_loteria, dias_analisis=730, top_n_horarios=5, top_n_animales_por_horario=3)

        print(f"\n--- Análisis de Rachas para {nombre_loteria} ---")
        analisis_rachas = analizar_rachas_animalitos(conexion, id_loteria=id_loteria, dias_analisis=730)

        print(f"\n--- Detección de Patrones Secuenciales para {nombre_loteria} ---")
        patrones_encontrados = buscar_patrones_secuenciales(conexion, id_loteria, longitud_patron=2, dias_atras=730, top_n_patrones=5)
        
        print(f"\n--- Análisis de Frecuencia por Día de la Semana para {nombre_loteria} ---")
        frecuencia_dia_semana = analizar_frecuencia_por_dia_semana(conexion, id_loteria, dias_analisis=730)
        
        print(f"\n--- Análisis de Terminaciones para {nombre_loteria} ---")
        analisis_terminaciones = analizar_terminaciones(conexion, id_loteria, dias_analisis=730)
        
        print(f"\n--- Análisis de Grupos para {nombre_loteria} ---")
        analisis_grupos = analizar_grupos(conexion, id_loteria, dias_analisis=730)
        
        print(f"\n--- Análisis de Horarios de Repetición para {nombre_loteria} ---")
        horarios_repeticion = analizar_horarios_de_repeticion(conexion, id_loteria)
        
        print("Top 3 horarios donde ocurren más repeticiones:")
        if horarios_repeticion['horarios_repeticion']:
            for hora, conteo in horarios_repeticion['horarios_repeticion']:
                print(f"  - {hora}: {conteo} repeticiones.")
        else:
            print("  - No se encontraron repeticiones en el período analizado.")
            
        print("\nAnimal más propenso a repetir del día de hoy:")
        if horarios_repeticion['animal_mas_propenso_repetir']:
            animal_nombre, repeticiones = horarios_repeticion['animal_mas_propenso_repetir'][0]
            print(f"  - {animal_nombre} (se repitió {repeticiones} veces hoy).")
        else:
            print("  - No se encontraron repeticiones de animalitos para el día de hoy.")

        # === NUEVAS FUNCIONES DE ANÁLISIS ===
        print(f"\n--- Análisis de Ciclo de Salida para {nombre_loteria} ---")
        analisis_ciclo_salida = analizar_ciclo_salida(conexion, id_loteria)
        
        print(f"\n--- Análisis de Patrones Secuenciales Profundo para {nombre_loteria} ---")
        patrones_profundos = analizar_patrones_secuenciales_profundo(conexion, id_loteria)
        
        print(f"\n--- Análisis de Paridad para {nombre_loteria} ---")
        analisis_paridad = analizar_paridad_numeros(conexion, id_loteria)

        print(f"\n--- Análisis de Correlación para {nombre_loteria} ---")
        analisis_correlacion = analizar_correlacion_animalitos(conexion, id_loteria)
        
        print(f"\n--- Análisis de Decenas para {nombre_loteria} ---")
        analisis_decenas = analizar_decenas_frecuentes(conexion, id_loteria)
        
        print(f"\n--- Modelo Predictivo por Hora para {nombre_loteria} ---")
        modelo_hora = modelo_predictivo_por_hora(conexion, id_loteria)

        
        # === FIN DE NUEVAS FUNCIONES ===

        todos_los_analisis_resultados[nombre_loteria] = {
            'tendencias': analisis_resultados,
            'frecuencia_horario': analisis_horario,
            'rachas': analisis_rachas,
            'patrones': patrones_encontrados,
            'frecuencia_dia_semana': frecuencia_dia_semana,
            'terminaciones': analisis_terminaciones,
            'grupos': analisis_grupos,
            'ciclo_salida': analisis_ciclo_salida,
            'patrones_profundos': patrones_profundos,
            'paridad': analisis_paridad,
            'correlacion': analisis_correlacion,
            'decenas': analisis_decenas,
            'modelo_hora': modelo_hora
        }

    # === Llamadas a las funciones de análisis globales ===
    analisis_correlacion_interloterias = analizar_correlacion_interloterias(conexion, dias_analisis=730, rango_sorteos=5, top_n=5)
    
    saltos_matutinos_global = analizar_saltos_matutinos(conexion, dias_analisis=1)
    
    frecuencia_global_por_horario = analizar_frecuencia_por_horario_interloterias(conexion, dias_analisis=730)
    
    # AÑADE ESTA NUEVA FUNCIÓN AQUÍ
    frecuencia_global_por_dia = analizar_frecuencia_global_por_dia_semana(conexion)
    
    # NUEVO: Análisis de Patrón de Vecindad
    print("\n--- Análisis de Patrón de Vecindad ---")
    analisis_patron_vecindad = analizar_patron_vecindad(conexion, dias_analisis=730)
    
    # === Fin de llamadas ===

    todos_los_analisis_resultados['Correlacion Interloterias'] = analisis_correlacion_interloterias
    todos_los_analisis_resultados['Saltos Matutinos'] = saltos_matutinos_global
    todos_los_analisis_resultados['Frecuencia Global por Horario'] = frecuencia_global_por_horario
    
    # Y AÑADE TAMBIÉN EL RESULTADO AL DICCIONARIO
    todos_los_analisis_resultados['Frecuencia Global por Dia'] = frecuencia_global_por_dia
    
    todos_los_analisis_resultados['Patron Vecindad'] = analisis_patron_vecindad

    predicciones_finales = generar_predicciones(conexion, todos_los_analisis_resultados)
    todos_los_analisis_resultados['Predicciones'] = predicciones_finales

    if conexion.is_connected():
        conexion.close()
    print("\nProceso de extracción de datos, guardado y análisis completado.")
    
    sys.stdout = original_stdout
    sys.stderr = original_stderr
    
    return todos_los_analisis_resultados

def ejecutar_scraper_historico(text_output_widget, dias_a_recolectar):
    """
    Función para ejecutar el scraping de datos históricos de forma optimizada.
    """
    original_stdout = sys.stdout
    original_stderr = sys.stderr
    sys.stdout = TextRedirector(text_output_widget, "stdout")
    sys.stderr = TextRedirector(text_output_widget, "stderr")
    
    text_output_widget.delete("1.0", tk.END)
    print(f"Iniciando recolección de datos históricos de los últimos {dias_a_recolectar} días...")
    
    conexion = obtener_conexion_db()
    if not conexion:
        print("No se pudo establecer conexión con la base de datos. Abortando recolección histórica.")
        sys.stdout = original_stdout
        sys.stderr = original_stderr
        return

    # Iniciar Selenium una sola vez
    driver = None
    try:
        servicio = Service(RUTA_CHROMEDRIVER)
        opciones_chrome = webdriver.ChromeOptions()
        opciones_chrome.add_argument('user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36')
        opciones_chrome.add_argument("--headless")
        driver = webdriver.Chrome(service=servicio, options=opciones_chrome)
        print("Controlador de Selenium iniciado exitosamente.")
    except WebDriverException as e:
        print(f"Error al iniciar el controlador de Selenium: {e}")
        print("Asegúrate que el archivo 'chromedriver.exe' esté en la ruta correcta y actualizado.")
        sys.stdout = original_stdout
        sys.stderr = original_stderr
        return
    
    
    for i in range(dias_a_recolectar):
        fecha_a_procesar = datetime.now().date() - timedelta(days=i)
        fecha_str = fecha_a_procesar.strftime('%Y-%m-%d')
        
        print(f"\n--- Procesando fecha: {fecha_str} ---")
        # Cambio de la URL a tu formato correcto
        url_historico = f"https://lotoven.com/animalitos/{fecha_str}"
        
        try:
            print(f"Abriendo página: {url_historico}")
            driver.get(url_historico)

            # Esperar a que los elementos del sorteo estén presentes
            WebDriverWait(driver, 30).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, ".counter-wrapper"))
            )
            contenido_html = driver.page_source
            print(f"HTML obtenido para {fecha_str}")
        except WebDriverException as e:
            print(f"Error de WebDriver al acceder a {url_historico}: {e}")
            contenido_html = None
        except Exception as e:
            print(f"Ocurrió un error inesperado con Selenium en {url_historico}: {e}")
            contenido_html = None
        
        if contenido_html:
            resultados_del_dia = parsear_resultados_lotoven(contenido_html, fecha_esperada=fecha_a_procesar)
            
            if not resultados_del_dia:
                print(f"No se encontraron resultados válidos para el {fecha_str}.")
                continue
            
            for resultado_sorteo in resultados_del_dia:
                nombre_loteria = resultado_sorteo['loteria']
                hora_sorteo = resultado_sorteo['hora']
                
                # Filtro: Por nombre de lotería y horario
                if nombre_loteria not in LOTERIAS_PERMITIDAS_HORARIOS or hora_sorteo not in LOTERIAS_PERMITIDAS_HORARIOS[nombre_loteria]:
                    continue
                    
                nombre_animal_normalizado = resultado_sorteo['animalito'].title()
                
                id_loteria = obtener_id_loteria(conexion, nombre_loteria)
                if not id_loteria:
                    continue

                datos_animal = obtener_id_y_numero_animalito(conexion, nombre_animal_normalizado)
                if datos_animal:
                    id_animalito, numero_animalito = datos_animal
                    insertar_resultado_sorteo(conexion, fecha_a_procesar, resultado_sorteo['hora'], id_loteria, id_animalito, numero_animalito, nombre_animal_normalizado)
                
            time.sleep(2)
        else:
            print(f"No se pudo obtener el HTML para la fecha {fecha_str}.")
    
    if driver:
        driver.quit()
        print("\nControlador de Selenium cerrado.")
        
    if conexion.is_connected():
        conexion.close()
    
    print("\nRecolección de datos históricos finalizada.")
    sys.stdout = original_stdout
    sys.stderr = original_stderr
    
if __name__ == "__main__":
    customtkinter.set_appearance_mode("System")
    customtkinter.set_default_color_theme("blue")

    app = App()
    app.mainloop()