import requests
from bs4 import BeautifulSoup
from datetime import datetime
import mysql.connector
from mysql.connector import Error
import re
# --- Configuración de la Base de Datos ---
# --- Configuración de la Base de Datos ---
CONFIG_DB = {
    'host': '127.0.0.1',
    'database': 'loterias',  # El nombre de tu base de datos en MySQL
    'user': 'root',              # Usuario por defecto de XAMPP para MySQL
    'password': ''               # Contraseña por defecto de XAMPP para MySQL (vacía)
}

def crear_base_de_datos():
    """Crea la base de datos si no existe."""
    conexion = None # Inicializar conexion a None
    cursor = None # Inicializar cursor a None
    try:
        conexion = mysql.connector.connect(
            host=CONFIG_DB['host'],
            user=CONFIG_DB['user'],
            password=CONFIG_DB['password']
        )
        if conexion.is_connected():
            cursor = conexion.cursor()
            cursor.execute(f"CREATE DATABASE IF NOT EXISTS {CONFIG_DB['database']}")
            print(f"Base de datos '{CONFIG_DB['database']}' verificada/creada exitosamente.")
    except Error as error:
        print(f"Error al crear la base de datos: {error}")
    finally:
        if cursor: # Verificar si cursor fue creado
            cursor.close()
        if conexion and conexion.is_connected(): # Verificar si conexion fue creada y está activa
            conexion.close()

def crear_tablas():
    """Conecta a la DB y crea las tablas."""
    conexion = None
    cursor = None
    try:
        conexion = mysql.connector.connect(**CONFIG_DB)
        if conexion.is_connected():
            cursor = conexion.cursor()

            # Crear tabla loterias
            cursor.execute("""
            CREATE TABLE IF NOT EXISTS loterias (
                id_loteria INT AUTO_INCREMENT PRIMARY KEY,
                nombre VARCHAR(50) NOT NULL UNIQUE,
                url_oficial VARCHAR(255)
            ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;
            """)
            print("Tabla 'loterias' verificada/creada exitosamente.")

            # Crear tabla animalitos (CORREGIDA: numero_asociado a VARCHAR para '00')
            cursor.execute("""
            CREATE TABLE IF NOT EXISTS animalitos (
                id_animalito INT AUTO_INCREMENT PRIMARY KEY,
                nombre VARCHAR(30) NOT NULL UNIQUE,
                numero_asociado VARCHAR(5) NOT NULL UNIQUE -- CAMBIO DE INT A VARCHAR
            ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;
            """)
            print("Tabla 'animalitos' verificada/creada exitosamente.")

            # Crear tabla sorteos (CORREGIDA: numero_ganador a VARCHAR)
            cursor.execute("""
            CREATE TABLE IF NOT EXISTS sorteos (
                id_sorteo INT AUTO_INCREMENT PRIMARY KEY,
                fecha DATE NOT NULL,
                hora TIME NOT NULL,
                id_loteria INT NOT NULL,
                id_animalito_ganador INT NOT NULL,
                numero_ganador VARCHAR(5) NOT NULL, -- CAMBIO DE INT A VARCHAR
                nombre_animalito_ganador VARCHAR(30) NOT NULL,
                FOREIGN KEY (id_loteria) REFERENCES loterias(id_loteria),
                FOREIGN KEY (id_animalito_ganador) REFERENCES animalitos(id_animalito)
            ) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;
            """)
            print("Tabla 'sorteos' verificada/creada exitosamente.")

    except Error as error:
        print(f"Error al conectar o crear tablas: {error}")
    finally:
        if cursor:
            cursor.close()
        if conexion and conexion.is_connected():
            conexion.close()

def insertar_datos_iniciales():
    """Inserta datos iniciales de loterías y animalitos."""
    conexion = None
    cursor = None
    try:
        conexion = mysql.connector.connect(**CONFIG_DB)
        if conexion.is_connected():
            cursor = conexion.cursor()

            # Insertar loterías (si no existen)
            loterias_data = [
                # NOTA: Las URLs de tuazar.com requerirán una nueva inspección de selectores
                # para el scraper, ya que su estructura HTML es diferente a las páginas oficiales.
                ('Lotto Activo', 'https://lotoven.com/animalitos/'),
                ('Granjita', 'https://lotoven.com/animalitos/'),
                ('Selva Plus', 'https://lotoven.com/animalitos/') # Esta sí es la oficial que inspeccionamos
            ]
            for nombre_loteria, url_loteria in loterias_data:
                try:
                    cursor.execute("INSERT INTO loterias (nombre, url_oficial) VALUES (%s, %s)", (nombre_loteria, url_loteria))
                    print(f"Lotería '{nombre_loteria}' insertada.")
                except mysql.connector.errors.IntegrityError as error_integridad:
                    if "Duplicate entry" in str(error_integridad):
                        print(f"Lotería '{nombre_loteria}' ya existe. Saltando.")
                    else:
                        raise error_integridad # Re-lanza si es otro error de integridad
            conexion.commit()

           
            
            animalitos_data = [
                ('Delfin', '0'),
                ('Ballena', '00'),
                ('Carnero', '1'),
                ('Toro', '2'),
                ('Ciempies', '3'),
                ('Alacrán', '4'),
                ('León', '5'),
                ('Rana', '6'),
                ('Perico', '7'),
                ('Ratón', '8'),
                ('Águila', '9'),
                ('Tigre', '10'),
                ('Gato', '11'),
                ('Caballo', '12'),
                ('Mono', '13'),
                ('Paloma', '14'),
                ('Zorro', '15'),
                ('Oso', '16'),
                ('Pavo', '17'),
                ('Burro', '18'),
                ('Chivo', '19'),
                ('Cochino', '20'),
                ('Gallo', '21'),
                ('Camello', '22'),
                ('Cebra', '23'),
                ('Iguana', '24'),
                ('Gallina', '25'),
                ('Vaca', '26'),
                ('Perro', '27'),
                ('Zamuro', '28'),
                ('Elefante', '29'),
                ('Caiman', '30'),
                ('Lapa', '31'), 
                ('Ardilla', '32'),
                ('Pescado', '33'),
                ('Venado', '34'),
                ('Jirafa', '35'),
                ('Culebra', '36'), 
            ]
            for nombre_animalito, numero_asociado_animalito in animalitos_data:
                try:
                    cursor.execute("INSERT INTO animalitos (nombre, numero_asociado) VALUES (%s, %s)", (nombre_animalito, numero_asociado_animalito))
                    print(f"Animalito '{nombre_animalito}' ({numero_asociado_animalito}) insertado.")
                except mysql.connector.errors.IntegrityError as error_integridad:
                    if "Duplicate entry" in str(error_integridad):
                        print(f"Animalito '{nombre_animalito}' ({numero_asociado_animalito}) ya existe. Saltando.")
                    else:
                        raise error_integridad
            conexion.commit()

    except Error as error:
        print(f"Error al insertar datos iniciales: {error}")
    finally:
        if cursor:
            cursor.close()
        if conexion and conexion.is_connected():
            conexion.close()


if __name__ == "__main__":
    print("Iniciando configuración de la base de datos...")
    crear_base_de_datos()
    crear_tablas()
    insertar_datos_iniciales()
    print("Configuración de la base de datos completada.")