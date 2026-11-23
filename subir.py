import json, os
from pymongo import MongoClient

MONGO_URI = "mongodb+srv://olivermeza164_db_user:TKLRe6e04mdwigFH@database.l5metuv.mongodb.net/"
client = MongoClient(MONGO_URI)
db = client["database"]  # nombre de tu base

carpeta = "database" # donde están tus .json

for archivo in os.listdir(carpeta):
    if not archivo.endswith(".json"):
        continue
    
    nombre_coleccion = archivo.replace(".json", "")
    coleccion = db[nombre_coleccion]
    
    with open(os.path.join(carpeta, archivo), "r") as f:
        datos = json.load(f)
    
    # Si es diccionario tipo {"8870209680": {...}}
    if isinstance(datos, dict):
        for user_id, info in datos.items():
            info["_id"] = str(user_id)
            coleccion.update_one(
                {"_id": str(user_id)},
                {"$set": info},
                upsert=True
            )
    # Si es lista
    elif isinstance(datos, list):
        for item in datos:
            coleccion.update_one(
                {"_id": str(item.get("id", item))},
                {"$set": item},
                upsert=True
            )
    
    print(f"Subido: {archivo} -> {nombre_coleccion}")

print("LISTO, TODO SUBIDO A MONGO")
