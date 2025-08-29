import os
import hashlib
import json
import subprocess
import re
from pathlib import Path

HASH_FILE = ".compile_hashes.json"

if os.path.exists(HASH_FILE):
    with open(HASH_FILE, "r") as f:
        previous_hashes = json.load(f)
else:
    previous_hashes = {}

def compute_md5(file_path):
    hasher = hashlib.md5()
    with open(file_path, "rb") as f:
        while chunk := f.read(4096):
            hasher.update(chunk)
    return hasher.hexdigest()










# Compiling LaTeX here...


tex_files = [ str(tex) for tex in Path(".").rglob("*.tex") ]
tex_ignore = []

def get_tex_to_recompile(filename):
    reg = r"(chap\d\d/chap\d\d\.tex)|(chap\d\d.tex)|(td\d\d\.tex)"
    res, n = re.subn(reg, "main.tex", filename)

    if n > 0: return [ filename, res ]
    else: return [ filename ]

tex_to_recompile = set()

for tex in sorted(tex_files):
    current_hash = compute_md5(tex)

    if previous_hashes.get(tex) != current_hash:
        tex_to_recompile.update(get_tex_to_recompile(tex))
        previous_hashes[tex] = current_hash

for tex in tex_to_recompile:
    if tex in tex_ignore: continue

    path = Path(tex)
    print('Considering file ', tex, '...')
    subprocess.run(["cluttex", "-e", "lualatex", path.name], check=True, cwd=path.parent)









# Compiling Typst here...


typ_files = [ str(typ) for typ in Path(".").rglob("*.typ") ]
typ_ignore = [ 'global.typ' ]
typ_ignore += [ fn for fn in typ_files if fn.startswith('cours-mpi') ]

for typ in sorted(typ_files):
    current_hash = compute_md5(typ)

    if previous_hashes.get(typ) != current_hash and typ not in typ_ignore:
        path = Path(typ)
        subprocess.run(["typst", "compile", "--root", os.getcwd(), path.name], check=True, cwd=path.parent)

        previous_hashes[typ] = current_hash










with open(HASH_FILE, "w") as f:
    json.dump(previous_hashes, f, indent=4)
