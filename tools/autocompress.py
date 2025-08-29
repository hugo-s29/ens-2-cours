import os
import hashlib
import json
import subprocess
from pathlib import Path

HASH_FILE = ".compressed_hashes.json"

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

# Find all *-uncompressed.pdf files recursively
pdf_files = list(Path(".").rglob("*-uncompressed.pdf"))

for pdf in pdf_files:
    pdf = str(pdf)
    compressed_pdf = pdf.replace("-uncompressed.pdf", ".pdf")

    current_hash = compute_md5(pdf)
    print(pdf)

    if previous_hashes.get(pdf) != current_hash:
        print(f"Compressing {pdf} -> {compressed_pdf} ...")
        subprocess.run(["convert", "-density", "125", pdf, "-quality", "95", "-compress", "JPEG", compressed_pdf], check=True)

        previous_hashes[pdf] = current_hash
    #else:
        # print(f"Skipping {pdf} (unchanged).")

with open(HASH_FILE, "w") as f:
    json.dump(previous_hashes, f, indent=4)
