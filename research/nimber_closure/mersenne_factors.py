# Factorisations of 2^n - 1 for the degrees option B (pseudo-Conway polynomials from On_2) needs:
# the 15 degrees missing from Lübeck's table (primitivity of rho_n) and every m <= 64 (discrete
# logarithms in GF(2^m)). Factors by GNU coreutils `factor`, each checked: the product is 2^n - 1
# and every factor passes sympy.isprime (deterministic below 2^64, BPSW above).
# Run: python3 research/nimber_closure/mersenne_factors.py  (writes data/mersenne_factors.txt)
import subprocess, sys, os
from concurrent.futures import ThreadPoolExecutor
from math import prod
from sympy import isprime

MISSING = [93, 94, 99, 104, 105, 106, 111, 112, 116, 117, 118, 122, 123, 124, 128]
NS = sorted(set(range(1, 65)) | set(MISSING))

def fac(n):
    out = subprocess.run(["factor", str(2**n - 1)], capture_output=True, text=True, check=True).stdout
    ps = [int(t) for t in out.split(":")[1].split()]
    assert prod(ps) == 2**n - 1, n
    assert all(isprime(p) for p in ps), n
    print(f"n = {n} done", file=sys.stderr, flush=True)
    return n, ps

with ThreadPoolExecutor(max_workers=os.cpu_count()) as ex:
    res = dict(ex.map(fac, NS))
path = os.path.join(os.path.dirname(__file__), "data", "mersenne_factors.txt")
with open(path, "w") as f:
    f.write("# n: prime factors of 2^n - 1 with multiplicity (mersenne_factors.py)\n")
    for n in NS:
        f.write(f"{n}: {' '.join(map(str, res[n]))}\n")
print("wrote", path, file=sys.stderr)
