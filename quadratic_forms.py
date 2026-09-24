# quadratic_forms.py
#
# Computations for Tables 2 and 3 of the paper (used in Propositions 4.5 and 4.8) and for the proof of Proposition 4.10.
#
# Run with:  sage -python quadratic_forms.py        (about 6 hours on one core, half of it for N = 720)
#
# Requires the Sage package mdsage by M. Derickx, https://github.com/koffie/mdsage (version 0.1.0).
# Install it with:  sage -pip install git+https://github.com/koffie/mdsage.git@v0.1.0
#
# For N in U_6 (resp. U_8) and every elliptic curve E/Q of positive rank with conductor dividing N and modular degree
# at most 6 (resp. 8), the script computes, following [DO24, Section 2], the quadratic form on Hom_Q(J_0(N), E) whose
# values are the degrees of the morphisms X_0(N) -> E (lines starting with ROW), and checks that it does not take the
# value 6 (resp. 8). Curves of larger modular degree are skipped by Lemma 3.3 (lines starting with SKIP).
# For N = 720 it checks that every elliptic curve of positive rank with conductor dividing 720 has modular degree at
# least 16, so by Lemma 3.3 there is no morphism X_0(720) -> E of degree 12 to such a curve.

import time
from sage.all import *
from mdsage.modular_degrees_oldforms import (modular_symbol_elliptic_curves,
    modular_symbol_elliptic_curves_divisors, degree_pairing, degree_quadratic_form)

U6 = [140, 180, 220, 252, 280, 288, 300, 348, 426, 432, 468, 472, 558, 560, 572, 576]
U8 = [360, 420, 440, 504, 528, 600, 672]

def curves_dividing(N):
    yield from modular_symbol_elliptic_curves_divisors(N)
    yield from modular_symbol_elliptic_curves(N)

def run(N, d):
    t = time.time()
    for A in curves_dividing(N):
        E = A.elliptic_curve()
        r = E.rank()
        if r == 0:
            continue
        degE = A.modular_degree()
        if degE > d:
            print(f"SKIP N={N} E={E.cremona_label()} rank={r} moddeg={degE} > {d}", flush=True)
            continue
        Q = degree_pairing(A, N)
        form = degree_quadratic_form(A, N)
        c = gcd(form.coefficients())
        cnt, maxnorm, vecs = pari.qfminim(Q, d)
        norms = sorted(set(int(vector(ZZ, list(v)) * Q * vector(ZZ, list(v))) for v in vecs.mattranspose())) if int(cnt) > 0 else []
        print(f"ROW N={N} E={E.cremona_label()} rank={r} moddeg={degE} content={c} form={c}*({form/c}) | norms<={d}: {norms}", flush=True)
        assert d not in norms
    print(f"DONE N={N} in {time.time()-t:.0f}s", flush=True)

for N in U6: run(N, 6)
for N in U8: run(N, 8)
# X_0(720): no positive rank E with conductor | 720 and modular degree < 16
t = time.time(); md = []
for A in curves_dividing(720):
    E = A.elliptic_curve()
    if E.rank() > 0:
        md.append((E.cremona_label(), A.modular_degree()))
print(f"N720 positive rank curves with conductor | 720 and their modular degrees: {md}", flush=True)
assert all(m >= 16 for _, m in md)
print(f"DONE N=720 in {time.time()-t:.0f}s", flush=True)
print("ALL_DONE", flush=True)
