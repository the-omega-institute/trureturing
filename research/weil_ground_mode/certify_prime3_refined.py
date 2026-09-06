"""Self-contained second-jet certificate for the c=3 Weil window.
Arithmetic routines below follow certify_prime3.py at PR5602 commit
461acf1bfacdb0884a2edc760716c29e4b321d96. New parts retain four boundary
moments and use exact per-entry quantization-radius energy. No zeta zeros
or eigensolver enter. Analytic domain/tail bridges are in the theory volume.
This is a directed-interval certificate, not a Lean kernel proof.
"""
from __future__ import annotations
import hashlib, json, math, pathlib, platform, time
from fractions import Fraction
import numpy as np
from mpmath import mp, iv
from sympy import bernoulli
import mpmath, sympy
if not __debug__: raise RuntimeError('Do not run with -O')
iv.dps=45
mp.dps=60
N=64; M=32768; BITS=40
CANDIDATE = (
    1884327, 1949881, 2454431, 1955838, 2267166, 2628844, 2019817, 2725995,
    2666928, 2258922, 3191558, 2627834, 2740665, 3535958, 2652877, 3431115,
    3691004, 2914967, 4199523, 3702151, 3543262, 4868979, 3743722, 4552854,
    5304731, 4078317, 5814371, 5510634, 4965730, 7089643, 5694160, 6550526,
    8139061, 6265021, 8774613, 8880841, 7751943, 11365368, 9561858, 10650784,
    13940578, 10893066, 15245277, 16256238, 14112283, 21456639, 18619811, 20944288,
    28759160, 22515646, 33301119, 36045767, 31375026, 51306542, 40139614, 48028821,
    55055748, 16558565, -14587791, -293594608, -638883816, -293594608, 0,
)
