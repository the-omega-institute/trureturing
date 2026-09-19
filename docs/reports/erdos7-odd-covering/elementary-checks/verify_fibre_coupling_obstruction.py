#!/usr/bin/env python3
"""Verify an actual complete forbidden family with an empty old survivor fibre.

Python 3.8+ standard library only. The mathematical proof extends the
construction to all heights at least four by reduction modulo 81 and 5.
This program enumerates the height-four residue period exactly.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

def require(c,m):
    if not c: raise ValueError(m)

H=4
m,n=3**H,5**H
forbidden=[]
for i in range(H+1):
    for j in range(H+1):
        if i==0 and j==0: continue
        a=1 if j==1 and 1<=i<=4 else 0
        b=i if j==1 and 1<=i<=4 else 0
        forbidden.append((3**i,5**j,a,b))
require(len(forbidden)==24,"incomplete divisor assignment")
def survives(x,y):
    return all(not (x%a==r%a and y%b==s%b) for a,b,r,s in forbidden)
count=0
empty=[]
for x in range(m):
    if x%3==0: continue
    row=sum(survives(x,y) for y in range(n))
    count+=row
    if row==0: empty.append(x)
    if x%81==1: require(row==0,"specified old survivor fibre not empty")
    if x%3==2: require(row==500,"unaffected root row count mismatch")
require(empty==[1],"empty fibre classification mismatch")
# Expected rows: 27 x root2, then root1 split by its 3-adic first disagreement with1.
# Of root1:18 disagree by depth2,6 by depth3,2 by depth4,1 never disagree.
expected=27*500+18*375+6*250+2*125
require(count==expected,"complete survivor count mismatch")
print({"height":H,"old_survivors":54,"empty_old_fibres":empty,"complete_survivors":count,"ambient_size":m*n})
