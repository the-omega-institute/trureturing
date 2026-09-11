"""Finite-dimensional numerical contrast; not a kernel certificate. Seed: 6298."""
import json
import numpy as np

rng = np.random.default_rng(6298)

def density(d):
    z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    a = z @ z.conj().T
    return a / np.trace(a)

def entropy(a):
    x = np.linalg.eigvalsh(a)
    x = x[x > 1e-14]
    return float(-np.dot(x, np.log(x)))

def trial(n, d, orthogonal):
    p = rng.dirichlet(np.ones(n))
    if orthogonal:
        u, _ = np.linalg.qr(rng.normal(size=(d, d)) + 1j*rng.normal(size=(d, d)))
        states = [u[:, 2*i:2*i+2] @ density(2) @ u[:, 2*i:2*i+2].conj().T
                  for i in range(n)]
    else:
        states = [density(d) for _ in range(n)]
    joint = np.zeros((n*d, n*d), dtype=complex)
    for i in range(n):
        joint[i*d:(i+1)*d, i*d:(i+1)*d] = p[i]*states[i]
    tensor = joint.reshape(n, d, n, d)
    system = np.trace(tensor, axis1=1, axis2=3)
    fragment = np.trace(tensor, axis1=0, axis2=2)
    mi = entropy(system) + entropy(fragment) - entropy(joint)
    hp = float(-np.dot(p, np.log(p)))
    return hp-mi

orth = [trial(n,d,True) for n,d in [(2,4),(3,6),(4,8)] for _ in range(80)]
general = [trial(n,d,False) for n,d in [(2,4),(3,6),(4,8)] for _ in range(40)]
print(json.dumps({"seed":6298,"numpy":np.__version__,"orthogonal_cases":len(orth),
                  "max_abs_I_minus_H":max(map(abs,orth)),"general_cases":len(general),
                  "general_strict_I_lt_H":sum(x > 1e-12 for x in general),
                  "general_min_H_minus_I":min(general)},indent=2))
