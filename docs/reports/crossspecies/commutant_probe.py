import json
import numpy as np
seed = 20260911
rng = np.random.default_rng(seed)
def unitary(n):
    z = rng.normal(size=(n,n)) + 1j*rng.normal(size=(n,n))
    q, r = np.linalg.qr(z)
    return q @ np.diag(np.diag(r)/np.abs(np.diag(r)))
def nullity(gs):
    n = len(gs[0]); eye = np.eye(n)
    k = np.vstack([np.kron(g.T, eye) - np.kron(eye, g) for g in gs])
    sv = np.linalg.svd(k, compute_uv=False)
    tol = 1e-10 * sv[0]
    d = int(np.count_nonzero(sv <= tol))
    return dict(nullity=d, tolerance=float(tol), smallest_nonzero=float(sv[-d-1]),
                largest_null=float(sv[-d]),
                unitarity_error=max(float(np.linalg.norm(g.conj().T@g-eye)) for g in gs))
rows=[]
for case in range(30):
    n=2+case%7
    generic=[unitary(n) for _ in range(2)]
    blocks=[]
    for _ in range(2):
        b=np.zeros((n,n),complex); cut=n//2
        b[:cut,:cut]=unitary(cut)
        b[cut:,cut:]=unitary(n-cut)
        blocks.append(b)
    rows.append(dict(case=case,n=n,generic=nullity(generic),reducible=nullity(blocks)))
result=dict(seed=seed,numpy=np.__version__,field="complex",cases=rows,
    generic_nullity_one=sum(x["generic"]["nullity"]==1 for x in rows),
    reducible_nullity_gt_one=sum(x["reducible"]["nullity"]>1 for x in rows),
    caveat="Floating-point diagnostic only; no kernel certificate of irreducibility.")
print(json.dumps(result,indent=2))
