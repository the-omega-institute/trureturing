"""Floating-point diagnostic only; independent of Lean proof, seed and tolerance fixed."""
import json
import numpy as np
rng = np.random.default_rng(12320911)
tol = 1e-10
counts = dict(cauchy_schwarz=0, full_width=0, half_width=0)
worst = {k: -float('inf') for k in counts}
for k in range(600):
    n = 2 + k % 7
    z = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    # Include singular states every fifth sample.
    if k % 5 == 0:
        z[:, 1:] = 0
    rho = z @ z.conj().T
    rho /= np.trace(rho)
    c, delta = rng.uniform(-3, 3), rng.uniform(0.01, 3)
    matrices = []
    for _ in range(2):
        q, _ = np.linalg.qr(rng.normal(size=(n,n)) + 1j*rng.normal(size=(n,n)))
        lam = rng.uniform(c-delta, c+delta, size=n)
        matrices.append((q * lam) @ q.conj().T)
    a, b = matrices
    expect = lambda x: float(np.trace(rho @ x).real)
    va, vb = expect(a @ a)-expect(a)**2, expect(b @ b)-expect(b)**2
    cov = expect((a@b+b@a)/2)-expect(a)*expect(b)
    residuals = dict(cauchy_schwarz=abs(cov)-np.sqrt(max(0,va*vb)),
                     full_width=max(va,vb)-(2*delta)**2,
                     half_width=max(va,vb)-delta**2)
    for name, residual in residuals.items():
        counts[name] += int(residual > tol)
        worst[name] = max(worst[name], residual)
print(json.dumps(dict(seed=12320911, samples=600, dimensions=[2,8],
                     singular_samples=120, tolerance=tol,
                     violations=counts, max_signed_residual=worst), indent=2))
