"""Numerical probe only; independent analytic controls, not a Lean proof."""
import json
import math
import sys
import numpy as np

TOL = 1e-10
rng = np.random.default_rng(172021)


def pinch(rho, basis):
    read = basis.conj().T @ rho @ basis
    return basis @ np.diag(np.diag(read)) @ basis.conj().T


def log_matrix(rho):
    eig, vec = np.linalg.eigh(rho)
    assert eig.min() > -TOL
    # The repository's finite trace-log convention uses log(0)=0.
    logs = np.zeros_like(eig)
    mask = eig > 1e-14
    logs[mask] = np.log(eig[mask])
    return (vec * logs) @ vec.conj().T


def entropy(rho):
    return float(-np.trace(rho @ log_matrix(rho)).real)


def divergence(rho, sigma):
    return float(np.trace(rho @ (log_matrix(rho) - log_matrix(sigma))).real)


def fourier(d):
    i, j = np.indices((d, d))
    return np.exp(2j * np.pi * i * j / d) / np.sqrt(d)


def close(actual, expected):
    return float(np.max(np.abs(np.asarray(actual) - np.asarray(expected)))) < TOL


# Expected values are analytic constants, independent of entropy/divergence code.
identity = []
for p, known_s in [(1.0, 0.0), (0.75, 2 * math.log(2) - 0.75 * math.log(3)),
                   (0.5, math.log(2))]:
    rho = np.diag([p, 1-p]).astype(complex)
    omega = np.eye(2) / 2
    sigma = pinch(rho, fourier(2))
    actual = [entropy(rho), entropy(sigma), divergence(rho, sigma),
              divergence(rho, omega), entropy(sigma) - entropy(rho)]
    expected = [known_s, math.log(2), math.log(2)-known_s,
                math.log(2)-known_s, math.log(2)-known_s]
    assert close(sigma, omega)
    assert all(close(a, e) for a, e in zip(actual, expected))
    identity.append(dict(p=p, actual=actual, expected=expected,
                         matrix_max_error=float(np.max(abs(sigma-omega))), passed=True))

max_residual = 0.0
count = 0
phase_count = 0
for d in [1, 2, 3, 4, 5, 8]:
    u = fourier(d)
    omega = np.eye(d) / d
    for p in [np.eye(d)[0], np.ones(d)/d] + [rng.dirichlet(np.ones(d)) for _ in range(100)]:
        # Rotate both bases: checks basis covariance, not only standard diagonal matrices.
        z, _ = np.linalg.qr(rng.normal(size=(d,d)) + 1j*rng.normal(size=(d,d)))
        x = z @ u
        rho = z @ np.diag(p) @ z.conj().T
        sigma = pinch(rho, x)
        assert close(pinch(rho,z), rho)
        assert close(abs(z.conj().T @ x)**2, np.ones((d,d))/d)
        s, tax, freedom = entropy(rho), divergence(rho,sigma), divergence(rho,omega)
        tested_freedom = -freedom if '--wrong-sign' in sys.argv else freedom
        residual = max(float(np.max(abs(sigma-omega))), abs(tax-tested_freedom),
                       abs(tax-(math.log(d)-s)), abs(entropy(sigma)-s-tax),
                       abs(s+freedom-math.log(d)))
        assert residual < TOL
        assert s >= -TOL and freedom >= -TOL
        assert close(pinch(rho,x),rho) == close(rho,omega)
        max_residual = max(max_residual,residual)
        count += 1
    # Generic states, independently sampled from the Z-fixed probe family.
    for _ in range(100):
        a = rng.normal(size=(d,d)) + 1j*rng.normal(size=(d,d))
        rho = a @ a.conj().T
        rho /= np.trace(rho)
        s, freedom = entropy(rho), divergence(rho,omega)
        assert s >= -TOL and freedom >= -TOL and close(s+freedom,math.log(d))
        phase_count += 1

rho = np.diag([1.,0.]).astype(complex)
omega = np.eye(2)/2
sigma = pinch(rho,fourier(2))
mutated_sign_error = abs(divergence(rho,sigma) + divergence(rho,omega))
mutated_basis_error = abs(divergence(rho,pinch(rho,np.eye(2))) - divergence(rho,omega))
assert mutated_sign_error > TOL, 'INSTRUMENT FAILURE: missed reversed sign'
assert mutated_basis_error > TOL, 'INSTRUMENT FAILURE: missed nonconjugate bases'
print(json.dumps(dict(seed=172021, numpy=np.__version__, tolerance=TOL,
    identities=identity, original_cases=count, original_failures=0,
    generic_phase_cases=phase_count, max_residual=max_residual,
    discrimination=dict(sign_reversal=dict(rejected=True,residual=mutated_sign_error),
        nonconjugate_basis=dict(rejected=True,residual=mutated_basis_error))), indent=2))
