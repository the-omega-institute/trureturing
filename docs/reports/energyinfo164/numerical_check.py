"""Independent floating-point diagnostic; no numerical result enters the Lean proof."""
import json
import numpy as np

SEED = 1641
rng = np.random.default_rng(SEED)


def hermitian(d):
    z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
    h = (z + z.conj().T) / 2
    return h / np.linalg.norm(h, 2)


def traceless(d):
    h = hermitian(d)
    h -= np.trace(h) / d * np.eye(d)
    return h / np.linalg.norm(h, 2)


def gibbs(h, beta):
    vals, vecs = np.linalg.eigh(h)
    weights = np.exp(-beta * vals)
    weights /= weights.sum()
    return (vecs * weights) @ vecs.conj().T


def entropy(rho):
    vals = np.linalg.eigvalsh(rho)
    assert vals.min() > -1e-12
    vals = vals[vals > 0]
    return float(-np.dot(vals, np.log(vals)))


def log_matrix(rho):
    vals, vecs = np.linalg.eigh(rho)
    assert vals.min() > 0
    return (vecs * np.log(vals)) @ vecs.conj().T


def relative_entropy(rho, sigma):
    return float(np.trace(rho @ (log_matrix(rho) - log_matrix(sigma))).real)


def marginals(rho, da, db):
    t = rho.reshape(da, db, da, db)
    return np.einsum('abcb->ac', t), np.einsum('abad->bd', t)


def mutual_information(rho, da, db):
    a, b = marginals(rho, da, db)
    return entropy(a) + entropy(b) - entropy(rho)


def case(k, correlated):
    da, db = [(2, 2), (2, 3), (3, 2), (3, 3)][k % 4]
    ha, hb = hermitian(da), hermitian(db)
    ba, bb = rng.uniform(-1.5, 1.5, size=2)
    ga, gb = gibbs(ha, ba), gibbs(hb, bb)
    product = np.kron(ga, gb)
    epsilon = 0.0
    rho = product.copy()
    if correlated:
        perturbation = np.kron(traceless(da), traceless(db))
        epsilon = 0.35 * np.linalg.eigvalsh(product).min() / np.linalg.norm(perturbation, 2)
        rho += epsilon * perturbation
    z = rng.normal(size=(da * db, da * db)) + 1j * rng.normal(size=(da * db, da * db))
    u, r = np.linalg.qr(z)
    u = u * (np.diag(r) / np.abs(np.diag(r)))
    final = u @ rho @ u.conj().T
    ia, ib = marginals(rho, da, db)
    fa, fb = marginals(final, da, db)
    de_a = float(np.trace(ha @ (fa - ia)).real)
    de_b = float(np.trace(hb @ (fb - ib)).real)
    d_a, d_b = relative_entropy(fa, ga), relative_entropy(fb, gb)
    ds_a, ds_b = entropy(fa) - entropy(ia), entropy(fb) - entropy(ib)
    i0, i1 = mutual_information(rho, da, db), mutual_information(final, da, db)
    delta_i = i1 - i0
    lhs = ba * de_a + bb * de_b
    residual = lhs - (d_a + d_b + delta_i)
    wrong_sign = lhs - (d_a + d_b - delta_i)
    marginal_error = max(np.max(np.abs(ia - ga)), np.max(np.abs(ib - gb)))
    assert np.linalg.eigvalsh(rho).min() > 0
    assert abs(np.trace(rho) - 1) < 1e-12
    assert marginal_error < 1e-12
    assert abs(residual) < 1e-10
    if correlated:
        assert i0 > 1e-8
        assert abs(wrong_sign) > 1e-8
    return dict(index=k, da=da, db=db, correlated=correlated, epsilon=float(epsilon),
                beta_a=float(ba), beta_b=float(bb), initial_mi=i0, delta_mi=delta_i,
                min_eigenvalue=float(np.linalg.eigvalsh(rho).min()),
                marginal_error=float(marginal_error),
                unitary_error=float(np.linalg.norm(u.conj().T @ u - np.eye(da * db))),
                total_entropy_residual=entropy(final)-entropy(rho),
                side_a_residual=d_a-(ba*de_a-ds_a),
                side_b_residual=d_b-(bb*de_b-ds_b),
                information_residual=ds_a+ds_b-delta_i,
                main_residual=residual, wrong_sign_residual=wrong_sign)


rows = [case(k, k < 41) for k in range(61)]
summary = dict(seed=SEED, numpy=np.__version__, total_cases=len(rows),
               correlated_cases=sum(r['correlated'] for r in rows),
               product_cases=sum(not r['correlated'] for r in rows),
               max_main_residual=max(abs(r['main_residual']) for r in rows),
               max_marginal_error=max(r['marginal_error'] for r in rows),
               min_initial_mi_correlated=min(r['initial_mi'] for r in rows if r['correlated']),
               wrong_sign_failures_correlated=int(sum(abs(r['wrong_sign_residual']) > 1e-8
                   for r in rows if r['correlated'])),
               min_wrong_sign_residual_correlated=min(abs(r['wrong_sign_residual'])
                   for r in rows if r['correlated']))
print(json.dumps(dict(summary=summary, cases=rows), indent=2, allow_nan=False))
