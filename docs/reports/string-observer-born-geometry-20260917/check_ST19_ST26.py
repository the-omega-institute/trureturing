#!/usr/bin/env python3
"""Finite checks for ST19-ST26. These tests are not substitutes for the proofs.
Run: python check_ST19_ST26.py --out checks_ST19_ST26.json
Requires NumPy, SciPy, SymPy. Deterministic seed; no network or repository writes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import platform
from pathlib import Path
import numpy as np
import scipy
from scipy.linalg import expm
from scipy.integrate import quad
import sympy as sp

SEED = 2026091703
rng = np.random.default_rng(SEED)
checks: dict[str, dict] = {}
witnesses: dict[str, object] = {}


def check(name: str, residual: float, tol: float = 3e-10) -> None:
    val = float(residual)
    if not np.isfinite(val) or val > tol:
        raise AssertionError(f'{name}: {val} > {tol}')
    item = checks.setdefault(name, {'count': 0, 'max_residual': 0.0, 'tolerance': tol})
    item['count'] += 1
    item['max_residual'] = max(item['max_residual'], val)


def eq(name: str, a, b, tol: float = 3e-10) -> None:
    check(name, np.linalg.norm(np.asarray(a) - np.asarray(b)), tol)


def le(name: str, lhs: float, rhs: float, tol: float = 3e-10) -> None:
    check(name, max(0.0, float(lhs-rhs)), tol)


def zmat(m: int, n: int) -> np.ndarray:
    return rng.normal(size=(m, n)) + 1j*rng.normal(size=(m, n))


def iso(n: int, d: int) -> np.ndarray:
    return np.linalg.qr(zmat(n, d))[0][:, :d]


def herm(n: int) -> np.ndarray:
    a = zmat(n, n)
    return (a+a.conj().T)/2


def state(d: int) -> np.ndarray:
    a = zmat(d, d)
    r = a@a.conj().T
    return r/np.trace(r)


def invsqrt(a: np.ndarray) -> np.ndarray:
    s, v = np.linalg.eigh(a)
    if np.min(s) <= 0:
        raise ValueError('Expected positive definite matrix')
    return (v*(s**-0.5))@v.conj().T


def trdist(a, b) -> float:
    x = a-b
    return float(np.sum(np.abs(np.linalg.eigvalsh((x+x.conj().T)/2)))/2)


def bfun(q: float) -> float:
    q = float(np.clip(q, 0, 1))
    return (q+math.sqrt(q*(4-3*q)))/2


def partial_ref(r: np.ndarray, system_dim: int, ref_dim: int) -> np.ndarray:
    return np.einsum('aiaj->ij', r.reshape(system_dim, ref_dim, system_dim, ref_dim))


def reset_kraus(effect: np.ndarray, tau: np.ndarray) -> list[np.ndarray]:
    lam, v = np.linalg.eigh((effect+effect.conj().T)/2)
    t, w = np.linalg.eigh((tau+tau.conj().T)/2)
    return [np.sqrt(max(0, si)*max(0, tj))*np.outer(w[:, j], v[:, i].conj())
            for i, si in enumerate(lam) for j, tj in enumerate(t)]


def apply(ks: list[np.ndarray], rho: np.ndarray, ref: int = 1) -> np.ndarray:
    out = np.zeros((ks[0].shape[0]*ref,)*2, complex)
    for k in ks:
        kk = np.kron(k, np.eye(ref))
        out += kk@rho@kk.conj().T
    return out


def compress(ks, u, w, taus):
    p = w@w.conj().T
    d = u.shape[1]
    effects, comp, leaks = [], [], []
    for group, tau in zip(ks, taus):
        ksmall = [w.conj().T@k@u for k in group]
        leak = sum((k@u).conj().T@(np.eye(p.shape[0])-p)@(k@u) for k in group)
        leak = (leak+leak.conj().T)/2
        effects.append(leak)
        comp.append(ksmall+reset_kraus(leak, tau))
        leaks.append(ksmall)
    lam = max(0, float(np.linalg.eigvalsh(sum(effects))[-1]))
    return comp, effects, lam, leaks


def choi(ks: list[np.ndarray]) -> np.ndarray:
    vs = [k.reshape(-1, order='F') for k in ks]
    return sum(np.outer(v, v.conj()) for v in vs)


def random_instrument_tests():
    for case in range(48):
        nin = 3+case % 3
        nout = 3+(case//3) % 3
        d = 1+case % min(3, nin)
        e = 1+(case//2) % min(3, nout)
        u, w = iso(nin, d), iso(nout, e)
        raw = [zmat(nout, nin) for _ in range(4)]
        normal = invsqrt(sum(k.conj().T@k for k in raw))
        raw = [k@normal for k in raw]
        ks = [raw[:2], raw[2:]]
        taus = [state(e), state(e)]
        comp, ls, lam, small = compress(ks, u, w, taus)
        ref = 2
        rho = state(d*ref)
        eq('full_TP', sum(k.conj().T@k for k in raw), np.eye(nin))
        eq('completion_TP', sum(k.conj().T@k for group in comp for k in group), np.eye(d))
        le('leakage_PSD', -np.linalg.eigvalsh(sum(ls))[0], 0)
        le('leakage_at_most_one', lam, 1)
        le('completion_Choi_PSD', -np.linalg.eigvalsh(choi([k for g in comp for k in g]))[0], 0)
        q = float(np.trace(np.kron(sum(ls), np.eye(ref))@rho).real)
        dist = 0.0
        for a in range(2):
            actual = apply([k@u for k in ks[a]], rho, ref)
            sim = apply([w@k for k in comp[a]], rho, ref)
            eq('outcome_effect', sum(k.conj().T@k for k in comp[a]),
               u.conj().T@sum(k.conj().T@k for k in ks[a])@u)
            eq('outcome_reference_marginal', partial_ref(actual, nout, ref), partial_ref(sim, nout, ref))
            dist += trdist(actual, sim)
        le('state_specific_sharp_bound', dist, bfun(q))
        le('uniform_complete_bound', dist, bfun(lam))
        gin, gout = iso(d, d), iso(e, e)
        comp2, ls2, lam2, _ = compress(ks, u@gin, w@gout,
              [gout.conj().T@tau@gout for tau in taus])
        eq('frame_invariance_lambda', lam, lam2)
        for a in range(2):
            eq('frame_leak_conjugation', ls2[a], gin.conj().T@ls[a]@gin)
            rho0 = state(d)
            eq('frame_completion_covariance', apply(comp2[a], rho0),
               gout.conj().T@apply(comp[a], gin@rho0@gin.conj().T)@gout)


def sharp_examples():
    u = np.eye(3, dtype=complex)[:, :2]
    tau = np.diag([0., 1.]).astype(complex)
    rho = np.diag([1., 0.]).astype(complex)
    for q in [0., 1e-8, .001, .01, .1, .3, .5, 2/3, .9, .99, 1.]:
        k = np.array([[np.sqrt(1-q), 0, -np.sqrt(q)],
                      [0, 1, 0], [np.sqrt(q), 0, np.sqrt(1-q)]], complex)
        comp, ls, lam, _ = compress([[k]], u, u, [tau])
        actual = apply([k@u], rho)
        sim = apply([u@kk for kk in comp[0]], rho)
        eq('sharp_b_achieved', trdist(actual, sim), bfun(q), 2e-9)
        eq('sharp_lambda', lam, q)
    for n in [4, 16, 64, 256, 1024]:
        theta = np.pi/(2*n)
        r = np.array([[np.cos(theta),-np.sin(theta)],[np.sin(theta),np.cos(theta)]])
        psi = np.linalg.matrix_power(r, n)@np.array([1., 0.])
        eq('coherent_accumulation_probability', abs(psi[1])**2, 1, 2e-10)
        lam = float(np.sin(theta)**2)
        le('coherent_accumulation_valid_budget', 1., min(1., n*bfun(lam)))
        witnesses[f'coherent_N{n}']={'per_step_leakage':lam,'incorrect_sum_probability':n*lam,
                                    'final_record_error':float(abs(psi[1])**2),
                                    'uncapped_valid_budget':n*bfun(lam)}


def adaptive_tests():
    # Small coherent leakage with two outcomes. The real state is never reprojected.
    u = np.eye(3, dtype=complex)[:, :2]
    for case in range(12):
        bell = np.array([1.,0.,0.,1.], complex)/np.sqrt(2)
        rho = np.outer(bell, bell.conj())
        encoded = np.kron(u,np.eye(2))@rho@np.kron(u,np.eye(2)).conj().T
        real, small = {():encoded}, {():rho}
        budget = 0.
        for j in range(3):
            nreal, nsmall = {}, {}
            worst = 0.
            for hist in real:
                theta = .012*(1+j)+.001*case+.004*sum(hist)
                rot = np.array([[np.cos(theta),0,-np.sin(theta)], [0,1,0],
                                [np.sin(theta),0,np.cos(theta)]], complex)
                probs = np.array([.3,.65,.45]) + .02*sum(hist)
                ks = [[rot@np.diag(np.sqrt(probs))],
                      [rot.conj().T@np.diag(np.sqrt(1-probs))]]
                comp, _, lam, _ = compress(ks,u,u,[np.eye(2)/2,np.eye(2)/2])
                worst = max(worst,bfun(lam))
                for a in range(2):
                    nreal[hist+(a,)] = apply(ks[a],real[hist],2)
                    nsmall[hist+(a,)] = apply(comp[a],small[hist],2)
            real, small = nreal, nsmall
            budget += worst
        full_dist=0.; record_dist=0.
        for hist in real:
            sim = np.kron(u,np.eye(2))@small[hist]@np.kron(u,np.eye(2)).conj().T
            full_dist += trdist(real[hist],sim)
            record_dist += abs(np.trace(real[hist])-np.trace(sim))/2
        le('adaptive_full_record_state_budget', full_dist, budget)
        le('adaptive_classical_record_budget', float(record_dist), budget)
        eq('adaptive_total_probability_real', sum(np.trace(x) for x in real.values()),1)
        eq('adaptive_total_probability_model', sum(np.trace(x) for x in small.values()),1)
        witnesses[f'adaptive_case{case}']={'cq_distance':full_dist,'classical_TV':float(record_dist),'budget':budget}


def commutator_tests():
    for case in range(40):
        n,d = 3+case%3, 1+case%2
        u = iso(n,d); p=u@u.conj().T
        a,b=herm(n),herm(n)
        aa,bb=u.conj().T@a@u,u.conj().T@b@u
        la,lb=(np.eye(n)-p)@a@u,(np.eye(n)-p)@b@u
        defect=aa@bb-bb@aa-u.conj().T@(a@b-b@a)@u
        eq('compressed_commutator_identity',defect,-la.conj().T@lb+lb.conj().T@la)
        le('compressed_commutator_bound', np.linalg.norm(defect,2),2*np.linalg.norm(la,2)*np.linalg.norm(lb,2))
        t=2e-5
        kk=expm(-1j*t*a)@u
        # Stable form avoids subtracting nearly equal probabilities.
        out=(np.eye(n)-p)@kk
        eq('short_time_leakage_coefficient',out.conj().T@out/t**2,la.conj().T@la,0.002)
    u=np.column_stack((np.array([1.,1.,0.])/np.sqrt(2),np.array([1.,-1.,2.])/np.sqrt(6)))
    a=np.diag([1.,0.,0.]);b=np.diag([0.,1.,0.])
    aa=u.T@a@u;bb=u.T@b@u
    target=np.array([[0.,-1.],[1.,0.]])/(3*np.sqrt(3))
    eq('commuting_full_noncommuting_compression',aa@bb-bb@aa,target)
    witnesses['compressed_commutator_norm']=float(np.linalg.norm(target,2))


sig=np.array([[[0,1],[1,0]],[[0,-1j],[1j,0]],[[1,0],[0,-1]]],complex)

def sm(v):return np.einsum('a,aij->ij',v,sig)


def sphere_tests():
    kappas=[-1.,-.5,0.,.3,1.]
    for case in range(48):
        theta=rng.uniform(.05,np.pi-.05);phi=rng.uniform(0,2*np.pi)
        n=np.array([np.sin(theta)*np.cos(phi),np.sin(theta)*np.sin(phi),np.cos(theta)])
        nt=np.array([np.cos(theta)*np.cos(phi),np.cos(theta)*np.sin(phi),-np.sin(theta)])
        nf=np.array([-np.sin(theta)*np.sin(phi),np.sin(theta)*np.cos(phi),0])
        u=np.array([np.cos(theta/2),np.exp(1j*phi)*np.sin(theta/2)])[:,None]
        ut=np.array([-.5*np.sin(theta/2),.5*np.exp(1j*phi)*np.cos(theta/2)])[:,None]
        uf=np.array([0,1j*np.exp(1j*phi)*np.sin(theta/2)])[:,None]
        p=u@u.conj().T;pp=np.eye(2)-p
        eq('spin_eigenvector',sm(n)@u,u)
        eq('spin_constant_gap',np.linalg.eigvalsh(sm(n)),[-1,1])
        g=np.exp(-1j*phi)
        us=u*g
        usf=g*(uf-1j*u)
        an=(1j*u.conj().T@uf).item()
        ass=(1j*us.conj().T@usf).item()
        eq('north_south_connection',ass,an+1)
        z=np.cos(theta/2)**2;x=np.exp(1j*phi)*np.tan(theta/2)
        eq('graph_overlap_identity',z,1/(1+abs(x)**2))
        for k in kappas:
            gt=k*sm(np.cross(n,nt));gf=k*sm(np.cross(n,nf))
            n0t=pp@ut;n0f=pp@uf
            nxt=pp@(ut-1j*gt@u);nxf=pp@(uf-1j*gf@u)
            eq('ambient_shape_scaling_theta',nxt,(1+2*k)*n0t)
            eq('ambient_shape_scaling_phi',nxf,(1+2*k)*n0f)
            ffull=2*k*(1+k)*np.sin(theta)*sm(n)
            fproj=(u.conj().T@ffull@u+1j*(nxt.conj().T@nxf-nxf.conj().T@nxt)).item()
            eq('ambient_curvature_decomposition',fproj,-.5*np.sin(theta))
            dens=np.linalg.norm(nxt)**2+np.linalg.norm(nxf)**2/np.sin(theta)**2
            eq('normal_energy_density',dens,.5*(1+2*k)**2)
            dpt=(1+2*k)*sm(nt)/2;dpf=(1+2*k)*sm(nf)/2
            cd_t=1j*(dpt@p-p@dpt);cd_f=1j*(dpf@p-p@dpf)
            control=np.linalg.norm(cd_t,'fro')**2+np.linalg.norm(cd_f,'fro')**2/np.sin(theta)**2
            eq('counterdiabatic_density',control,2*dens)
            le('pointwise_ambient_corrected_bound',abs(fproj-(u.conj().T@ffull@u).item())/np.sin(theta),dens)
    chern=quad(lambda th:-.5*np.sin(th),0,np.pi,epsabs=1e-12)[0]
    eq('sphere_Chern_integral',chern,-1)
    for k in kappas:
        en=2*np.pi*quad(lambda th:.5*(1+2*k)**2*np.sin(th),0,np.pi)[0]
        ambient=2*np.pi*quad(lambda th:2*k*(1+k)*np.sin(th),0,np.pi)[0]
        eq('global_corrected_bound_saturation',en,abs(-2*np.pi-ambient))
        witnesses[f'ambient_kappa_{k}']={'normal_energy':en,'ambient_flux':ambient,'chern':-1}
    # Any chosen rank-one fixed chart meets a zero-overlap point at the antipode.
    for _ in range(24):
        fixed=iso(2,1);p0=fixed@fixed.conj().T;p= np.eye(2)-p0
        eq('antipodal_chart_loss',np.linalg.norm((np.eye(2)-p0)@p,2),1)


def symbolic_tests():
    q=sp.symbols('q',positive=True)
    b=(q+sp.sqrt(q*(4-3*q)))/2
    assert sp.simplify(sp.diff(b,q,2)+2/(q*(4-3*q))**sp.Rational(3,2))==0
    m=sp.Matrix([[0,sp.sqrt(q*(1-q))],[sp.sqrt(q*(1-q)),q]])
    assert sp.simplify(m.det()+q*(1-q))==0
    assert sp.simplify(2*sp.trace(m*m)-sp.trace(m)**2-q*(4-3*q))==0
    k=sp.symbols('k',real=True)
    assert sp.expand(-2*sp.pi-8*sp.pi*k*(1+k)+2*sp.pi*(1+2*k)**2)==0
    checks['exact_symbolic_identities']={'count':4,'max_residual':0,'tolerance':0}


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,default=Path('checks_ST19_ST26.json'))
    args=p.parse_args()
    random_instrument_tests();sharp_examples();adaptive_tests();commutator_tests();sphere_tests();symbolic_tests()
    result={'status':'passed','seed':SEED,'assertion_count':sum(x['count'] for x in checks.values()),
            'families':len(checks),'checks':checks,'witnesses':witnesses,
            'scope':'Finite numerical and exact symbolic error probes. No Lean compilation or proof of universal assertions by testing.',
            'versions':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,'sympy':sp.__version__},
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':result['status'],'assertions':result['assertion_count'],'families':result['families'],
                     'output':str(args.out)},indent=2))

if __name__=='__main__':main()
