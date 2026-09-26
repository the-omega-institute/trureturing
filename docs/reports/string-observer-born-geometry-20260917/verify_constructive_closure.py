#!/usr/bin/env python3
"""Finite tests of the explicitly constructed maps; not Lean/kernel verification."""
from __future__ import annotations
import json, platform
from pathlib import Path
import numpy as np
import scipy
from scipy.linalg import expm
from scipy.integrate import solve_ivp

RNG=np.random.default_rng(20260923)
checks={}
def ck(name,a,b=0,tol=2e-9):
    err=float(np.linalg.norm(np.asarray(a)-np.asarray(b)))
    if not np.isfinite(err) or err>tol: raise AssertionError((name,err,tol))
    e=checks.setdefault(name,dict(count=0,max_error=0.,tolerance=tol));e['count']+=1;e['max_error']=max(e['max_error'],err)
def rnd(n,m):return RNG.normal(size=(n,m))+1j*RNG.normal(size=(n,m))
def iso(n,d):return np.linalg.qr(rnd(n,d))[0][:,:d]
def state(d):
    X=rnd(d,d);A=X@X.conj().T;return A/np.trace(A)
def herm(d):
    A=rnd(d,d);return (A+A.conj().T)/2

def spectral(Q):
    q,v=np.linalg.eigh((Q+Q.conj().T)/2);tol=2e-11*max(1.,float(np.max(q)))
    if np.min(q)<-tol:raise ValueError('nonpositive Q')
    keep=q>tol;P=v[:,keep]@v[:,keep].conj().T
    W=(v[:,keep]/np.sqrt(q[keep]))@v[:,keep].conj().T
    return P,W

def apply(Es,A):return sum(E@A@E.conj().T for E in Es)
def recovery(Es):
    n,d=Es[0].shape;Q=sum(E@E.conj().T for E in Es);P,W=spectral(Q)
    e0=np.eye(d,dtype=complex)[:,0]
    Rs=[E.conj().T@W for E in Es]
    Rs.extend(np.outer(e0,np.eye(n,dtype=complex)[b])@(np.eye(n)-P) for b in range(n))
    return Q,P,W,Rs

def matrix_units(Es,W):
    d=Es[0].shape[1];basis=np.eye(d,dtype=complex)
    return [[W@apply(Es,np.outer(basis[i],basis[j]))@W for j in range(d)] for i in range(d)]
def algebra(F,A):return sum(A[i,j]*F[i][j] for i in range(len(F)) for j in range(len(F)))
def decoder_units(F,P):
    d=len(F);n=P.shape[0];zero=np.eye(d,dtype=complex)[:,0]
    Ts=[np.vstack([F[0][i][b,:] for i in range(d)]) for b in range(n)]
    return Ts+[np.outer(zero,np.eye(n,dtype=complex)[b])@(np.eye(n)-P) for b in range(n)]
def choi(Es):
    return sum(np.outer(E.reshape(-1,order='F'),E.reshape(-1,order='F').conj()) for E in Es)
def sqrt_kraus(Es):
    n,d=Es[0].shape;q,v=np.linalg.eigh(choi(Es));root=(v*np.sqrt(np.maximum(q,0)))@v.conj().T
    return [root[:,mu].reshape((n,d),order='F') for mu in range(n*d)]
def entropy(A):
    w=np.linalg.eigvalsh((A+A.conj().T)/2);w=w[w>1e-12];return float(-np.sum(w*np.log(w)))
def rel(A,B):
    def logm(X):
        w,v=np.linalg.eigh((X+X.conj().T)/2);lv=np.zeros_like(w);m=w>1e-11;lv[m]=np.log(w[m]);return (v*lv)@v.conj().T
    return float(np.trace(A@(logm(A)-logm(B))).real)

def reversible_cases():
    for case in range(36):
        d=1+case%3;k=1+(case//3)%3;n=d*k+1+case%2
        S=iso(n,d*k);lam=RNG.uniform(.3,1.,size=k);lam/=lam.sum()
        Es=[np.sqrt(lam[j])*S[:,j*d:(j+1)*d] for j in range(k)]
        # Add an exactly zero Kraus and mix all Kraus coordinates.
        Es.append(np.zeros((n,d),complex));mix=iso(k+1,k+1)
        Es=[sum(mix[a,j]*Es[a] for a in range(k+1)) for j in range(k+1)]
        Q,P,W,Rs=recovery(Es);F=matrix_units(Es,W);Ts=decoder_units(F,P)
        ck('input_TP',sum(E.conj().T@E for E in Es),np.eye(d))
        ck('recovery_TP',sum(R.conj().T@R for R in Rs),np.eye(n))
        ck('support_pseudoinverse',W@Q@W,P)
        C=np.array([[np.trace(E.conj().T@B)/d for B in Es] for E in Es])
        ck('Gram_trace',np.trace(C),1)
        for a in range(len(Es)):
            for b in range(len(Es)):
                ck('KL_residual',Es[a].conj().T@Es[b],C[a,b]*np.eye(d))
        ck('logical_identity',sum(F[i][i] for i in range(d)),P)
        for i in range(d):
            for j in range(d):
                ck('logical_star',F[i][j].conj().T,F[j][i])
                for a in range(d):
                    for b in range(d):ck('matrix_unit_law',F[i][j]@F[a][b],F[i][b] if j==a else np.zeros((n,n)))
        for A in (state(d),rnd(d,d)):
            ck('exact_recovery_all_matrices',apply(Rs,apply(Es,A)),A)
            ck('matrixunit_decoder',apply(Ts,apply(Es,A)),A)
            ck('channel_factorization',apply(Es,A),Q@algebra(F,A))
        X=rnd(n,n);ck('decoder_two_formulas',apply(Rs,X),apply(Ts,X))
        K=sqrt_kraus(Es);ck('global_sqrt_Choi_kraus',choi(K),choi(Es),2e-8)
        rho=state(d*2);Eref=[np.kron(E,np.eye(2)) for E in Es];Rref=[np.kron(R,np.eye(2)) for R in Rs]
        ck('entangled_reference_recovery',apply(Rref,apply(Eref,rho)),rho)
        a,b=state(d),state(d)
        ck('entropy_added_syndrome',entropy(apply(Es,a))-entropy(a),-np.sum(lam*np.log(lam)),2e-8)
        ck('relative_entropy_preserved',rel(apply(Es,a),apply(Es,b)),rel(a,b),2e-8)
        # The eigenspace F_11 gives a constructible factor, independent of Kraus diagonalization.
        ev,vec=np.linalg.eigh(F[0][0]);f=vec[:,ev>.5]
        theta=np.column_stack([F[i][0]@f[:,q] for q in range(k) for i in range(d)])
        ck('Theta_isometry',theta.conj().T@theta,np.eye(k*d));ck('Theta_image',theta@theta.conj().T,P)
        sigma=f.conj().T@Q@f;ck('syndrome_trace',np.trace(sigma),1)
        ck('Theta_Q_factorization',theta.conj().T@Q@theta,np.kron(sigma,np.eye(d)))
        for scale in (0.,.31):
            scaled=[np.sqrt(scale)*E for E in Es];_,_,_,Rscaled=recovery(scaled)
            ck('zero_subchannel_TP',sum(R.conj().T@R for R in Rscaled),np.eye(n))
            ck('subchannel_recovery',apply(Rscaled,apply(scaled,a)),scale*a)

def nonreversible():
    g=.37
    Es=[np.diag([1.,np.sqrt(1-g)]).astype(complex),np.array([[0,np.sqrt(g)],[0,0]],complex)]
    _,_,_,Rs=recovery(Es);ck('noncorrectable_recovery_still_TP',sum(R.conj().T@R for R in Rs),np.eye(2))
    I=choi([np.eye(2)]);err=np.linalg.norm(choi([R@E for R in Rs for E in Es])-I)
    if err<.01:raise AssertionError('negative control invisible')
    return dict(amplitude_damping_Choi_error=float(err))

def generator_cases():
    for case in range(20):
        d=1+case%3;k=1+case%2;n=d*k+2
        S=iso(n,d*k);w=RNG.uniform(.2,1.,k);w/=w.sum()
        Es=[np.sqrt(w[j])*S[:,j*d:(j+1)*d] for j in range(k)]
        _,P0,_,_=recovery(Es);F0=matrix_units(Es,recovery(Es)[2])
        H=herm(n);t=.12
        G=expm(-1j*t*H);A=-1j*H
        F=[[G@f@G.conj().T for f in row] for row in F0]
        P=G@P0@G.conj().T;dP=A@P-P@A
        dF=[[A@f-f@A for f in row] for row in F]
        Z=sum(dF[i][j]@F[j][i] for i in range(d) for j in range(d))/d
        K=Z-P@dP
        ck('Z_anti_part',Z+Z.conj().T,dP)
        ck('K_antihermitian',K+K.conj().T,0)
        ck('K_transports_projection',K@P-P@K,dP)
        for i in range(d):
            for j in range(d):ck('K_transports_matrixunits',K@F[i][j]-F[i][j]@K,dF[i][j])
        if d==1:ck('Kato_limit',K,dP@P-P@dP)
        # Noncommutative arbitrary logical Kraus transfer.
        raw=[rnd(d,d) for _ in range(3)];Gm=sum(R.conj().T@R for R in raw);ev,v=np.linalg.eigh(Gm);ir=(v/np.sqrt(ev))@v.conj().T
        Ls=[L@ir for L in raw];phys=[algebra(F,L) for L in Ls]+[np.eye(n)-P]
        ck('lifted_instrument_TP',sum(R.conj().T@R for R in phys),np.eye(n))
        Et=[G@E for E in Es];_,_,_,Rs=recovery(Et);rho=state(d)
        for L,M in zip(Ls,phys):ck('lifted_branch',apply(Rs,M@apply(Et,rho)@M.conj().T),L@rho@L.conj().T)

def time_evolution():
    d,k,n=2,2,5
    S=iso(n,d*k);Es=[np.sqrt(w)*S[:,i*d:(i+1)*d] for i,w in enumerate([.3,.7])]
    Q,P0,W,Rs=recovery(Es);F0=matrix_units(Es,W)
    H1,H2=herm(n),herm(n);hL=np.array([[.2,.13+.07j],[.13-.07j,-.2]])
    gap=1.2;hb=.9
    def data(t):
        G=expm(-1j*t*H1)@expm(-1j*t*t*H2/2)
        A=-1j*H1+expm(-1j*t*H1)@(-1j*t*H2)@expm(1j*t*H1)
        F=[[G@f@G.conj().T for f in row] for row in F0]
        P=G@P0@G.conj().T;dp=A@P-P@A
        df=[[A@f-f@A for f in row] for row in F]
        Z=sum(df[i][j]@F[j][i] for i in range(d) for j in range(d))/d;K=Z-P@dp
        Hp=1j*hb*K+algebra(F,hL)+gap*(np.eye(n)-P)
        return F,P,K,Hp
    def rhs(t,y):
        X=y[:n*n].reshape(n,n);U=y[n*n:].reshape(n,n);_,_,K,H=data(t)
        return np.concatenate([(K@X).ravel(),(-1j/hb*H@U).ravel()])
    y0=np.concatenate([np.eye(n,dtype=complex).ravel()]*2)
    sol=solve_ivp(rhs,(0,.7),y0,rtol=3e-10,atol=3e-12)
    if not sol.success:raise AssertionError(sol.message)
    X,U=sol.y[:n*n,-1].reshape(n,n),sol.y[n*n:,-1].reshape(n,n)
    F,P,K,Hp=data(.7);VL=expm(-1j*.7*hL/hb)
    pred=X@(algebra(F0,VL)+np.exp(-1j*gap*.7/hb)*(np.eye(n)-P0))
    ck('physical_unitary_ODE',U.conj().T@U,np.eye(n),2e-8)
    ck('explicit_evolution_solution',U,pred,2e-8)
    rho=state(d*2);enc=apply([np.kron(E,np.eye(2)) for E in Es],rho)
    out=np.kron(U,np.eye(2))@enc@np.kron(U.conj().T,np.eye(2))
    D=decoder_units(F,P);dec=apply([np.kron(R,np.eye(2)) for R in D],out)
    target=np.kron(VL,np.eye(2))@rho@np.kron(VL.conj().T,np.eye(2))
    ck('full_geometric_logical_recovery',dec,target,2e-8)

def topology_phase_checks():
    paulis=[np.array([[0,1],[1,0]],complex),np.array([[0,-1j],[1j,0]]),np.diag([1.,-1.]).astype(complex)]
    for j in range(24):
        x=RNG.normal(size=3);x/=np.linalg.norm(x);p=(np.eye(2)+sum(x[i]*paulis[i] for i in range(3)))/2
        bad=np.zeros((3,3),complex);bad[:2,:2]=p;bad[2,2]=1
        good=np.kron(p,np.eye(2));ck('bad_rank_two',np.trace(bad),2);ck('good_rank_two',np.trace(good),2)
        ck('bad_gap',np.linalg.eigvalsh(2*bad-np.eye(3)),[-1,1,1]);ck('good_gap',np.linalg.eigvalsh(2*good-np.eye(4)),[-1,-1,1,1])
        Es=[np.kron(p[:,a:a+1],np.eye(2)) for a in range(2)];Q,P,W,Rs=recovery(Es)
        rho=state(2);ck('sphere_global_decoder',apply(Rs,apply(Es,rho)),rho)
    plus=np.array([1,1])/np.sqrt(2);minus=np.array([1,-1])/np.sqrt(2)
    ck('controlled_phase_distinguishes',abs(np.vdot(plus,minus)),0)
    ck('ordinary_global_phase_invisible',choi([np.eye(2)]),choi([-np.eye(2)]))

if __name__=='__main__':
    reversible_cases();witness=nonreversible();generator_cases();time_evolution();topology_phase_checks()
    result=dict(status='passed',seed=20260923,count=sum(v['count'] for v in checks.values()),families=len(checks),checks=checks,witnesses=witness,versions=dict(python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__),scope='Finite numerical error probes; no directed interval certification or Lean compilation.')
    out=Path(__file__).with_name('constructive_closure_checks.json');out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','count','families','witnesses']},indent=2))
