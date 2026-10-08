---
slug: belkin-allen-clark-2025-permuted-brickwork-even-depth
bibkey: belkinallenclark2025secondmoments
doi: null
url: https://arxiv.org/abs/2510.23726v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.result
---

# Even-depth permuted brickwork has a negative moment direction

## Problem

Belkin, Allen and Clark, arXiv:2510.23726v2, Section 5.2, ask:

> Like the brickwork, this architecture can be shown to have a PSD vectorization if the depth is odd. It is unclear if the vectorization is PSD at even depths.

The source defines a complete layer by a uniformly random perfect matching,
with independent Haar-random two-site gates on its pairs. Permuted brickwork
requires every adjacent pair of matchings to have connected union. Its
second-moment vectorization is
$\mathbb E[\overline U\otimes\overline U\otimes U\otimes U]$.
The bars are entrywise conjugation. Matrix vectorization is column-first.

Issue #13744 preregisters the negative answer on four sites: for every integer
$q\ge2$ and every even $d\ge2$, the depth-$d$ vectorization is not positive
semidefinite. The public Lean `claim` states this negative answer and
`result : claim` proves it; `Refuted` refers to even-depth PSD, not to `claim`.
The three matchings are $A=\{01,23\}$, $B=\{02,13\}$ and $C=\{03,12\}$.
Equal matchings have disconnected union and distinct matchings form a
four-cycle, so the connected-block condition is exactly no adjacent repeats.

## Motivation

The frozen result
`D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.result`
answers the source's even-depth question negatively with an unbounded family
in both local dimension and even depth. The four-site restriction suffices
to refute a general even-depth PSD assertion.

## Gap

The preregistration identifies this as a Tier 1 external named question.
The question remains explicit in the source's v2. The preregistered MathDB
searches for the architecture, title, authors and even-depth vectorization
found no answer in that searched scope. Citing-work checks on
arXiv:2503.17759v2 and arXiv:2510.23719v4 are search-seat-reported and found
no settlement. These bounded checks establish neither exhaustive worldwide
novelty nor priority.

## Route

The Haar module derives the two-copy commutant from quarter phases,
permutation invariance and a Hadamard constraint, and integrates the literal
four-factor moment. On the normalized identity/swap vectors its mixed
coefficient is $a=q/(q^2+1)$.

Let $v=|0101\rangle-|0110\rangle-|1001\rangle+|1010\rangle$ in the actual,
nonorthogonal physical permutation vectors, and put
$h=(q^4+1)/(q^2+1)^2=1-2a^2$. The layer projections satisfy
$P_Av=0$ and $(P_A+P_B+P_C)v=hv$. The unnormalized no-repeat word sum obeys
$R_{d+1}=(S-I)R_d$, $R_1=S$, with $S=P_A+P_B+P_C$.
There are $3\cdot2^{d-1}$ admissible words for positive depth. Consequently

$$
\lambda_d=\frac h3(-a^2)^{d-1},\qquad
\langle v,v\rangle=4(1-q^{-2})^2,\qquad
\langle v,\operatorname{vec}(\Phi_d)v\rangle
=\frac h3(-a^2)^{d-1}4(1-q^{-2})^2.
$$

This real quadratic form is strictly negative at every even $d\ge2$.
The Haar-to-layer bridge and the word-length induction identify this with
the literal circuit expectation, rather than an orthonormal coefficient model.

## Falsifier

The settlement concerns the source's independent Haar gates and the uniform
connected-matching word law. A different layer law, an entrywise-conjugation
convention replaced by adjoints, or a coefficient basis declared orthonormal
would describe a different operator. The theorem assumes exactly $q\ge2$,
$d\ge2$ and even $d$, and fixes four sites.

## Evidence

The canonical Lean sources are
`D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl.lean` and
`D5/S3/Quantum/RandomCircuits/PermutedBrickworkEvenRefutation.lean`.
The settling declaration proves the fully quantified `claim`; its live
negative-form witness is `even_physical_quadratic_negative`.
The axiom closure of every public declaration is contained in
`{propext, Classical.choice, Quot.sound}`.
The Scribe settling node carries `OpenProblemResolutionClaim` with
`ResolutionKind.Refuted`.

## Triage

Tier 1, `theorem`, settlement `Refuted` for even-depth PSD under issue #13744.
The Haar module has `admission_basis: escape-witness`, witnessed by
`Commutant.two_copy_commutant` and consumed by `gate_mixed_rule`.
The settling module has `admission_basis: open-problem-resolution` and
`proof_shape: content`. Both have `utility: none`: their new content is a
universal commutant/expectation derivation and induction over arbitrary depth;
finite coefficient identities are consumed normalization steps.
Information-escape registration is paused under CLAUDE.md section 3.9.

### What the settlement shows

- **Proved in this module:** for every $q\ge2$ and every positive $d$, the
  witness eigenvalue is $(h/3)(-a^2)^{d-1}$, with squared physical norm
  $4(1-q^{-2})^2$. `FiniteModel.moment_eigenvector`, `moment_lift`,
  `witness_lift` and `physical_quadratic` provide the live derivation.
  `even_physical_quadratic_negative` establishes the strict sign at all even
  depths. At $q=2,d=2$ the formula evaluates to $-51/625$.
- **Open as a Lean theorem here; source-stated:** odd-depth PSD. Appendix A.8
  conditions on the middle matching and writes the moment as an average of
  $A^\dagger P A$, where $P$ is the middle-layer projection. At even depth
  the middle is an interface between different matchings; the single middle
  projection used by that argument is absent. The proved negative form
  excludes transferring its conclusion to even depth.
- **Computed:** $N=6,q=2,d=2$ has 120 words and minimum eigenvalue
  approximately $-0.00938666666666669$; an integer coefficient vector has exact
  physical quadratic form $-4693321306383/50000$. At $N=6,q=2,d=4$, 7680 words
  give minimum eigenvalue approximately $-0.00016861866666668352$ and exact
  physical quadratic form $-52692713158569/31250000$. The script below checks
  rational Haar-layer matrices and the nonorthogonal Gram matrix; floating
  diagonalization only selects an integer vector, whose negative quadratic
  form is then checked exactly. These are computations, not Lean theorems.
- **Open:** embedding the four-site mechanism into every even $N\ge4$.
  No uniform larger-site statement follows from the two $N=6$ computations.
  $N=8$ is untested by this script and remains open here.
- **Proved consequence of the settlement; source theorem retained:** four-site
  even-depth PB fails the PSD hypothesis of the source's Section 2.2
  optimal-experiment theorem. That conditional theorem is not refuted; its
  application to this ensemble cannot use a PSD premise. No other source
  numerical or scrambling claim is disproved by this settlement.
- **Open as a Lean theorem here; source-stated remedy:** Section 2.2 samples
  $UV^\dagger$ with independent identically distributed $U,V$. Its moment is
  $MM^\dagger$ and is PSD, for $M=\mathbb E[\overline U\otimes\overline U
  \otimes U\otimes U]$. Independence changes the ensemble and does not
  assert PSD of the original even-depth PB ensemble.

### Reproducible computations

Save the following block verbatim as `checks.py` and run `python3 checks.py`
with Python, NumPy and SymPy. The invocation exits 0. The script SHA-256 is
`8d97d8e828b6b9d1e29888567355ddbbe11d530844ebedbb65807edeb682d6ba`. It tests $N=4,q\in\{2,3\},d\in\{1,\ldots,6\}$ and
$N=6,q=2,d\in\{2,4\}$, writes `checks.json`, and prints the exact certificates.
Its explicit scope does not include $N=8$ or arbitrary $N$.

```python
import itertools, json, time, hashlib
from fractions import Fraction as F
from pathlib import Path
import numpy as np
import sympy as sp

root=Path(__file__).resolve().parent
started=time.monotonic()

def matchings(vertices):
    if not vertices:
        return [()]
    x=vertices[0]
    out=[]
    for j in range(1,len(vertices)):
        y=vertices[j]
        for rest in matchings(vertices[1:j]+vertices[j+1:]):
            out.append(((x,y),)+rest)
    return out

def connected(a,b,n):
    found={0}
    for _ in range(n):
        for i,j in a+b:
            if i in found or j in found: found.update([i,j])
    return len(found)==n

def local_weingarten(q):
    # Normalized identity and swap vectors on the D=q^2 dimensional gate.
    # E[bar U_a,b bar U_c,d U_e,f U_g,h] has the four t=2 delta contractions.
    D=q*q
    W=sp.Matrix([[F(D*D,D*D-1),F(-D,D*D-1)],
                 [F(-D,D*D-1),F(D*D,D*D-1)]])
    g=sp.Matrix([[1,F(1,q)],[F(1,q),1]])
    G=sp.kronecker_product(g,g)
    B=sp.zeros(4,2);B[0,0]=1;B[3,1]=1
    T=B*W*B.T*G
    return T,g,W

def gate_product(q,n,matching):
    T,_,_=local_weingarten(q)
    sz=2**n
    rows=[{} for _ in range(sz)]
    bits=list(itertools.product(range(2),repeat=n))
    ix={b:k for k,b in enumerate(bits)}
    for col,b in enumerate(bits):
        terms=[([0]*n,F(1))]
        for i,j in matching:
            term=[]
            for val,c in terms:
                for s in range(2):
                    for t in range(2):
                        w=T[2*s+t,2*b[i]+b[j]]
                        if w:
                            v=val.copy();v[i]=s;v[j]=t
                            term.append((v,c*F(w)))
            terms=term
        for val,c in terms:
            r=ix[tuple(val)];rows[r][col]=rows[r].get(col,F(0))+c
    A=np.zeros((sz,sz),dtype=object); A[:]=F(0)
    for r,row in enumerate(rows):
        for c,v in row.items():A[r,c]=v
    return A,rows

def leftmul(rows,X):
    out=np.zeros_like(X);out[:]=F(0)
    for i,row in enumerate(rows):
        for j,c in row.items():out[i,:]+=c*X[j,:]
    return out

def run(q,n,depths):
    ms=matchings(tuple(range(n)))
    adj=[[j for j,b in enumerate(ms) if connected(a,b,n)] for a in ms]
    assert len({len(a) for a in adj})==1
    degree=len(adj[0]);size=2**n
    mats=[gate_product(q,n,m) for m in ms]
    G=np.array([[F(1,q**sum(x!=y for x,y in zip(b,c)))
          for c in itertools.product(range(2),repeat=n)]
          for b in itertools.product(range(2),repeat=n)],dtype=object)
    # First complete layer annihilates orthogonal complement of the site permutation sector.
    # Therefore the compressed Gram-similar operator has the full nonzero spectrum.
    Gf=G.astype(float);L=np.linalg.cholesky(Gf);W=L.T;Winv=np.linalg.inv(W)
    endpoint=[P.copy() for P,_ in mats]
    records=[]
    for d in range(1,max(depths)+1):
        if d in depths:
            M=sum(endpoint)/F(len(ms)*degree**(d-1))
            H=G@M
            herm=bool(np.array_equal(H,H.T))
            assert herm
            real=W@M.astype(float)@Winv
            assert np.max(np.abs(real-real.T))<1e-12
            vals,V=np.linalg.eigh((real+real.T)/2)
            # Genuine global operator additionally has zero eigenvalues.
            rec={'N':n,'q':q,'d':d,'matchings':len(ms),'transition_degree':degree,
                'words':len(ms)*degree**(d-1),'minimum_sector_eigenvalue':float(vals[0]),
                'minimum_full_eigenvalue':min(0.,float(vals[0])),
                'gram_hermitian_exact':herm,'orthonormalization_residual':float(np.max(np.abs(real-real.T))),
                'eigenvalues_sector':[float(x) for x in vals]}
            if n==4:
                v=np.zeros(size,dtype=object);v[:]=F(0)
                for i,x in [(5,1),(6,-1),(9,-1),(10,1)]:v[i]=F(x)
                a=F(q,q*q+1);h=1-2*a*a
                norm=v@G@v
                assert np.array_equal(mats[0][0]@v,0*v)
                assert np.array_equal(sum(P for P,_ in mats)@v,h*v)
                lam=F(h,3)*(-a*a)**(d-1)
                assert np.array_equal(M@v,lam*v)
                quad=v@G@M@v
                assert quad==lam*norm
                rec.update(witness_eigenvalue=str(lam),witness_norm2=str(norm),witness_quadratic=str(quad))
                assert (lam<0)==(d%2==0)
            if n==4:
                cp=sp.Matrix(M.tolist()).charpoly().as_expr()
                rec["characteristic_polynomial_factors"]=str(sp.factor(cp))
            if n==6 and vals[0]<-1e-12:
                x=np.round(Winv@V[:,0]*100000).astype(int)
                xf=np.array([F(int(t)) for t in x],dtype=object)
                quad=xf@H@xf
                assert quad<0
                rec.update(negative_witness=[int(t) for t in x],negative_quadratic_exact=str(quad))
            if d%2==1 or vals[0]>=-1e-12:
                # Exact LDL pivot certificate for positive semidefiniteness.
                Sm=sp.Matrix(H.tolist())
                pivots=[];B=Sm.copy()
                for i in range(size):
                    p=B[i,i]
                    assert p>=0
                    if p==0:
                        assert all(B[i,j]==0 for j in range(i,size))
                    else:
                        for j in range(i+1,size):
                            for k in range(j,size):
                                B[j,k]-=B[j,i]*B[i,k]/p
                                B[k,j]=B[j,k]
                    pivots.append(str(p))
                rec.update(psd_ldl_pivots=pivots,psd_exact=True,minimum_full_eigenvalue=0.)
            records.append(rec)
            print(json.dumps(rec),flush=True)
        if d<max(depths):
            endpoint=[leftmul(rows,sum(endpoint[j] for j in adj[i]))
                      for i,(_,rows) in enumerate(mats)]
    return records

out=[]
for q in [2,3]:out+=run(q,4,list(range(1,7)))
out+=run(2,6,[2,4])
json.dump({'method':'t=2 Weingarten exact local projector, uniform connected-matching word sum; rational entries and physical Gram; zero complement','results':out,'elapsed_seconds':time.monotonic()-started},open(root/'checks.json','w'),indent=2)
```

## ASSUMED-UNVERIFIED

The bounded literature checks do not exclude independent settlements.
The Lean kernel verifies the encoded statements and does not authenticate
external publication metadata. Odd-depth PSD, the independent $UV^\dagger$
remedy and arbitrary larger even site counts are not additional Lean results
of this delivery. Floating spectra are approximate; the displayed negative
quadratic forms are exact rational computations.
