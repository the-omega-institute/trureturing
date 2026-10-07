---
slug: basu-kashyap-2019-unique-indecomposable-basis
bibkey: basu2019latticesubspacecodes
doi: null
url: https://arxiv.org/abs/1911.00721v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.result
---

# A Unique Indecomposable Basis Without Intersection Closure

## Problem

Pranab Basu and Navin Kashyap, *The Lattice Structure of Linear Subspace Codes*,
arXiv:1911.00721v1, Section 6, Conjecture 6.1 (page 23; TeX label `UIB`):

> A linear code $\mathcal U$ in $\mathbb P_q(n)$ has a unique indecomposable basis
> if and only if $\mathcal U$ is closed under intersection.

A linear subspace code contains the zero subspace and carries an abelian,
exponent-two group operation $\boxplus$ whose identity is zero and whose
translations preserve $d_S(X,Y)=\dim X+\dim Y-2\dim(X\cap Y)$.
A nonzero codeword is indecomposable when no two codewords of strictly smaller
ambient dimension have it as their $\boxplus$-sum. A basis is an unordered finite
set of codewords giving exactly one finite-subset-sum representation of each
codeword, with respect to the same operation. Thus the basis belongs to the
code's $\mathbb F_2$-space, rather than to the ambient $\mathbb F_q$-space.

## Motivation

`D5/S3/Combinatorics/SubspaceCodes/BasuKashyapUniqueIndecomposableBasisRefutation.result` proves the negation of the universal conjecture.
Its consumed private `family` theorem gives a counterexample over every finite
field, for every $0<i<a$ and $i<b$, in ambient dimension $i+a+b$.
The code has a unique indecomposable basis and is not closed under intersection.

## Gap

Tier 1; preregistration [#13819](https://github.com/the-omega-institute/trureturing/issues/13819)
records the verbatim source, quantified statement, conventions and literature
screen. The source has only arXiv v1. The recorded MathDB entry
[344378](https://mathdb.com/p/344378/unique-indecomposable-basis-conjecture-for-linear-subspace-c)
has no solution; the recorded arXiv and Crossref searches identify no settlement
or journal version. These are bounded literature readings, not a global
priority claim. The source's intersection-closed implication is a proved result
in Remark 5 and Proposition 17, not the missing converse.

## Route

Split $\mathbb F_q^{i+a+b}=I\oplus P\oplus Q$ into coordinate blocks of
dimensions $i,a,b$. Put $A=I\oplus P$, $B=I\oplus Q$, $C=P\oplus Q$ and
$\mathcal U=\{0,A,B,C\}$, with Klein addition $A\boxplus B=C$.
The private coordinate constructors compose upstream projection kernels,
infima, coordinate equivalences and submodule maps. Klein addition transports
upstream addition on $\mathbb Z/2\mathbb Z\times\mathbb Z/2\mathbb Z$.

1. The family proves $A\cap B=I$, $A\cap C=P$, $B\cap C=Q$ and the
   dimensions $i+a,i+b,a+b$.
2. The literal integer distance equals the weight of the Klein difference;
   translation preserves it, and the other three code axioms hold.
3. Exactly $A,B$ are indecomposable: $C=A\boxplus B$ has two smaller summands;
   a decomposition of $A$ or $B$ cannot have both summands strictly smaller.
4. The subset sums of $\{A,B\}$ are $0,A,B,C$. Every indecomposable basis is
   this unordered set.
5. $A\cap B=I\notin\mathcal U$. The settling theorem specializes the family
   to $F=\mathbb Z/2\mathbb Z$, $(i,a,b)=(1,2,2)$ and $n=5$.

## Falsifier

The counterexample would fail if the four literal code axioms, the finite-subset
basis condition, or the strict ambient-dimension decomposition condition failed.
The family checks them jointly for the same subspace set and operation.
Both readings of "indecomposable basis"—a basis chosen from indecomposables,
or the entire indecomposable set forming a basis—give $\{A,B\}$ here.
Ordered bases and ambient-field bases do not express the source's definition.

## Evidence

Source locator: `Library/FiniteGeometry/basu2019latticesubspacecodes.md`.

The public `result : ¬ claim` and its consumed private family are kernel-checked.
The axiom closure is contained in `{propext, Classical.choice, Quot.sound}`.
The following exhaustive computation and independent validation are evidence
outside the Lean kernel; they do not constitute a formal proof of minimality.

## Triage

### What the settlement shows

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Three coordinate-block intersections escape the Klein code; the dimension gaps leave exactly two indecomposable words forming its unique basis. | proved | Kernel-checked private `family`, `realizeFin_inter`, `klein_indecomposable`, `klein_unique_basis` and `family_intersection_missing`, consumed by `result`; the block nonmembership argument below handles $P,Q$. Every finite field, $0<i<a$, $i<b$. |
| Intersection-closed codes have a unique indecomposable basis. | proved | Literature reading: Proposition 17 (label `11`) and Remark 5 (label `R`), page 21; Section 6, page 22. This implication is not formalized here. |
| Over $\mathbb F_2$, $n\le5$, codes of size $\le4$, the smallest counterexample dimension is $5$ and every counterexample has Klein addition. | computed | Exhaustive programs below, commands, exits 0 and SHA-256 values; all distinct ambient subspace sets, not isomorphism classes. |
| Remark 5 includes "closed under intersection"; the Section 6 recap omits that qualifier. | proved | Literature reading: exact quotations below; this is a textual conclusion, not a Lean theorem. |
| A weaker intersection or lattice property characterizing unique indecomposable bases. | open | No characterization established by this module or the finite computation. |
| Codes of size $\ge8$, and $q>2$ outside the proved coordinate family. | open | No exhaustive computation or classification in these domains. |
| Restoring the converse by requiring indecomposable codewords to intersect trivially. | open | Candidate strengthening; no general theorem asserted. |
| The equal-block case $a=b=i>0$ in this coordinate construction. | proved | Paper argument: the three nonzero words have equal dimension, so all are indecomposable; every pair is a basis and there are three distinct indecomposable bases. Not a Lean theorem in this module. |
| The source's intersection-closed lattice results and the separate Braun–Etzion–Vardy cardinality question. | proved | Literature reading: the lattice results retain their explicit intersection-closed hypothesis; this refutation supplies no conclusion on the separate cardinality conjecture. |

The three blocks are positive. The kernel family establishes that $I$ is
outside the code. For $P$, the codeword $A$ additionally contains $I$, $B$
contains $I,Q$, and $C$ contains $Q$, so none equals $P$; also $P\ne0$.
The same argument interchanging $P,Q$ proves $Q\notin\mathcal U$.
These are paper consequences of the coordinate realization, not additional
Lean declarations. The failure mechanism is that an additive basis of the
code need not encode disjointness or intersection closure of its ambient
subspaces.

Remark 5 (label `R`, page 21) says:

> The set of indecomposable codewords in a linear subspace code closed under
> intersection is linearly independent with respect to the linear addition
> over $\mathbb F_2$. This together with Proposition 17 imply that the
> indecomposable codewords are a basis for the vector space over $\mathbb F_2$
> formed by the linear code.

Section 6 (page 22) says:

> We observed earlier that the indecomposable codewords in a linear subspace
> code constitute a basis for the vector space over $\mathbb F_2$ formed by the
> code (Remark 5).

The qualified remark and the proved lattice results remain valid under their
stated hypotheses. Conjecture 6.1's converse is refuted. Section 6 also poses
the separate Braun–Etzion–Vardy cardinality question; it is not settled here.

### Exhaustive binary computation

The scope is exactly $q=2$, $n=0,1,2,3,4,5$, code size at most four, with no
sampling. Generate every subspace by adjoining vectors and closing under XOR,
then examine every unordered triple of distinct nonzero subspaces. For a
four-word exponent-two group the operation is uniquely Klein. The three
pair-distance/complement-dimension identities are equivalent to all translation
isometries. Sizes one and two are intersection-closed; size three cannot carry
an exponent-two group. The independent validator enumerates subspaces by RREF,
and checks all 64 translation equalities, all decompositions and all 16 basis
candidates for every reported counterexample.

| $n$ | Subspaces | Nonzero triples examined | Size-four linear codes | Counterexamples |
| --- | ---: | ---: | ---: | ---: |
| 0 | 1 | 0 | 0 | 0 |
| 1 | 2 | 0 | 0 | 0 |
| 2 | 5 | 4 | 3 | 0 |
| 3 | 16 | 455 | 84 | 0 |
| 4 | 67 | 45,760 | 4,180 | 0 |
| 5 | 374 | 8,579,746 | 455,576 | 217,000 |

All $217,000$ counterexamples have word dimensions $(3,3,4)$ and pairwise
intersection dimensions $(1,2,2)$. Of these, $138,880$ have triple intersection
dimension zero and the coordinate-family shape; $78,120$ have triple
intersection dimension one and a different shape. "Klein" describes the
code operation, not the coordinate-family classification. One noncoordinate
example is $A=\langle e_1,e_2,e_3\rangle$,
$B=\langle e_1,e_4,e_5\rangle$,
$C=\langle e_1,e_2,e_4,e_3+e_5\rangle$.
No minimality or exhaustiveness claim extends beyond this tested range.

The exact program sources are below. Save their two Python blocks as
`/tmp/op-bk/enumerate.py` and `/tmp/op-bk/check_enumeration.py`, respectively;
create `/tmp/op-bk` first. Commands measured by the implementation seat:

```sh
python3 /private/tmp/op-bk/enumerate.py
python3 /private/tmp/op-bk/check_enumeration.py
```

Both exit codes are 0. On this host `/tmp` resolves to `/private/tmp`.

### Enumerator source

SHA-256: `47173728a5819a81b998cffa35253cf057e73f1c4c94ae9aaed5d28b3301ca6c`.

```python
import json,itertools,time,pathlib
out=pathlib.Path('/tmp/op-bk'); totals=[]
for n in range(6):
    start=time.monotonic(); zero=1
    spaces={zero}; level={zero}
    for d in range(n):
        nxt=set()
        for S in level:
            el=[x for x in range(1<<n) if (S>>x)&1]
            for v in range(1,1<<n):
                if not (S>>v)&1:
                    T=S
                    for x in el: T|=1<<(x^v)
                    nxt.add(T)
        spaces.update(nxt); level=nxt
    subs=sorted(spaces); nz=[s for s in subs if s!=zero]
    dim={s:s.bit_count().bit_length()-1 for s in subs}
    assert len(subs)==[1,2,5,16,67,374][n]
    # Symmetric distance matrix and exact common-intersection dimensions.
    D=[[dim[s]+dim[t]-2*((s&t).bit_count().bit_length()-1) for t in nz] for s in nz]
    codes=bad=coordinate=noncoordinate=0; dist={}; examples={}
    with (out/f'counterexamples-n{n}.jsonl').open('w') as fh:
        for j in range(len(nz)):
            X=nz[j]; x=dim[X]
            for k in range(j+1,len(nz)):
                Y=nz[k]; y=dim[Y]; zreq=D[j][k]
                for l in range(k+1,len(nz)):
                    Z=nz[l]; z=dim[Z]
                    if z!=zreq or D[j][l]!=y or D[k][l]!=x: continue
                    codes+=1
                    # A nonzero word is decomposable precisely when both other
                    # nonzero words have strictly smaller ambient dimensions.
                    inc=[p for p,v in enumerate((x,y,z)) if not all(w<v for r,w in enumerate((x,y,z)) if r!=p)]
                    unique=(len(inc)==2)
                    closed=all(T in (zero,X,Y,Z) for T in (X&Y,X&Z,Y&Z))
                    if not unique or closed: continue
                    bad+=1
                    words=[X,Y,Z]; A,B=[words[p] for p in inc]; C=next(w for w in words if w not in (A,B))
                    i=(A&B).bit_count().bit_length()-1
                    a=(A&C).bit_count().bit_length()-1
                    b=(B&C).bit_count().bit_length()-1
                    t=(A&B&C).bit_count().bit_length()-1
                    # Coordinate shape iff the three intersections are direct
                    # and sum to the pairwise union (triple intersection zero).
                    shape=(t==0 and i>0 and i<a and i<b and dim[A]==i+a and dim[B]==i+b and dim[C]==a+b)
                    coordinate+=shape; noncoordinate+=not shape
                    key=f'{sorted((x,y,z))};triple={t}'
                    dist[key]=dist.get(key,0)+1
                    row={'q':2,'n':n,'subspaces_bitmasks':[1,A,B,C],'dims':[0,dim[A],dim[B],dim[C]],'intersection_dims':[i,a,b],'triple_intersection_dim':t,'coordinate_family_shape':shape,'operation':'Klein; nonzero pair sums to remaining word','indecomposable_indices':[1,2]}
                    fh.write(json.dumps(row,separators=(',',':'))+'\n')
                    examples.setdefault(str(t),row)
    r={'n':n,'subspace_count':len(subs),'nonzero_triples_examined':len(nz)*(len(nz)-1)*(len(nz)-2)//6,'linear_codes_by_size':{'1':1,'2':len(nz),'3':0,'4':codes},'counterexamples':bad,'coordinate_family_shape':coordinate,'other_shape':noncoordinate,'distribution':dist,'examples':examples,'seconds':time.monotonic()-start,'sampling':False}
    totals.append(r); print(json.dumps(r),flush=True)
(out/'enumeration-summary.json').write_text(json.dumps(totals,indent=2))
```

### Independent validator source

SHA-256: `c706b0ec6d6872fce66b9d2d5f52634a65bb127410300e8e827d6615f099994c`.

```python
import itertools,json,pathlib,time
out=pathlib.Path('/tmp/op-bk'); summary=json.loads((out/'enumeration-summary.json').read_text());checks=[]
def rref_spaces(n):
    for d in range(n+1):
        for pivots in itertools.combinations(range(n),d):
            free=[(r,j) for r,p in enumerate(pivots) for j in range(p+1,n) if j not in pivots]
            for bits in range(1<<len(free)):
                rows=[1<<p for p in pivots]
                for k,(r,j) in enumerate(free):
                    if (bits>>k)&1:rows[r]|=1<<j
                vecs=[0]
                for r in rows:vecs+= [v^r for v in vecs]
                yield sum(1<<v for v in vecs)
def dim(S):return S.bit_count().bit_length()-1
def dist(S,T):return dim(S)+dim(T)-2*dim(S&T)
for n in range(6):
    start=time.monotonic(); spaces=list(rref_spaces(n));assert len(spaces)==len(set(spaces))==summary[n]['subspace_count']
    lookup=set(spaces);badcount=0;shapes={0:0,1:0}
    for line in (out/f'counterexamples-n{n}.jsonl').open():
        row=json.loads(line);U=row['subspaces_bitmasks'];assert all(s in lookup for s in U)
        # Enumerate and check all 64 translation equalities and all 16 possible bases.
        assert all(dist(U[x^y],U[x^z])==dist(U[y],U[z]) for x,y,z in itertools.product(range(4),repeat=3))
        inc=[x for x in range(1,4) if not any(dim(U[y])<dim(U[x]) and dim(U[z])<dim(U[x]) for y in range(4) for z in range(4) if y^z==x)]
        bases=[]
        for S in range(16):
            if any((S>>x)&1 and x not in inc for x in range(4)):continue
            words=[x for x in range(4) if (S>>x)&1];images=[]
            for T in range(1<<len(words)):
                value=0
                for j,x in enumerate(words):
                    if (T>>j)&1:value^=x
                images.append(value)
            if sorted(images)==[0,1,2,3]:bases.append(words)
        assert bases==[[1,2]]
        assert any(s&t not in U for s,t in itertools.product(U,repeat=2))
        triple=dim(U[1]&U[2]&U[3]);assert triple==row['triple_intersection_dim']
        shapes[triple]+=1;badcount+=1
    assert badcount==summary[n]['counterexamples']
    result={'n':n,'independent_RREF_subspaces':len(spaces),'counterexamples_independently_checked':badcount,'all_64_translation_equalities_per_counterexample':True,'all_16_candidate_bases_per_counterexample':True,'triple_intersection_counts':shapes,'seconds':time.monotonic()-start}
    checks.append(result);print(json.dumps(result),flush=True)
(out/'enumeration-independent-check.json').write_text(json.dumps(checks,indent=2))
```

## ASSUMED-UNVERIFIED

The literature status is limited to the source and searches recorded in #13819;
no worldwide novelty or priority guarantee is claimed. The exhaustive-search
results and minimality are computational, not Lean theorems. Larger ambient
spaces, larger codes and fields other than $\mathbb F_2$ outside the family
have no classification in this delivery. Information-escape registration is
paused under CLAUDE.md §3.9.
