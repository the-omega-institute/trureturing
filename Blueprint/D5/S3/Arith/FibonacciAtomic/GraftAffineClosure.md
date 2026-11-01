# Fibonacci Graft Words and Complete Composition States

## Abstract

Forward Fibonacci steps and a fixed complete graft realize exactly the observable translation ideal.

Natural numbers include zero. Compositions v,w are pairs of natural numbers. Unless specified otherwise, k,A,B,j are natural numbers, b,X,Y are integers, W is any finite chronological word, and H is a positive natural modulus. A_H is ZMod(H). Residue vectors and their scalar coefficients lie in A_H. The word alphabet has two named operations, R and G; the empty word is allowed. All prefixes are also words, with no length, phase, or expansion restriction. Current readouts include gcd(0,H)=H.

**Definition 1.1 (Fibonacci step).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.step`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R(v)=Mv=(v_2,v_1+v_2). The same formula acts on any additive pair.

**Definition 1.2 (Quantity).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.quantity`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.quantity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q(v)=2v_1+3v_2, over any semiring.

**Definition 1.3 (Consecutive quantity coordinates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.observe`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.observe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C(v)=(q(v),q(Mv))=(2v_1+3v_2,3v_1+5v_2).

**Definition 1.4 (Chronological forward words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.run`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(W,v) executes W from left to right. R sends v to Mv; G sends v to v+w. Both preserve actual nonnegative compositions. False denotes R and true denotes G.

**Definition 1.5 (Current gcd).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.readout`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

o(v)=gcd(q(v),H).

**Definition 1.6 (Common-word equivalence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.behavior`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.behavior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(v,v') means o(T(W,v))=o(T(W,v')) for every identical finite word W. Each possible prefix is included as a word; no intermediate readout is assumed free in a query task.

**Definition 1.7 (Complete residue coordinates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.residue`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.residue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rho(v)=(v_1 mod H,v_2 mod H). res(m) is the scalar residue of m modulo H.

**Definition 1.8 (Observable graft divisor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.graftGcd`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.graftGcd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

d=gcd(gcd(w_1,w_2),H).

**Definition 1.9 (Translation space).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.graftSpace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.graftSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L_w={a rho(w)+b M rho(w): a,b in A_H}.

**Definition 1.10 (Two graft blocks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.realizationWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.realizationWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L=(H^2)!. U(k,A,B) is R^k,G^A,R^(L-1),G^B,R in chronological order. All exponents are nonnegative.

**Definition 1.11 (Translation-only local labels).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.psi`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For prime p and natural h,e, r(X)=depth(p,h,X). If r(X)<e, psi(p,h,e,X) is Low(r(X)); otherwise it is Exact(X mod p^h). These are disjoint sum constructors, in N plus ZMod(p^h). The low label keeps only depth, with no unit coordinate. Multipliers are absent from the local tests.

**Definition 1.12 (Autonomous representation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.Autonomous`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.Autonomous` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(H,w,E,deltaR,deltaG,oS) means E(Mv)=deltaR(E(v)), E(v+w)=deltaG(E(v)), and oS(E(v))=o(v) for every actual v. E maps the entire N^2 into an arbitrary state type S; its image, rather than a single-source reachable set, is counted.

**Definition 1.13 (Actual Fibonacci block).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.atomicBlock`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.atomicBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

a_j=M^j(1,0), for every natural j. Write alpha=(1,0). The Fibonacci sequence has F_0=0 and F_1=1.

**Definition 1.14 (Fibonacci matrix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.matrixM`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.matrixM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M is the integer matrix with rows (0,1) and (1,1).

**Definition 1.15 (Quantity matrix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.matrixC`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.matrixC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C is the integer matrix with rows (2,3) and (3,5).

**Definition 1.16 (Block columns).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.blockMatrix`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.blockMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D_j is the integer matrix with columns a_j and M a_j.

**Definition 1.17 (Residue decoder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.residueReadout`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.residueReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

oBar(u)=gcd(val(q(u)),H), where val is the least nonnegative residue representative.

**Theorem 1.18 (Translation classification, realization, and minimal states).**

$$(\forall p, h, e, ((\operatorname{Prime}\left(p\right)) \land \\{}(e \leq h)) \implies (\forall X, Y, (\forall b, \operatorname{gcd}\left(X + p^{e} \times b, p^{h}\right) = \operatorname{gcd}\left(Y + p^{e} \times b, p^{h}\right)) \Leftrightarrow (\operatorname{psi}\left(p, h, e, X\right) = \operatorname{psi}\left(p, h, e, Y\right)))) \land \\{}(\forall H, (0 < H) \implies (\forall w, (\forall W, \exists k, \exists t, (\operatorname{rho}\left(t\right) \in L_{w}) \land \\{}(\forall v, \operatorname{T}\left(W, v\right) = M^{k} \times v + t)) \land \\{}(\forall u, M^{L} \times u = u) \land \\{}(\forall k, A, B, v, \operatorname{T}\left(\operatorname{U}\left(k, A, B\right), v\right) = M^{k + L} \times v + A \times M^{L} \times w + B \times M^{1} \times w) \land \\{}(\forall k, \forall t, (t \in L_{w}) \implies (\exists W, \forall v, \operatorname{rho}\left(\operatorname{T}\left(W, v\right)\right) = M^{k} \times \operatorname{rho}\left(v\right) + t)) \land \\{}((\operatorname{gcd}\left(\operatorname{gcd}\left(\operatorname{q}\left(w\right), \operatorname{q}\left(M^{1} \times w\right)\right), H\right) = d) \land \\{}(\forall z, (\exists t, (t \in L_{w}) \land \\{}(\operatorname{q}\left(t\right) = z)) \Leftrightarrow (\exists c, z = d \times c))) \land \\{}(\forall v, v', (\operatorname{B}\left(v, v'\right)) \Leftrightarrow (\forall k, b, \operatorname{gcd}\left(\operatorname{q}\left(M^{k} \times v\right) + d \times b, H\right) = \operatorname{gcd}\left(\operatorname{q}\left(M^{k} \times v'\right) + d \times b, H\right))) \land \\{}(\forall v, v', (\operatorname{B}\left(v, v'\right)) \Leftrightarrow (\forall p, ((\operatorname{Prime}\left(p\right)) \land \\{}(p \mid H)) \implies (\forall k, \operatorname{psi}\left(p, \operatorname{valuation}\left(p, H\right), \operatorname{valuation}\left(p, d\right), \operatorname{q}\left(M^{k} \times v\right)\right) = \operatorname{psi}\left(p, \operatorname{valuation}\left(p, H\right), \operatorname{valuation}\left(p, d\right), \operatorname{q}\left(M^{k} \times v'\right)\right)))) \land \\{}((\operatorname{Surjective}\left(rho\right)) \land \\{}(\forall u, \exists v, (v_{1} < H) \land \\{}(v_{2} < H) \land \\{}(\operatorname{rho}\left(v\right) = u)) \land \\{}(\operatorname{Surjective}\left(v \mapsto C \times \operatorname{rho}\left(v\right)\right)) \land \\{}(\forall v, (C \times v = M^{4} \times v) \land \\{}(C \times M^{1} \times v = M^{1} \times C \times v) \land \\{}(C \times (v + w) = C \times v + C \times w)) \land \\{}(\forall k, v, (M^{k} \times C \times v)_{1} = \operatorname{q}\left(M^{k} \times v\right)) \land \\{}(\operatorname{A}\left(H, w, rho, M, v \mapsto v + \operatorname{rho}\left(w\right), oBar\right)) \land \\{}(\operatorname{card}\left(\operatorname{ZMod}\left(H\right)^{2}\right) = H^{2}) \land \\{}(\operatorname{card}\left(\operatorname{image}\left(rho\right)\right) = H^{2}) \land \\{}(\forall u, C \times (5 \times u_{1} - 3 \times u_{2}, -3 \times u_{1} + 2 \times u_{2}) = u)) \land \\{}((M^{4} = C) \land \\{}(\operatorname{det}\left(M\right) = -1) \land \\{}(\operatorname{det}\left(C\right) = 1) \land \\{}(C \times \begin{pmatrix}5&-3\\-3&2\end{pmatrix} = I) \land \\{}(M^{2} = M + I)) \land \\{}(\forall t, (t \in L_{w}) \implies ((M^{1} \times t \in L_{w}) \land \\{}((t_{2} - t_{1}, t_{1}) \in L_{w}))) \land \\{}(\forall k, A, B, \operatorname{length}\left(\operatorname{U}\left(k, A, B\right)\right) = L + k + A + B) \land \\{}(((d = H) \implies (\forall k, b, v, \operatorname{gcd}\left(\operatorname{q}\left(M^{k} \times v\right) + d \times b, H\right) = \operatorname{o}\left(M^{k} \times v\right))) \land \\{}((H = 1) \implies (\forall v, \operatorname{o}\left(v\right) = 1))) \land \\{}(\forall j, (w = \operatorname{a}\left(j\right)) \implies ((\operatorname{q}\left(w\right) = \operatorname{F}\left(j + 3\right)) \land \\{}(\operatorname{q}\left(M^{1} \times w\right) = \operatorname{F}\left(j + 4\right)) \land \\{}(\operatorname{gcd}\left(w_{1}, w_{2}\right) = 1) \land \\{}(d = 1) \land \\{}((j = 0) \implies (w = (1, 0))) \land \\{}((0 < j) \implies (w = (\operatorname{F}\left(j - 1\right), \operatorname{F}\left(j\right)))) \land \\{}(\operatorname{D}\left(j\right) = M^{j}) \land \\{}(\operatorname{Coprime}\left(\operatorname{q}\left(w\right), \operatorname{q}\left(M^{1} \times w\right)\right)) \land \\{}(\operatorname{det}\left(\operatorname{D}\left(j\right)\right) = (-1)^{j}) \land \\{}(\forall v, v', (\operatorname{B}\left(v, v'\right)) \Leftrightarrow (\operatorname{rho}\left(v\right) = \operatorname{rho}\left(v'\right))) \land \\{}(\forall v, v', (\operatorname{rho}\left(v\right) \neq \operatorname{rho}\left(v'\right)) \implies (\exists k, A, B, (k \leq 1) \land \\{}(A < H) \land \\{}(B < H) \land \\{}((w = (1, 0)) \implies ((\operatorname{res}\left(A\right) = \operatorname{res}\left(\operatorname{q}\left(M^{k} \times v\right)\right)) \land \\{}(\operatorname{res}\left(B\right) = -\operatorname{res}\left(\operatorname{q}\left(M^{k} \times v\right)\right)))) \land \\{}(\operatorname{length}\left(\operatorname{U}\left(k, A, B\right)\right) \leq L + 2 \times (H - 1) + 1) \land \\{}(\operatorname{o}\left(\operatorname{T}\left(\operatorname{U}\left(k, A, B\right), v\right)\right) = H) \land \\{}(\operatorname{o}\left(\operatorname{T}\left(\operatorname{U}\left(k, A, B\right), v'\right)\right) < H))) \land \\{}(\forall S, E, deltaR, deltaG, oS, (\operatorname{A}\left(H, w, E, deltaR, deltaG, oS\right)) \implies (H^{2} \leq \operatorname{card}\left(\operatorname{image}\left(E\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first group quantifies all natural p,h,e with p prime and e<=h, including h=0. The remaining group quantifies every H>0 and every actual graft w; the affine assertions also hold at H=1. In its local-axis clause, h_p=v_p(H) and e_p=v_p(d), for each prime p dividing H. The local depth is saturated at h; for nonzero integers v_p is the usual valuation. In the actual affine form, t is in N^2; elsewhere t,u,z are residue vectors or scalars. Cardinalities use finite cardinals when finite, and the image lower bound applies also to infinite state types. All conjunctions below are under those scopes.

Low depth stays unchanged under p^e translations. Different low depths, or a low and a high label, are separated by the zero translation. For two distinct high residues, an integer multiple of p^e cancels the first; its gcd is p^h and the second gcd is smaller. This includes e=0 and e=h. These tests have no arbitrary scalar multiplication, so the low unit information required by multiplier tasks does not occur here.

The invertible Fibonacci step permutes H^2 residue pairs, so its L-th power is the identity. The exact word U has terminal composition M^(k+L)v+A M^Lw+B Mw. Least nonnegative representatives of the two coefficients realize every translation in L_w, on the same actual source and with no inverse operation. The unimodular quantity matrix gives gcd(qw,qMw,H)=d. Bezout coefficients for these two quantities and H realize each scalar translation db. Thus the full common-word tests equal the integer translation tests at every k.

At a prime axis, the cofactor d/p^e is invertible modulo the remaining power. Hence each p^e translation is induced by some global db and by a forward word. A difference at one prime already separates the whole gcd. Equality of all prime-axis labels conversely assembles equality of the full gcd. No simultaneous cancellation at other primes is needed. When d=H all observable translations vanish; when H=1 every current output is one.

For w=a_j the two quantities are consecutive Fibonacci numbers. Their coprimality supplies Bezout coefficients even when neither quantity alone is a unit modulo H. The block is retained as its complete composition, never as its index or as a scalar addend. Different residue pairs have different quantity readings at time zero or one. A common U cancels the first reading, giving outputs H and a proper divisor of H. For alpha its coefficients are A=-c and B=c modulo H, where c=-q(M^kv). Both coefficients have representatives below H.

Every residue pair has actual nonnegative representatives, and C is invertible modulo H, so every observation pair also occurs. Recording the complete composition residue gives an autonomous representation with exactly H^2 states. If any representation identifies different residues, its deterministic updates give equal outputs after their common separating word, a contradiction. The minimum image size is therefore H^2, including the one-state case H=1.

## Fixed rooted rational words on each positive-beta pair orbit

Specialize the chronological pair run to the graft vector alpha=(1,0) and V={(a,b) in N squared: b>0}. Thus the two pair actions are Rpair(a,b)=(b,a+b) and Gpair(a,b)=(a+1,b). Both preserve V, including a=0. For each independently fixed v in V, let O(v) contain every endpoint of every finite chronological pair word from v, including the empty word. These are entire attained pair-action orbits, with no word-length bound.

On positive rational numbers use the separate rooted actions Lroot(x)=x/(1+x) and Rroot(x)=x+1. E(s,x) executes the finite rooted word s chronologically, so E(st,x)=E(t,E(s,x)). A representation is any map iota from O(v) into the positive rationals and two rooted words u,w satisfying iota(Gpair(z))=E(u,iota(z)) and iota(Rpair(z))=E(w,iota(z)) for every z in O(v). The words may be chosen separately for each initial v, but remain fixed across its orbit, states and histories. No injectivity, effectiveness, acquisition or anchor certificate is assumed. Empty words are allowed.

Such a representation exists exactly when u and w are empty and iota is constant on the entire orbit. Every positive rational constant supplies a representation with both words empty. On the separate whole domain V, the same two fixed-word equations hold exactly for constant maps with both words empty. In the formulas, K(v0,iota,u,w) denotes the two orbit equations, Kglobal(iota,u,w) the two whole-domain equations, and nil the empty rooted word. The constant c is a positive rational. All maps have the positive-rational codomain stated above; z ranges over the indicated domain.

$$
(\operatorname{K}\left(v0, iota, u, w\right)) \Leftrightarrow ((u = \operatorname{nil}\left(\right)) \land (w = \operatorname{nil}\left(\right)) \land (\forall z, (z \in \operatorname{O}\left(v0\right)) \implies (\operatorname{iota}\left(z\right) = \operatorname{iota}\left(v0\right))))
$$

$$
(\operatorname{Kglobal}\left(iota, u, w\right)) \Leftrightarrow ((u = \operatorname{nil}\left(\right)) \land (w = \operatorname{nil}\left(\right)) \land (\exists c, \forall z, (z \in V) \implies (\operatorname{iota}\left(z\right) = c)))
$$

The exact rational input is the reconstruction theorem original_views_reconstruct in RationalRouting.Views. It identifies ratio(encode(s)) with E(s,1), sends this ratio back to the same literal word s, and reconstructs every positive rational x from originalWord(x). If d=originalWord(x), then E(d,1)=x. Equality E(s,x)=E(t,x) therefore gives E(ds,1)=E(dt,1), hence ds=dt by the word round trip, and s=t by prefix cancellation. The existing private ratio_fold and pair_ratio_step in Views identify this evaluator with the rational list fold on positive pairs; encode_good and rational_reconstruction supply its initial pair, while Source.attain_control supplies positivity at concatenation cuts. This derives freeness at every positive rational anchor from the supplied reconstruction laws; it is no extra premise and does not follow merely from matrix generation.

Replace each chronological Gpair letter by u and each Rpair letter by w, preserving concatenation. The list-fold homomorphism law transports the two equations to every finite word W: iota(Run(W,z))=E(Phi(W),iota(z)) for every orbit state z. The literal chronological evaluator, rather than a reversed matrix product, is used. In GraftAffineClosure, false denotes Rpair and true denotes Gpair; in RationalRouting, false denotes Lroot and true denotes Rroot. The correspondence follows the actions and the substitution Phi, without identifying these Boolean names.

At every initial pair (a,b), Gpair Rpair Rpair and Rpair Gpair Rpair Gpair both end at (a+b+1,a+2b+1). Transport and rational-anchor freeness give uww=wuwu. Taking word lengths forces u empty. Now Rpair cubed and Rpair Gpair to the power (a+b) Rpair Gpair to the power b both end at (a+2b,2a+3b). Iterated translation by alpha gives these exact endpoints and keeps every prefix in V. The exponents depend on the initial pair only as witnesses of a legal native pair equality; they do not change the fixed compiled words. With u empty, the second equality gives www=ww and forces w empty. Transport along an arbitrary reaching word now makes iota equal to its value at the initial state. The empty-word evaluation law proves the converse for every positive rational constant.

For a map on all of V, restriction to the orbit of (0,1) first forces both compiled words empty. Gpair invariance and its finite iterates give iota(a,b)=iota(0,b). For each b>0, Rpair(b-1,1)=(1,b); applying the same invariance before and after this replacement yields iota(0,b)=iota(0,1). Thus the whole-domain map is constant, and the empty-word law again supplies every constant converse.

This is a composition-level application of the exact rational reconstruction and generic fold and iteration laws. It gives no native root-graft permission: the Gpair composition effect can be realized by the LAB leftmost-beta split under its authentic binding, current rights, tapes, completed replies and sufficient finite material. Whole-frontier replacement uses its acquired entry leaf list and does not edit newly born leaves again. That actual source implementation and its physical or resource obligations remain separate from this pair-action inference. Full native trees or histories, state-dependent compiled words, inverse or signed actions and other codomains are outside this classification. No decoder acquisition, finite observation certificate, retention bound, noise margin or physical realization follows from it.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.Autonomous`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.atomicBlock`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.behavior`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.blockMatrix`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.graftGcd`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.graftSpace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.matrixC`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.matrixM`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.observe`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.psi`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.quantity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.readout`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.realizationWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.residue`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.residueReadout`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.run`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.step`
- Dependency: [D5/S3/Arith/Congruence/PrimePowerAffineBehavior](../Congruence/PrimePowerAffineBehavior.md)
