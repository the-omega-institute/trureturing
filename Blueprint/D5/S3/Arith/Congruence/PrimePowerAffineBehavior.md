# Prime-Power Affine Behavior

## Abstract

A tagged low quotient or high quotient class records exactly the prime-power depth responses to all positive multiplications and forward translations.

**Definition 1.1 (Saturated prime depth).**

Lean statement: `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.depth`

*Formalization.* `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.depth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural p,h and integer x, depth(p,h,x) is log base p of gcd(x,p^h). At prime p the theorem identifies it with min(v_p(x),h) for x!=0, and assigns depth h to every zero residue modulo p^h.

**Definition 1.2 (Disjoint quotient coordinates).**

Lean statement: `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.eta`

*Formalization.* `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.eta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Put N=p^h, D=p^e and M=p^(h-e). Write r(x)=depth(p,h,x). The coordinate E(x)=eta(p,h,e,x) is S(r(x),[x/p^r(x)]_M) when r(x)<e, and D([x/p^e]_M) otherwise. The S and D labels are disjoint constructors. The ambient carrier is (natural numbers x ZMod M) disjoint-union ZMod M; the low residue is proved to be a unit, rather than imposed as a restriction on integer source values. Integer division is exact in the relevant branch.

**Definition 1.3 (Finite forward continuations).**

Lean statement: `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.run`

*Formalization.* `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word is any finite list whose entries are either a positive natural multiplier or a unit marker meaning add p^e. T(w,x)=run(p,e,w,x) applies entries in list order. The empty word returns x. There is no fixed bound on word length.

**Theorem 1.4 (Exact local classification and its bridges).**

$$p \text{prime}, h,e \in \mathbb{N}, e \leq h \Rightarrow\\{}(\forall x, r(x) \leq h \land gcd(x, N) = p^{r(x)} \land (r(x) = h \iff N \mid x) \land (x \neq 0 \Rightarrow r(x) = min(v(p, x), h)) \land (r(x) < e \Rightarrow IsUnit([x/p^{r(x)}]_{M}))) \land\\{}(\forall x,y, (x \equiv y (\operatorname{mod} N) \Rightarrow r(x) = r(y) \land E(x) = E(y))) \land\\{}(\forall x, (\exists X, X > 0 \land x \equiv X (\operatorname{mod} N))) \land\\{}(\forall a,b, (\exists A,B, A > 0 \land B \geq 0 \land (\forall x, ax+Db \equiv Ax+DB (\operatorname{mod} N)))) \land\\{}(\forall w, (\exists A,B \in \mathbb{N}, A > 0 \land (\forall x, T(w, x) = Ax+DB))) \land\\{}(\forall A,B \in \mathbb{N}, (A > 0 \Rightarrow (\exists w, (\forall x, T(w, x) = Ax+DB)))) \land\\{}(\forall x,y, (E(x) = E(y) \iff (\forall a,b, (a > 0 \land b \geq 0 \Rightarrow r(ax+Db) = r(ay+Db)))) \land (E(x) = E(y) \iff (\forall w, r(T(w, x)) = r(T(w, y))))) \land\\{}(e = h \Rightarrow (\forall u,v \in U_{M}, u = v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.local_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses natural p,h,e with p prime and e<=h. It includes h=0; the positive-depth case takes h>=1. N,D,M,r,E,T have the meanings above. Unless a natural domain is displayed, x,y,X,a,b,A,B are integers. Words w range over all finite continuations. U_M denotes the unit group of ZMod M. Every clause below belongs to the same theorem; there are no additional arithmetic hypotheses.

Equal coordinates give equal depths after every common legal continuation, and equal responses force equal coordinates. In the low branch the actual quotients x/p^r and y/p^r are units modulo p^(h-r). A Bezout inverse of the first quotient gives a unit t carrying x to y modulo N and satisfying t=1 modulo M. Multiplying each affine response by t preserves its gcd with N. In the high branch coordinate equality already gives full congruence modulo N.

For the reverse implication, the empty continuation identifies the current depth. Put q=min(r,e), use multiplier p^(e-q), and cancel x by the signed translation parameter -x/p^q. The x-response is zero, so the y-response must be divisible by N. Cancellation leaves equality of the relevant quotient coordinates modulo M. Signed tests have common legal lifts: A=a mod N+N>0 and B=b mod M>=0. Thus the cancellation test is realized by a positive multiplier and finitely many forward additions.

Every source residue has the positive representative x mod N+N. In particular the zero multiplier residue has representative N, and a zero source residue has a positive representative. At e=h the stored low unit coordinate is 0 modulo 1, the unique unit of that ring; the inverse used in the proof remains an inverse of the actual quotient modulo p^(h-r). These claims concern one local prime power. They do not assemble different primes or realize translations from a separate addend library.

## References

- Truth anchor: `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.depth`
- Truth anchor: `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.eta`
- Truth anchor: `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.local_classification`
- Truth anchor: `D5/S3/Arith/Congruence/PrimePowerAffineBehavior.run`
