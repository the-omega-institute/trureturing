# Raw unanchored replication

## Abstract

Literal synchronous arrays and countable unit normal forms preserve ordered comparisons while removing unit drift.

M is an arbitrary genuine unital magma, U is any self-map, and c is finite, real, nonnegative and zero on the diagonal. RawCost requires the full four-variable identity c(au,bv)+c(aUu,bUv)+c(aU(Uu),bU(Uv))=3c(a,b)+3c(u,v). It requires no associativity, commutativity, symmetry, triangle inequality, positivity of a bilinear form, surjectivity of U, or equation U(1)=1.

**Theorem 1.1 (Actual finite-depth supplier).**

$$(\forall M: Type, [\operatorname{MulOneClass}\left(M\right)] (\forall U: M \to M, (\forall c: M \to M \to \mathbb{R}, (\operatorname{RawCost}\left(U, c\right) \Rightarrow (\forall N: \mathbb{N}, (0 < N \Rightarrow (\operatorname{RawCost}\left(\operatorname{arrayMarker}\left(U\right), \operatorname{arrayCost}\left(c, N\right)\right) \land (\operatorname{omega}\left(\operatorname{arrayMarker}\left(U\right), \operatorname{arrayCost}\left(c, N\right)\right) = \frac{\operatorname{omega}\left(U, c\right)}{N} \land ((\forall a: M, (\forall b: M, \operatorname{arrayCost}\left(c, N, \operatorname{gamma}\left(U, N, a\right), \operatorname{gamma}\left(U, N, b\right)\right) = \operatorname{c}\left(a, b\right))) \land ((\forall a: M, (\operatorname{arrayCost}\left(c, N, \operatorname{gamma}\left(U, N, a\right), 1\right) \le ((3 \cdot \operatorname{c}\left(a, 1\right))+\frac{(3 \cdot \operatorname{omega}\left(U, c\right))}{N}) \land \operatorname{arrayCost}\left(c, N, 1, \operatorname{gamma}\left(U, N, a\right)\right) \le ((3 \cdot \operatorname{c}\left(1, a\right))+\frac{(3 \cdot \operatorname{omega}\left(U, c\right))}{N}))) \land (\forall x: M, (\forall n: \mathbb{N}, (\operatorname{c}\left(\operatorname{iterate}\left(U, n, x\right), 1\right)+\operatorname{c}\left(1, \operatorname{iterate}\left(U, n, x\right)\right)) \le ((9 \cdot (\operatorname{c}\left(x, 1\right)+\operatorname{c}\left(1, x\right)))+(24 \cdot \operatorname{omega}\left(U, c\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawUnanchoredReplication.raw_replication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sigma(N) is literally Fin N -> Fin 3. The cost divides the sum over all coordinate arrays by N*3^N. Product and marker act coordinatewise, and the actual unit is the constant old-unit array. The right comb applies a*U^k(inner) at each node. Every source at a coordinate uses the same phase e=(3-s mod 3) mod 3, where s is the sum of that coordinate's phase choices. Thus 3 divides s+e. The corrected old-unit source is U^(s+e)(1), which need not be the actual array unit. The theorem retains every ordered comparison, both actual-unit budgets, the complete raw law and exact unit-budget scaling.

The raw recurrence at the two true units is nonnegative, so ThreeWayBalance.nonneg_recurrence_constant supplies synchronous marker isometry. Subtracting consecutive balance laws gives period three for simultaneous right multiplication by unit-orbit markers. Two further balance instances give the unit-orbit budget. These facts provide unit control after phase completion. The synchronous right-comb sum is proved by induction over the literal coordinate arrays, preserving multiplicity, bracketing and order.

**Theorem 1.2 (Uniform budgets on actual unit normal forms).**

$$(\forall M: Type, [\operatorname{MulOneClass}\left(M\right)] (\forall U: M \to M, (\forall c: M \to M \to \mathbb{R}, (\forall A: Type, (\forall f: A \to M, (\operatorname{RawCost}\left(U, c\right) \Rightarrow (\operatorname{budget}\left(f, U, c, 1\right) = 0 \land ((\forall a: A, \operatorname{budget}\left(f, U, c, \operatorname{source}\left(a\right)\right) = ((3 \cdot (\operatorname{c}\left(\operatorname{f}\left(a\right), 1\right)+\operatorname{c}\left(1, \operatorname{f}\left(a\right)\right)))+(6 \cdot \operatorname{omega}\left(U, c\right)))) \land ((\forall s: \operatorname{Term}\left(A\right), \operatorname{budget}\left(f, U, c, \operatorname{termMarker}\left(s\right)\right) = ((9 \cdot \operatorname{budget}\left(f, U, c, s\right))+(24 \cdot \operatorname{omega}\left(U, c\right)))) \land ((\forall s: \operatorname{Term}\left(A\right), (\forall t: \operatorname{Term}\left(A\right), \operatorname{budget}\left(f, U, c, (s \cdot t)\right) \le (3 \cdot (\operatorname{budget}\left(f, U, c, s\right)+\operatorname{budget}\left(f, U, c, t\right))))) \land (\forall N: \mathbb{N}, (0 < N \Rightarrow (\forall s: \operatorname{Term}\left(A\right), (\forall t: \operatorname{Term}\left(A\right), ((\operatorname{modelCost}\left(f, U, c, N, s, 1\right)+\operatorname{modelCost}\left(f, U, c, N, 1, s\right)) \le \operatorname{budget}\left(f, U, c, s\right) \land \operatorname{modelCost}\left(f, U, c, N, s, t\right) \le (3 \cdot (\operatorname{budget}\left(f, U, c, s\right)+\operatorname{budget}\left(f, U, c, t\right))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawUnanchoredReplication.normal_form_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same budget controls all actual evaluation depths. Smart multiplication first removes a unit factor; nonnegativity then gives B(st)<=3(B(s)+B(t)) even in those reduced cases. At a nonunit product the equality follows from the ordered constructor. These bounds supply the compact intervals used by the common all-pair extraction.

**Theorem 1.3 (A common limit on the free unital U terms).**

$$(\forall M: Type, [\operatorname{MulOneClass}\left(M\right)] (\forall U: M \to M, (\forall c: M \to M \to \mathbb{R}, (\forall A: Type, [\operatorname{Finite}\left(A\right)] (\forall f: A \to M, (\operatorname{RawCost}\left(U, c\right) \Rightarrow (\exists d: \operatorname{Term}\left(A\right) \to \operatorname{Term}\left(A\right) \to \mathbb{R}, (\exists rho: \mathbb{N} \to \mathbb{N}, (\operatorname{StrictMono}\left(rho\right) \land ((\forall s: \operatorname{Term}\left(A\right), (\forall t: \operatorname{Term}\left(A\right), \operatorname{Tendsto}\left(\lambda l: \mathbb{N} \mapsto \operatorname{modelCost}\left(f, U, c, (\operatorname{rho}\left(l\right)+1), s, t\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{d}\left(s, t\right)\right)\right))) \land (\operatorname{RawCost}\left(\operatorname{termMarker}\left(\right), d\right) \land (\operatorname{omega}\left(\operatorname{termMarker}\left(\right), d\right) = 0 \land ((\forall a: A, (\forall b: A, \operatorname{d}\left(\operatorname{source}\left(a\right), \operatorname{source}\left(b\right)\right) = \operatorname{c}\left(\operatorname{f}\left(a\right), \operatorname{f}\left(b\right)\right))) \land ((\forall a: A, \operatorname{source}\left(a\right) \neq 1) \land (\operatorname{termMarker}\left(1\right) \neq 1 \land (\forall P: \operatorname{Term}\left(A\right) \to Prop, ((\operatorname{P}\left(1\right) \land ((\forall a: A, \operatorname{P}\left(\operatorname{source}\left(a\right)\right)) \land ((\forall s: \operatorname{Term}\left(A\right), (\operatorname{P}\left(s\right) \Rightarrow \operatorname{P}\left(\operatorname{termMarker}\left(s\right)\right))) \land (\forall s: \operatorname{Term}\left(A\right), (\forall t: \operatorname{Term}\left(A\right), ((\operatorname{P}\left(s\right) \land \operatorname{P}\left(t\right)) \Rightarrow \operatorname{P}\left((s \cdot t)\right))))))) \Rightarrow (\forall s: \operatorname{Term}\left(A\right), \operatorname{P}\left(s\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawUnanchoredReplication.raw_zero_drift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is any finite type of labels, and f maps those labels to the original magma; repetitions and the old unit are allowed. Expr has separate constructors for unit, source, unary marker and ordered binary product. Term is the subset of unit normal forms: a product has two nonunit normal children. Multiplication removes a unit factor and otherwise keeps the binary product constructor. U(unit) is retained. Evaluation into every actual array model respects these operations. Consequently only the two-sided unit laws are imposed; no original operation-preserving or unit-preserving embedding is asserted.

For a source a the budget is 3(c(f(a),1)+c(1,f(a)))+6 omega. Unit has budget zero, a marker node has budget 9B+24 omega, and a nonunit product has budget 3(B(s)+B(t)). For every N>=1 the two unit comparisons of an evaluated term sum to at most its budget, and each ordered pair costs at most 3(B(s)+B(t)). All term pairs form one countable index type. The compact product of their finite closed intervals yields a single strictly increasing subsequence, rather than separate choices for separate pairs. All finite scalar balance identities pass to that same limit. Exact omega/N scaling gives zero unit drift, and the source matrix remains exact. The final induction principle states that the actual unit, source symbols, marker and binary product generate every element of Term. Each source symbol differs from the new unit, even if its original label equals the old unit.

Finite sums, the nonnegative recurrence and countable compact extraction are reused mathematical tools. The construction concerns the stated algebraic comparison model; it supplies no additional physical preparation or measurement assumptions and makes no literature priority claim.

## Application: bounded row recurrence on every free unit term

C133 Unanchored Marker Bounded Orbits Continuation W, Section 29.1, applies the free-term evaluator to a specified nine-state unital magma. The result is one real function on all natural times and all original free unit terms. The following definitions, parameter correspondence and derivation retain that application of existing results; the finite table normalization and witness packaging introduce no new canonical mathematical declaration or theorem handle.

The original carrier is this module's Term Empty. There are no external source generators. Expr has unit, mark and ordered binary product constructors; Normal and termProduct remove exactly left and right unit factors. All other finite bracketings and every finite marker depth remain. In this section U means termMarker on this original carrier. No associativity, commutativity, marker homomorphism, equation U(1)=1 or identity U^3=I is imposed on original terms. In particular, U^3(1) and 1 remain different normal forms. The finite auxiliary evaluation below is a map out of that carrier, not a replacement of it.

### Auxiliary states, source parameters and exact readings

Nine consists of nine distinct labels e,p,q,b0,b1,b2,c0,c1,c2. To match the source exactly, put omega=exp(2*pi*i/3) and Theta={1,omega,omega^2,-1,-omega,-omega^2}. Source e,p,q map respectively to e,p,q. Our bi denotes the source label b_(omega^i), and our ci denotes its b_(-omega^i), for i=0,1,2. Thus b0,b1,b2 correspond to phases 1,omega,omega^2, while c0,c1,c2 correspond to -1,-omega,-omega^2. The label q here is an object, not the external comparison function q(x)=c(x,1). Define chi(e)=chi(p)=chi(q)=0, chi(bi)=omega^i and chi(ci)=-omega^i.

The full marker table is nineMarker(e)=p, nineMarker(p)=q, nineMarker(q)=e; nineMarker(b0)=b2, nineMarker(b2)=b1, nineMarker(b1)=b0; nineMarker(c0)=c2, nineMarker(c2)=c1, nineMarker(c1)=c0. Equivalently it subtracts one modulo three from each phase index. This is precisely the source U0, since chi(nineMarker(x))=omega^2*chi(x). Its period three is an auxiliary-state identity only.

The following ordered rules define every product nineMul(a,b), with e as both-sided unit. First nineMul(e,b)=b and nineMul(a,e)=a for all nine states. For every a and every i, nineMul(a,bi)=bi and nineMul(a,ci)=ci. For each phase state d in {b0,b1,b2,c0,c1,c2}, nineMul(d,p)=nineMul(d,q)=d. Finally nineMul(p,p)=nineMul(q,p)=c0 and nineMul(p,q)=nineMul(q,q)=b2. The overlapping unit and right-phase rules agree. These cases cover all 81 ordered pairs. For example nineMul(nineMul(p,q),p)=b2 while nineMul(p,nineMul(q,p))=c0, so no associativity is used. Taking one=e and multiplication=nineMul gives a MulOneClass: its only required equations are the two unit rules just specified.

Define nineReading(n,x)=1+Re(omega^n*chi(x)). It depends only on n modulo three. The exact rational readings, ordered by residues n=0,1,2, are: e:(1,1,1), p:(1,1,1), q:(1,1,1); b0:(2,1/2,1/2), b1:(1/2,1/2,2), b2:(1/2,2,1/2); c0:(0,3/2,3/2), c1:(3/2,3/2,0), c2:(3/2,0,3/2). These nine triples specify the reading for every natural n, with exact real rational values and no approximation to a complex root. They are the source H_n under the parameter map above.

Every entry lies in [0,2], and the three unit-orbit labels always read one. The marker table and these triples give the shift identity for all nine states and every n:

$$
(\forall n: \mathbb{N}, (\forall x: Nine, \operatorname{nineReading}\left((n+1), \operatorname{nineMarker}\left(x\right)\right) = \operatorname{nineReading}\left(n, x\right)))
$$

Here is the complete derivation of the finite recurrence, rather than a sample at bounded term depth. For a right phase state t with chi(t)=zeta, right absorption and the marker rule give omega^k*chi(nineMul(s,nineMarker^k(t)))=omega^k*omega^(2k)*zeta=zeta for k=0,1,2, for every s. Their sum is 3*zeta. For t=e the sum is chi(s)+omega*chi(nineMul(s,p))+omega^2*chi(nineMul(s,q)). It is zero when s=e. For s=p or q it is -omega+omega^4=0. For a phase state s it is (1+omega+omega^2)*chi(s)=0. The cases t=p,q are cyclic rotations of this same weighted sum, multiplied by a nonzero power of omega, and remain zero. These cases exhaust all nine choices of t and every s. Thus the weighted chi sum is always 3*chi(t). Multiply it by omega^n, take real parts and add the three constant ones. This gives, with every summand and its time index retained:

$$
(\forall n: \mathbb{N}, (\forall s: Nine, (\forall t: Nine, ((\operatorname{nineReading}\left(n, \operatorname{nineMul}\left(s, t\right)\right)+\operatorname{nineReading}\left((n+1), \operatorname{nineMul}\left(s, \operatorname{nineMarker}\left(t\right)\right)\right))+\operatorname{nineReading}\left((n+2), \operatorname{nineMul}\left(s, \operatorname{nineMarker}\left(\operatorname{nineMarker}\left(t\right)\right)\right)\right)) = (3 \cdot \operatorname{nineReading}\left(n, t\right)))))
$$

Equivalently, substitute the 81 ordered products into the three exact reading columns, reducing n,n+1,n+2 modulo three. This finite rational normalization derives the displayed identity inside this application; it is not a new independent canonical theorem.

### Unrestricted evaluation and the complete seven clauses

Instantiate the original evaluate with this MulOneClass Nine, U=nineMarker and the unique function Empty -> Nine. In the formulas below, evaluate nineMarker t abbreviates RawUnanchoredReplication.evaluate nineMarker (fun a : Empty => nomatch a) t; the omitted empty assignment is fixed once for the entire domain. The original eval_one, eval_mark and eval_product give exactly evaluate nineMarker 1=e, evaluate nineMarker (U t)=nineMarker(evaluate nineMarker t), and evaluate nineMarker (s*t)=nineMul(evaluate nineMarker s,evaluate nineMarker t). These are the existing evaluator's laws, including both unit-reduction cases of termProduct. They apply to every original normal form, with no depth parameter or subsequent extension choice.

The marker law is a semiconjugacy. Function.Semiconj.iterate_right applied to that law yields the following identity for every original t and every natural j; it preserves the original marker iterates before evaluating them:

$$
(\forall j: \mathbb{N}, (\forall t: \operatorname{Term}\left(\operatorname{Empty}\left(\right)\right), \operatorname{evaluate}\left(\operatorname{nineMarker}\left(\right), \operatorname{iterate}\left(U, j, t\right)\right) = \operatorname{iterate}\left(\operatorname{nineMarker}\left(\right), j, \operatorname{evaluate}\left(\operatorname{nineMarker}\left(\right), t\right)\right)))
$$

For all marked units, take the actual subset S={e,p,q} of Nine. Its closure is explicit: nineMarker(e)=p, nineMarker(p)=q and nineMarker(q)=e all belong to S. Hence Set.MapsTo nineMarker S S holds, and Set.MapsTo.iterate supplies Set.MapsTo (nineMarker^[j]) S S for every natural j. Since e belongs to S, every nineMarker^[j](e) belongs to S and reads one for every n. Combining this with the semiconjugacy identity and eval_one proves the marked-unit clause for every j, not merely j=0,1,2. This uses the existing set-iteration theorem; no new induction result is needed.

Fix a single global function, for every natural n and every original t:

$$
(\forall n: \mathbb{N}, (\forall t: \operatorname{Term}\left(\operatorname{Empty}\left(\right)\right), \operatorname{h}\left(n, t\right) = \operatorname{nineReading}\left(n, \operatorname{evaluate}\left(\operatorname{nineMarker}\left(\right), t\right)\right)))
$$

The first three clauses follow directly from the exact readings and the preceding unit-orbit argument:

$$
(\forall n: \mathbb{N}, (\forall t: \operatorname{Term}\left(\operatorname{Empty}\left(\right)\right), (0 \le \operatorname{h}\left(n, t\right) \land \operatorname{h}\left(n, t\right) \le 2)))
$$

$$
(\forall n: \mathbb{N}, \operatorname{h}\left(n, 1\right) = 1)
$$

$$
(\forall n: \mathbb{N}, (\forall j: \mathbb{N}, \operatorname{h}\left(n, \operatorname{iterate}\left(U, j, 1\right)\right) = 1))
$$

For clause four, apply the finite shift identity at the actual state evaluate nineMarker t and use eval_mark:

$$
(\forall n: \mathbb{N}, (\forall t: \operatorname{Term}\left(\operatorname{Empty}\left(\right)\right), \operatorname{h}\left((n+1), \operatorname{termMarker}\left(t\right)\right) = \operatorname{h}\left(n, t\right)))
$$

For clause five, let a=evaluate nineMarker s and b=evaluate nineMarker t for arbitrary original s,t. The three evaluated original terms s*t, s*U(t) and s*U(U(t)) are respectively nineMul(a,b), nineMul(a,nineMarker(b)) and nineMul(a,nineMarker(nineMarker(b))), by eval_product and eval_mark. Evaluate their readings at n,n+1,n+2 respectively and apply the finite identity at these actual a,b. Its right side is 3*nineReading(n,b)=3*h(n,t). Consequently the full recurrence is:

$$
(\forall n: \mathbb{N}, (\forall s: \operatorname{Term}\left(\operatorname{Empty}\left(\right)\right), (\forall t: \operatorname{Term}\left(\operatorname{Empty}\left(\right)\right), ((\operatorname{h}\left(n, (s \cdot t)\right)+\operatorname{h}\left((n+1), (s \cdot \operatorname{termMarker}\left(t\right))\right))+\operatorname{h}\left((n+2), (s \cdot \operatorname{termMarker}\left(\operatorname{termMarker}\left(t\right)\right))\right)) = (3 \cdot \operatorname{h}\left(n, t\right)))))
$$

For the last two clauses keep the specified original composite z=(U1)*(U1), with exactly those two marked-unit factors. Its evaluation is nineMul(p,p)=c0, which is the source b_(-1). The residue-zero reading is therefore zero, whereas the original unit reads one:

$$
\operatorname{h}\left(0, (\operatorname{termMarker}\left(1\right) \cdot \operatorname{termMarker}\left(1\right))\right) = 0
$$

$$
(\forall C: \mathbb{R}, \neg (\operatorname{h}\left(0, 1\right) \le (C \cdot \operatorname{h}\left(0, (\operatorname{termMarker}\left(1\right) \cdot \operatorname{termMarker}\left(1\right))\right))))
$$

Indeed, for each real C the proposed inequality reduces to 1<=C*0=0, which is false. This includes every finite real constant, with no sign restriction. The seven clauses hold simultaneously for this one h, independently quantified over all n,j and all original s,t. Arbitrary finite bracketing is handled by the unrestricted original evaluator. The auxiliary image is finite; the original free carrier is not identified with it, and no unexamined finite-depth tail remains.

### Full-relation and realization boundaries

The source is C133 Unanchored Marker Bounded Orbits Continuation W, Theorem 29.1 and Proposition 29.2. The mathematical ingredients reused here are this module's original Term, termProduct, termMarker, evaluate, eval_one, eval_mark and eval_product, together with Function.Semiconj.iterate_right and Set.MapsTo.iterate. Literal finite tables, their rational normalization, the evaluation transport and logical witness packaging supply the application. They add no canonical theorem, Describe or truth anchor and make no literature priority claim.

Proposition 29.2 keeps a crucial stronger premise separate. If a complete nonnegative four-variable R model actually contained the auxiliary Nine algebra as a subalgebra preserving its unit, multiplication and marker, then every auxiliary state a would satisfy c(x,a)=q(x) and c(a,x)=r(x) for every external x, where q(x)=c(x,1), r(x)=c(1,x). For a right phase state v, its three marker iterates are phase states and the absorption rules give a*U^k(v)=U^k(v)=1*U^k(v) for k=0,1,2. The source's full-R row-and-column identification argument then gives those equalities. In particular q(x)=1 and c(x,c0)=0, with c0=source b_(-1), cannot coexist under that actual-subalgebra premise.

This application installs no such actual nine-state subalgebra of a full-R model and constructs no external nonnegative four-variable R kernel. Equality of two auxiliary evaluations identifies neither the original terms nor their whole R rows or columns. It licenses no quotient by those fibers. The row recurrence does not supply arbitrary external composite constraints, the source's general external-left-factor constraints, or feasibility of all finite systems for any fixed (lambda,B). It establishes no global Hilbert representation, general full-source classification, or physical realization. Preparation, records, measurements, reference systems, joint operations, time operations and source realizability remain additional contracts. Neither the full quantum representation problem nor its physical contract is settled by this row application.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RawUnanchoredReplication.normal_form_budgets`
- Truth anchor: `D5/S3/Quantum/Completion/RawUnanchoredReplication.raw_replication`
- Truth anchor: `D5/S3/Quantum/Completion/RawUnanchoredReplication.raw_zero_drift`
- Dependency: [D5/S3/QuadraticForms/ThreeWayBalance](../../QuadraticForms/ThreeWayBalance.md)
