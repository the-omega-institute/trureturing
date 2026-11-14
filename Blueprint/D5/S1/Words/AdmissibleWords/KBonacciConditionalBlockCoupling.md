# Full exterior and sampled prefix

## Abstract

Conditional next-bit couplings and zero screening for forbidden-run words.

Write W(n) for Fin n to Bool and A(k,n,w) for the original DBonacciAdmissible scanner. C(k,n,F,x) is the finite set of legal full words w satisfying w(i)=x(i) for every i in F. The fixed set F can contain the entire exterior of a contiguous block and any sampled prefix. Both ends remain fixed. L(F,x,h) is completionLaw, the uniform PMF on this fiber, where h states that the fiber is nonempty.

For PMFs p and q on Bool, J(p,q) denotes bitCoupling. Set a=p(false) and b=q(false). If a is at most b, its masses at (false,false), (false,true), (true,false), (true,true) are a, zero, b-a, one-b. Otherwise exchange the two coordinates of the same construction with a and b interchanged. This is the finite shared-threshold next-bit law.

**Theorem 1.1 (Exact conditional-bit marginals and a common zero).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (h:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, x\right)\right)), ((\forall (g:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, y\right)\right)), ((\forall (i:\operatorname{Fin}\left(n\right)), (((\neg (i \in F)) \implies (((\operatorname{mapFst}\left(\operatorname{J}\left(\operatorname{evalLaw}\left(F, x, h, i\right), \operatorname{evalLaw}\left(F, y, g, i\right)\right)\right) = \operatorname{evalLaw}\left(F, x, h, i\right)) \land (\operatorname{mapSnd}\left(\operatorname{J}\left(\operatorname{evalLaw}\left(F, x, h, i\right), \operatorname{evalLaw}\left(F, y, g, i\right)\right)\right) = \operatorname{evalLaw}\left(F, y, g, i\right)) \land (1/2 \leq \operatorname{mass}\left(\operatorname{J}\left(\operatorname{evalLaw}\left(F, x, h, i\right), \operatorname{evalLaw}\left(F, y, g, i\right)\right), \operatorname{false}, \operatorname{false}\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.conditional_step_coupling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The laws p and q in the formula are the pushforwards of L(F,x,h) and L(F,y,g) by evaluation at i. Deleting the one at an unfixed coordinate gives an injection from one-completions into zero-completions while preserving all other bits. Thus each actual conditional zero mass is at least one half. The displayed joint law has exact marginals and common-zero mass equal to their minimum. No lower bound on word length relative to k is required.

**Theorem 1.2 (A common zero screens the earlier prefix).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (((((\operatorname{A}\left(k, n, x\right)) \land (\operatorname{A}\left(k, n, y\right)))) \implies ((\forall (z:\operatorname{Fin}\left(n\right)), (((((\operatorname{at}\left(x, z\right) = \operatorname{false}) \land (\operatorname{at}\left(y, z\right) = \operatorname{false}))) \implies ((\forall (t:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (\operatorname{A}\left(k, n, \operatorname{S}\left(x, z, t\right)\right) \iff \operatorname{A}\left(k, n, \operatorname{S}\left(y, z, t\right)\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.zero_screening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define S(x,z,t)(i) to be x(i) when i is at most z and t(i) otherwise. A forbidden window is either contained in the legal prefix, contained in the shared later assignment, or crosses z. The last possibility contains the specified zero. Hence replacing the legal prefix preserves the entire suffix-completion condition.

**Theorem 1.3 (Uniform suffix laws agree after reset).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), (((((\operatorname{A}\left(k, n, x\right)) \land (\operatorname{A}\left(k, n, y\right)))) \implies ((\forall (z:\operatorname{Fin}\left(n\right)), (((((\operatorname{at}\left(x, z\right) = \operatorname{false}) \land (\operatorname{at}\left(y, z\right) = \operatorname{false}) \land ((\forall (i:\operatorname{Fin}\left(n\right)), (((\operatorname{val}\left(i\right) \leq \operatorname{val}\left(z\right)) \implies (i \in F))))) \land ((\forall (i:\operatorname{Fin}\left(n\right)), (((((i \in F) \land (\operatorname{val}\left(z\right) < \operatorname{val}\left(i\right)))) \implies (\operatorname{at}\left(x, i\right) = \operatorname{at}\left(y, i\right)))))))) \implies (((\operatorname{mapReset}\left(\operatorname{L}\left(F, x\right), y, z\right) = \operatorname{L}\left(F, y\right)) \land ((\forall (w:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (i:\operatorname{Fin}\left(n\right)), (((\operatorname{val}\left(z\right) < \operatorname{val}\left(i\right)) \implies (\operatorname{at}\left(\operatorname{S}\left(y, z, w\right), i\right) = \operatorname{at}\left(w, i\right)))))))) \land (((\operatorname{mapFst}\left(\operatorname{R}\left(F, x, y, z\right)\right) = \operatorname{L}\left(F, x\right)) \land (\operatorname{mapSnd}\left(\operatorname{R}\left(F, x, y, z\right)\right) = \operatorname{L}\left(F, y\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.reset_law_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All coordinates through z are fixed. The two legal exterior words have a zero at z and agree at every fixed coordinate strictly after z. Prefix replacement S(y,z,w) is a bijection between their full completion fibers, with inverse S(x,z,w). It therefore transports the uniform conditional laws exactly. R(F,x,y,z) samples w from L(F,x) and returns the pair (w,S(y,z,w)); its two marginal pushforwards are exactly L(F,x) and L(F,y). Every coordinate strictly after z is preserved.

**Theorem 1.4 (Stopped conditional recursion has exact full-word marginals).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (s:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\right)), (((\operatorname{Nodup}\left(s\right)) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((((\forall (i:\operatorname{Fin}\left(n\right)), (((i \in s) \implies (\neg (i \in F)))))) \implies ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (h:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, x\right)\right)), ((\forall (g:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, y\right)\right)), (((\operatorname{mapFst}\left(\operatorname{P}\left(s, F, x, y, h, g\right)\right) = \operatorname{L}\left(F, x, h\right)) \land (\operatorname{mapSnd}\left(\operatorname{P}\left(s, F, x, y, h, g\right)\right) = \operatorname{L}\left(F, y, g\right)))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.prefix_coupling_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P(s,F,x,y,h,g) denotes prefixCoupling. At each listed site, the finite next-bit joint law is bound to the recursively refined completion law. Its supported bit pairs have nonempty refined fibers. The marginal weight of a bit times its refined uniform completion mass is the original mass on that bit fiber; summing over Bool proves exact disintegration. If the fixed histories already contain a common screening zero and agree at all farther fixed sites, the recursion instead uses resetCoupling, with legal representatives chosen from the actual nonempty fibers. Uniform prefix transport proves both marginals in this stopped branch.

**Theorem 1.5 (Expected internal Hamming cost for an increasing scan).**

$$(\forall (k,n:\mathbb{N}), (((0 < k) \implies ((\forall (s:\operatorname{List}\left(\operatorname{Fin}\left(n\right)\right)), (((((\operatorname{Nodup}\left(s\right)) \land ((\forall (i:\operatorname{Fin}\left(n\right)), ((\forall (j:\operatorname{Fin}\left(n\right)), (((\operatorname{Before}\left(s, i, j\right)) \implies (\operatorname{val}\left(i\right) < \operatorname{val}\left(j\right)))))))))) \implies ((\forall (F:\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((((((\forall (i:\operatorname{Fin}\left(n\right)), (((i \in s) \implies (\neg (i \in F)))))) \land ((\forall (i:\operatorname{Fin}\left(n\right)), (((\neg (i \in F)) \implies (i \in s))))))) \implies ((\forall (x,y:(\operatorname{Fin}\left(n\right) \to \operatorname{Bool})), ((\forall (h:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, x\right)\right)), ((\forall (g:\operatorname{Nonempty}\left(\operatorname{C}\left(k, n, F, y\right)\right)), ((((\forall (i:\operatorname{Fin}\left(n\right)), ((\forall (j:\operatorname{Fin}\left(n\right)), (((((i \in s) \land (j \in F) \land (\operatorname{val}\left(i\right) < \operatorname{val}\left(j\right)))) \implies (\operatorname{at}\left(x, j\right) = \operatorname{at}\left(y, j\right)))))))) \implies (\operatorname{ExpectedHamming}\left(\operatorname{P}\left(s, F, x, y, h, g\right), s\right) \leq 1))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.right_scan_hamming` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ExpectedHamming(J,s) is the sum over full-word pairs w of J(w)H(s,w). Before(s,i,j) means that i occurs strictly before j in the list s. H(s,w) denotes scanHamming: the sum of the zero-one disagreement indicators at the listed sites. The list is strictly increasing and lists the entire complement of F without repetitions. The fixed histories agree at every fixed site farther right than any scanned site. A supported common-zero branch has zero remaining cost, by screening and the reset law. In every other branch the current indicator is at most one, and the recursive expected remaining cost is at most one. Those branches have total mass at most one half, derived from conditional_step_coupling. Their weighted cost is therefore at most one. This estimate uses the same full-word joint law as the marginal theorem. The theorem covers short words and arbitrary nonempty completion fibers; it does not assert reflection, the geometric survival tail, or the final two-orientation contiguous-block assembly.

## Application: actual legal-state refresh, projection and complex energy

Fix integers k >= 2 and n >= 0. The state set S is the actual finite subtype DBonacciName k n: its elements x are full words x.val : Fin n to Bool with proof of DBonacciAdmissible k n x.val. Thus S consists of the legal words with no k consecutive true bits, with open boundaries. In the book's Chapter 39 example on a uniform parent gap, the parameter correspondence is K=k, N=n and the one-based book site j=i.val+1 for i : Fin n. The book's legal-word set W_N corresponds to S, whereas W(n) above denotes all Boolean words, including illegal ones. Every sum over x or y below is over S unless a fiber is specified.

Put Z=card(S), pi(x)=1/Z, and pi[h]=(1/Z) sum_x h(x). The all-zero word is legal, including the unique empty word at n=0, so Z>0. The canonical Names suppliers DBonacciName, DBonacciAdmissible and dbonacci_name_card identify Z with dbonacci k (n+2); Values.dbonacci_level_pos supplies positivity for positive order. The uniformPmf supplier in DBonacci.TerminalSampling realizes pi on this actual nonempty subtype. The normalization is the number of legal states, not the number 2^n of unconstrained words.

Let B be any finite subset of Fin n and take B-complement in the whole set Fin n. No interval or connectedness assumption is imposed. Define ext_B(x)=x.val restricted to B-complement and A_B(x)={y in S : ext_B(y)=ext_B(x)}. Write m_B(x)=card(A_B(x)). The state x belongs to its own fiber, hence m_B(x)>0. Forgetting the legality proof is a bijection from A_B(x) to the original C(k,n,B-complement,x.val), so these two finite sets have the same cardinality. Every exterior coordinate, on all sides of B, is fixed.

The actual full-state refresh law mu_B(x) is the original completionLaw(B-complement,x.val,h_x) pushed to S, where h_x is completion_nonempty applied to x.property. More explicitly, sample a supported completion w from L(B-complement,x.val,h_x) and set legalWord(w) to the subtype element with value w and the legality proof contained in its completion membership. This conversion changes no bit. Equivalently, first sample the uniform PMF on the completion subtype and map this supported legalWord conversion. If a total map on all ambient Boolean words is used, it can return x off the legal support; those inputs have zero mass, so this extension has no effect on mu_B(x).

Forgetting the subtype proof after this pushforward gives exactly the original completionLaw again. Its pushforward by restrictBlock B is the canonical conditionalBlockLaw B x.val x.property from KBonacciIntervalBlockCoupling. Conversely, a block assignment b in that law's support has an original legal completion preimage. Restoring b on B and x.val on every site in B-complement recovers that completion, hence a legal state, and pushes the block law back to mu_B(x). Restriction and restoration are inverse on this support because the entire exterior is fixed. An arbitrary unsupported assignment need not restore to a legal word.

The canonical completionLaw_apply formula therefore gives mu_B(x)(y)=1/m_B(x) for y in A_B(x) and zero otherwise. Define its real transition mass and its action on any complex function f:S to C by T_B(x,y)=indicator(y in A_B(x))/m_B(x) and (E_B f)(x)=sum_y T_B(x,y)f(y). Here T_B(x,y)=(mu_B(x)(y)).toReal is the real mass at y; real weights are embedded in C when multiplying f(y). This identifies the matrix with the original legal-state law, rather than assuming a freely chosen stochastic matrix.

The actual exterior law is q_B=(ext_B)_* pi. For any realizable exterior eta, let C_eta={x in S : ext_B(x)=eta} and m_eta=card(C_eta). Then q_B(eta)=m_eta/Z. In particular q_B(ext_B(x))=m_B(x)/Z. Impossible exteriors have q_B mass zero. For y in C_eta, conditional probability under pi is (1/Z)/(m_eta/Z)=1/m_eta; conditioning on ext_B(x) consequently gives precisely mu_B(x). Thus E_B is conditional averaging with respect to the full exterior, with no assumption of independent exterior bits.

Equality of exterior data partitions S into disjoint nonempty fibers. If y is in A_B(x), then A_B(y)=A_B(x) and m_B(y)=m_B(x); otherwise both directed masses T_B(x,y) and T_B(y,x) vanish. This proves T_B(x,y)>=0 and T_B(x,y)=T_B(y,x). The equality of completion laws on equal fixed data is also exactly the content of the original completionLaw_congr. Each row has m_B(x) entries equal to 1/m_B(x), so sum_y T_B(x,y)=1. Symmetry then gives sum_x T_B(x,y)=1. It follows that sum_x pi(x)T_B(x,y)=pi(y); the other marginal of pi(x)T_B(x,y) is pi(x). Uniform stationarity and reversibility have thus been derived from actual fibers.

Use the conjugate-first uniform pairing <f,g>_pi=(1/Z) sum_x conj(f(x))g(x) and squared norm ||f||_pi^2=(1/Z) sum_x |f(x)|^2, for arbitrary complex f,g. Throughout, |z|^2 is the squared complex modulus conj(z)z, a nonnegative real number, not the complex square z^2. Let Id denote the identity operator on these functions. All sums are finite, so no limiting or integrability assumption is needed.

Let C range once over the distinct nonempty exterior fibers, and put fbar_C=(1/card(C)) sum_{x in C} f(x). Then E_B f is fbar_C throughout C. A second fiber average changes nothing, proving E_B^2=E_B. Moreover E_B f=f if and only if f is constant on every actual exterior fiber: the forward direction follows from equality of their means and the reverse direction from averaging a constant. This identifies the fixed functions and the range of E_B.

Grouping the finite sums by these fibers gives <f,E_B g>_pi=(1/Z) sum_C card(C) conj(fbar_C)gbar_C=<E_B f,g>_pi. In particular <f,E_B f>_pi=(1/Z) sum_C card(C)|fbar_C|^2=||E_B f||_pi^2>=0, with this real number embedded in the complex numbers when compared with the pairing. Thus E_B is self-adjoint and positive semidefinite. For any fiber-constant h, the sum over C of f-fbar_C is zero, so <h,f-E_B f>_pi=0. Together with idempotence this proves that E_B is the orthogonal projection onto the fiber-constant functions.

Put p_x(y)=(mu_B(x)(y)).toReal. Define conditional variance independently from the original law's moments: V_B(f;x)=sum_y p_x(y)|f(y)|^2-|sum_y p_x(y)f(y)|^2. The mean in this definition is E_B f(x) by the preceding law identification. Equivalently the two moments can be taken over the original supported completions w, evaluating f(legalWord(w)); the pushforward preserves both finite sums. This variance is defined by the conditional law, without using a generator energy as its definition.

For a real probability row p_y=p_x(y), let a=sum_y p_y f(y). Expand |f(y)-a|^2=|f(y)|^2-2 Re(conj(a)f(y))+|a|^2. Since sum_y p_y=1 and sum_y p_y f(y)=a, the summed cross term is -2|a|^2 and the final term is |a|^2. Hence V_B(f;x)=sum_y T_B(x,y)|f(y)-E_B f(x)|^2>=0. Equal exteriors have identical laws, means and variances, so V_B(f;x) is constant on each fiber. It is also E_B(|f-E_B f|^2)(x), since E_B f(y)=E_B f(x) on the row support.

The complex energy identity can be checked inside each fiber. Write m=card(C)>0, S_C=sum_{x in C} f(x) and a=S_C/m. Then sum_{x in C} conj(f(x))(f(x)-a)=sum_{x in C}|f(x)|^2-|S_C|^2/m=sum_{x in C}|f(x)-a|^2=(1/(2m)) sum_{x in C} sum_{y in C}|f(x)-f(y)|^2. Indeed sum_x conj(f(x))a=conj(S_C)S_C/m, which is real. In the centered expansion the two conjugate cross terms total -2|S_C|^2/m and the constant terms total |S_C|^2/m. In the ordered pair expansion the two diagonal-square sums total 2m sum_x |f(x)|^2, while the cross terms total -2|S_C|^2. This finite cancellation supplies every equality, including its exact factor two.

Summing the fiber identity and dividing by Z yields the complete chain: Re<f,(Id-E_B)f>_pi = (1/(2Z)) sum_x sum_y T_B(x,y)|f(x)-f(y)|^2 = (1/Z) sum_x sum_y T_B(x,y)|f(y)-E_B f(x)|^2 = (1/Z) sum_x V_B(f;x) = sum_eta q_B(eta)V_B(f;eta) = ||f-E_B f||_pi^2. The pair sum is over ordered pairs of legal states, including the zero diagonal terms. The centered conditional sum has factor 1/Z, whereas the ordered difference sum has factor 1/(2Z).

Here V_B(f;eta) is V_B(f;x) for any x with exterior eta, and may be set to zero for an impossible exterior. It is well-defined because equal exteriors have equal laws. Grouping the state average gives (1/Z) sum_x V_B(f;x)=sum_C (card(C)/Z)(1/card(C)) sum_{x in C}|f(x)-fbar_C|^2. This is exactly expectation under the exterior pushforward q_B, whose weights are card(C)/Z; it is not a uniform average over distinct exteriors. Their fiber-size weights cancel the conditional denominators and produce the global factor 1/Z.

The pairing <f,(Id-E_B)f>_pi itself is real and nonnegative: orthogonality gives <E_B f,f-E_B f>_pi=0 and therefore <f,(Id-E_B)f>_pi=||f-E_B f||_pi^2 as a complex number with zero imaginary part. Alternatively, in the centered double sum replace E_B f(x) by E_B f(y) on every supported pair and use sum_x T_B(x,y)=1; this directly recovers the same squared residual norm. These arguments apply to arbitrary complex functions, with conjugate cross terms retained.

Now take any finite index set I and any family a maps to B_a of finite subsets of Fin n, allowing an empty index set. Set r_a=1 for every a in I, with a separate refresh clock for each index. Define (L_refresh f)(x)=sum_{a in I}((E_{B_a}f)(x)-f(x)), so -L_refresh=sum_{a in I}(Id-E_{B_a}). Define the Dirichlet energy D(f)=Re<f,-L_refresh f>_pi. Linearity and the single-block chain give D(f)=sum_{a in I} ||f-E_{B_a}f||_pi^2=sum_{a in I} pi[V_{B_a}(f;.)]=(1/(2Z)) sum_{a in I} sum_x sum_y T_{B_a}(x,y)|f(x)-f(y)|^2. The corresponding centered and exterior-average expressions are summed with the same indices.

Repeated block values contribute separately, once per clock index; they are not collapsed to a set of distinct blocks. There is no factor 1/M in L_refresh or D, where M=card(I). Only when M>0 may one also introduce the discrete-time average P=(1/M) sum_{a in I} E_{B_a}; then L_refresh=M(P-Id). For I empty, L_refresh and D are zero and no division by M is used. Under the book's parameter map, its blocks are B_a={i : a<=i.val+1<=a+ell-1}, ell=2k-1, indexed by all integers a=2-ell,...,n for n>=1, with M=n+ell-1; equal truncated intervals keep their separate indices. The identities above do not require this particular family.

For B empty, every fiber is {x}, mu_B(x) is the point mass at x, E_B=Id and all single-block energies and conditional variances vanish. For B=Finset.univ, the only realized exterior is empty, the fiber is all of S, mu_B(x)=pi and E_B f=pi[f]. Disconnected blocks satisfy the same formulas because agreement on the whole complement still defines the same partition. No independence of their components is assumed. Short words n<k are included. At n=0 the sole legal state is the empty word, Z=1, every refresh is the identity and every energy vanishes. This asserts no excited eigenvalue or excited gap for an empty chain.

This application gives the actual-law, conditional-projection and complex-energy calculation in the book's Chapter 39 example, Paper derivation: a uniform gap at fixed forbidden-run length. Its canonical suppliers are the original completionLaw_apply and completionLaw_congr, completion_nonempty, DBonacciName and its counting and positivity results, and the restrictBlock and conditionalBlockLaw definitions. It is an application of those laws and finite-sum identities, without a claim of mathematical novelty.

The coupled-generator application in CostCoupling supplies the generic route from actual adjacent-state couplings and a summed drift bound to a uniform Poincare inequality. The fiber calculation here supplies the specific legal-state kernel, its projection and its variance normalization. It does not supply that actual model's summed drift estimate, a complete uniform heat-bath gap, or the comparison from block clocks to single-site clocks. Those additional steps are needed before any uniform gap conclusion can be drawn from this application. It also establishes no parent-Hamiltonian or full-sector gap and no physical or Rauzy realization; those require their own operator identification and sector comparison or realization hypotheses.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.conditional_step_coupling`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.prefix_coupling_marginals`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.reset_law_transport`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.right_scan_hamming`
- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.zero_screening`
- Dependency: [D5/S0/Tower/DBonacci/TerminalSampling](../../../S0/Tower/DBonacci/TerminalSampling.md)
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciIntegerInterval](KBonacciIntegerInterval.md)
- Dependency: [D5/S1/Words/ClosedRunStarts](../ClosedRunStarts.md)
