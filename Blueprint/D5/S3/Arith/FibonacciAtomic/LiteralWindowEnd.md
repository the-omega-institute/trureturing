# Literal Windows and Positive End

## Abstract

Low-to-high three-bit windows have a terminal flag as well as a seam. Successful literal End queries correspond to independent selected positions.

**Theorem 1.1 (The seam guard recognizes the flattened legal word).**

$$\begin{aligned}\forall s, E \in B, \forall w \in W^{*},\\(\operatorname{run}(\operatorname{some}((s, E)), w) = \operatorname{some}((\operatorname{lastFold}(s, w), \operatorname{endFold}(E, w))) \iff \operatorname{legal}(s, \operatorname{flatten}(w))) \land\\(\operatorname{run}(\operatorname{some}((s, E)), w) = none \iff \neg\operatorname{legal}(s, \operatorname{flatten}(w))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd.execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here B is the Boolean set, W is the five-letter window alphabet, W* is its finite-word set, and none is the absorbing error. The letters are 000, 100, 010, 101 and 001 in low-to-high order. The final seam and End flag are the following folds; the initial End flag survives only for the empty word.

$$
\begin{aligned}\operatorname{lastFold}(s, w) = \operatorname{foldl}(((a, b) \mapsto \operatorname{last}(b)), s, w),\\\operatorname{endFold}(E, w) = \operatorname{foldl}(((a, b) \mapsto \operatorname{nonzero}(b)), E, w).\end{aligned}
$$

A live transition rejects an incoming seam 1 followed by a low bit 1. Otherwise it takes the high bit as the new seam and records whether the current window is nonzero as End. Legal(s,flatten(w)) includes the incoming seam and excludes adjacent ones in the complete flattened word.

**Theorem 1.2 (Legal flattened words are window seam chains).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd.legal_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd.legal_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This interface exposes the adjacent-window chain form of the legal flattened language. It is reused by the gap histogram module and does not introduce a new counting claim.

**Theorem 1.3 (All successful bounded queries have an exact independent-set parametrization).**

$$\begin{aligned}\forall t \in \mathbb{N}, (\exists e: \operatorname{Equiv}(S_{t}, I_{t}),\\(\forall x \in I_{t}, e^{-1}(x) = \operatorname{encode}(t, x)) \land\\(\forall w \in S_{t}, \operatorname{independentBits}(t, e(w)) = \operatorname{flatten}(\operatorname{pad}(t, w))) \land\\(\forall w \in S_{t}, \forall r \in \mathbb{N}, \forall u \in \mathbb{N}, \forall v \in \mathbb{N}, \operatorname{query}(r, u, v, w) = \operatorname{some}((r+\operatorname{O}(t, u, v, e(w))))) \land\\(\forall H \in \mathbb{N}, \forall u \in \mathbb{N}, \forall v \in \mathbb{N}, \forall w \in S_{t}, \operatorname{value}([u]_{H}, [v]_{H}, \operatorname{flatten}(w)) = [\operatorname{O}(t, u, v, e(w))]_{H})) \land\\\lvert S_{t} \rvert = F_{3t+1} \land\\(\forall w \in W^{*}, \forall r \in \mathbb{N}, \forall u \in \mathbb{N}, \forall v \in \mathbb{N}, \operatorname{query}(r, u, v, w) = none \iff \neg\operatorname{Success}(w)) \land\\(\forall w \in W^{*}, \forall r \in \mathbb{N}, \forall u \in \mathbb{N}, \forall v \in \mathbb{N}, (\operatorname{Success}(w) \land 0 < r) \implies (\exists N \in \mathbb{N}, 0 < N \land \operatorname{query}(r, u, v, w) = \operatorname{some}(N))) \land\\\lvert L_{t} \rvert = \sum_{n=0}^{t}5^{n} \land\\\lvert R_{t} \rvert = \sum_{n=0}^{t}5^{n} - F_{3t+1} \land\\(\forall H \in \mathbb{N}, \forall u \in \operatorname{ZMod}(H), \forall v \in \operatorname{ZMod}(H), \lvert \operatorname{centerImage}(t, H, u, v) \rvert \le F_{3t+1}) \land\\(\forall epsilon \in B, \forall w \in W^{*}, \forall N \in \mathbb{N}, \operatorname{initialized}(epsilon, w) = \operatorname{some}(N) \implies 0 < N).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All word lengths are numbers of whole windows. S_t is the set of words of length at most t with a true End flag after running from (seam,End)=(true,true); L_t contains every such literal word, and R_t contains those in L_t without success. I_t consists of independent Boolean selections at offsets 1 through 3t-1, identified with their selected-position sets; I_0 is a singleton. The empty selection gives the empty query, which is charged and successful.

$$
\begin{aligned}\operatorname{Success}(w) \iff \operatorname{endable}(\operatorname{run}(\operatorname{some}((true, true)), w)) = true,\\S_{t} = \{w \in W^{*}\mid\operatorname{length}(w) \le t \land \operatorname{Success}(w)\},\\L_{t} = \{w \in W^{*}\mid\operatorname{length}(w) \le t\},\\R_{t} = \{w \in L_{t}\mid\neg\operatorname{Success}(w)\},\\I_{0} = \{\emptyset\},\\t > 0 \implies I_{t} = \{x \subseteq \{i \in \mathbb{N}\mid1 \le i < 3t\}\mid\operatorname{noAdjacent}(x)\}.\end{aligned}
$$

Equiv(S_t,I_t) is the type of invertible maps; e inverse is the reverse map. Encode prepends the forced zero bit, packs windows, and removes only terminal whole 000 windows. Its inverse pads a successful word to t windows and flattens it. The selected offset below uses F_0=0 and F_1=1, so position 1 contributes v.

$$
\operatorname{O}(t, u, v, x) = \sum_{i \in x}(F_{i-1}u+F_{i}v), x \in I_{t}.
$$

The modular value equality uses the same natural u and v after reduction modulo H. ZMod(H) is the residue ring and [a]_H denotes reduction of a natural a. CenterImage(t,H,u,v) is the set of negated modular values of successful words. A nonzero terminal window 100 or 010 is retained; first-01 words are retained. A trailing whole 000 window clears End and gives the same error for every numeric input.

$$
\operatorname{centerImage}(t, H, u, v) = \{-\operatorname{value}(u, v, \operatorname{flatten}(w))\mid w \in S_{t}\}, u, v \in \operatorname{ZMod}(H).
$$

Initialized(epsilon,w) uses r=epsilon, u=2, v=3 and starts with both Boolean state fields equal to epsilon. Its successful numeric answer is positive. Applying the original terminal readout to that answer gives H divided by gcd(N,H).

The existing admissible-word count gives F_(3t+1) successes. For t=3 there are 55 successes among 156 literal words, leaving 101 errors. The image of their modular translations or negated centers has at most 55 elements; different successful words may have the same modular image. This parametrization does not establish residue realization at a common returned row or the finite-center identification criterion.

$$
\begin{aligned}\lvert S_{3} \rvert = 55, \lvert L_{3} \rvert = 156, \lvert R_{3} \rvert = 101,\\\forall H \in \mathbb{N}, \forall u \in \operatorname{ZMod}(H), \forall v \in \operatorname{ZMod}(H), \lvert \operatorname{centerImage}(3, H, u, v) \rvert \le 55.\end{aligned}
$$

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd.execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd.legal_chain`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd.result`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](../../../S1/Words/AdmissibleWords/AdmissibleCount.md)
- Dependency: [D5/S3/Arith/ZeckendorfFutureKernel](../ZeckendorfFutureKernel.md)
