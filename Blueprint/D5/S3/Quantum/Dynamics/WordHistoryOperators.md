# Word history operators

## Abstract

Creation on all finite words and the unbounded length multiplier on finite support.

**Theorem 1.1 (No bounded extension of word length multiplication).**

$$(\forall Alphabet: \operatorname{Type}\left(\right), (\forall g: Alphabet, \neg(\exists A: \operatorname{ContinuousComplexLinearMap}\left(\operatorname{WordHilbert}\left(Alphabet\right), \operatorname{WordHilbert}\left(Alphabet\right)\right), (\forall f: \operatorname{WordHilbert}\left(Alphabet\right), (\forall hf: \operatorname{FiniteSupport}\left(f\right), (\operatorname{apply}\left(A, f\right) = \operatorname{number}\left(f, hf\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/WordHistoryOperators.number_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alvaro Arias; Gelu Popescu (1994). *Factorization and Reflexivity on Fock spaces*. URL: <https://arxiv.org/abs/math/9404209>.

*Commentary.*

Let Alphabet be any type and g one of its letters. WordHilbert is the complex Hilbert space ell2 of all finite lists over Alphabet, including the empty word and arbitrarily long words. FiniteSupport means that only finitely many word coordinates are nonzero. The number operator multiplies each word coordinate by its length; its finite-support argument proves that the resulting vector still belongs to ell2. For any proposed continuous linear extension A, choose an integer n larger than its operator norm. The unit basis vector at the word replicate n g has number-operator norm n, contradicting the operator-norm bound for A. This is an arbitrary-alphabet operator obstruction, not a finite truncation or a claim of a bounded length operator.

The right append map is defined canonically from the orthogonal family of coordinate lines at words ending in g. OrthogonalFamily.linearIsometry supplies its extension to the complete Hilbert space and preserves its norm. Its single-coordinate rule, lp.evalCLM and map_tsum give the coordinate at wg and zero outside that image. Applying the adjoint inner-product identity to a basis vector gives the adjoint coordinate at wg. Thus LinearIsometry.adjoint_comp_self gives Sg* Sg=I, while Sg Sg* is the projection onto words ending in g. Evaluation at the empty-word unit vector shows the projection is proper.

Finite partial sums of lp.hasSum_single prove density of finite support. The support of Nf is contained in the support of f; creation sends the support into the append image; the adjoint sends it into the dropLast image. These are a common invariant dense domain. On that domain the coordinate length identity length(wg)=length(w)+1 gives NSg-SgN=Sg. Appending any inverse-readout letter is still creation: its action on the empty-word vector differs from Sg*, and two appends send the basis word w to the longer word wg inverse, never back to w. These exact applications of orthogonal-family, adjoint, summation and list identities remain temporary compiled applications rather than additional named project theorems. Their definitions, parameter correspondence and derivation are retained here.

The original finite nonempty alphabet supplies g, so it is a special case without a bound on word length. A readout that assigns inverse system gates does not impose cancellation on the free word carrier. Arias and Popescu use left creation on Fock space; word reversal identifies that convention with this right append convention. The theorem is reusable formal content; no claim of new literature mathematics is made.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/WordHistoryOperators.number_unbounded`
