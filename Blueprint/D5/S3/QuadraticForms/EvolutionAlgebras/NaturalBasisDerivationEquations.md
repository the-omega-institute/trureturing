# Natural-basis derivation equations

## Abstract

Canonical natural-basis equations for actual evolution derivations.

These are the original canonical proof bodies factored from NondegenerateDerivationBlocks. Their qualified mathematical names and hypotheses are preserved. The ambient product is bilinear over an arbitrary field and its actual natural basis has zero mixed products; no associativity, unit or perfectness is assumed. For the normalized statements, label records the natural-square class and w its representative. The exact hypotheses concerning normalized squares, nonzero representatives and separation of distinct classes appear in each statement. Semisimple implications retain that explicit assumption. The scientific application retains Haobo Ma then Wenlin Zhang credit, alongside the classical linear and Lie ingredients; no priority claim is made.

**Theorem 1.1 (Right multiplication in a natural basis).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \forall (x : V), (\forall (j : I), (mu\left(x, b\left(j\right)\right) = \operatorname{smul}\left(\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(x, j\right), mu\left(b\left(j\right), b\left(j\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.mul_basis_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite natural basis, mu(x,b(j)) is the j-th coordinate of x times the square of b(j). Expanding x removes the mixed products.

**Theorem 1.2 (Left multiplication in a natural basis).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \forall (x : V), (\forall (i : I), (mu\left(b\left(i\right), x\right) = \operatorname{smul}\left(\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(x, i\right), mu\left(b\left(i\right), b\left(i\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.mul_basis_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite natural basis, mu(b(i),x) is the i-th coordinate of x times the square of b(i). Commutativity is not needed for this basis expansion.

**Theorem 1.3 (The exact square derivation equation).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \forall (D : \operatorname{derivations}\left(mu\right)), (\forall (i : I), (D\left(mu\left(b\left(i\right), b\left(i\right)\right)\right) = \operatorname{smul}\left(2 \cdot \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), i\right), mu\left(b\left(i\right), b\left(i\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.square_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual derivation sends the square of b(i) to twice its i-th diagonal coefficient times that square. This uses only bilinearity and the finite natural-basis equations.

**Theorem 1.4 (Distinct nonzero lines are independent).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (x : V), (\forall (y : V), (x \ne 0 \Rightarrow \left(y \ne 0 \Rightarrow \left(\operatorname{Submodule}.\operatorname{span}\left(k, \operatorname{Set}.\operatorname{singleton}\left(x\right)\right) \ne \operatorname{Submodule}.\operatorname{span}\left(k, \operatorname{Set}.\operatorname{singleton}\left(y\right)\right) \Rightarrow \forall (s : k), (\forall (t : k), (\operatorname{smul}\left(s, x\right) + \operatorname{smul}\left(t, y\right) = 0 \Rightarrow \left(s = 0 \land t = 0\right)))\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.separate_of_distinct_lines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two nonzero vectors spanning different lines have no nontrivial two-term linear relation over the field. This is the original linear separation proof.

**Theorem 1.5 (Zero coefficients between distinct classes).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (alpha : \operatorname{Type}\left(\right)), (\forall (label : I \to alpha), (\forall (w : alpha \to V), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \left(\forall (i : I), (mu\left(b\left(i\right), b\left(i\right)\right) = w\left(label\left(i\right)\right)) \Rightarrow \left(\forall (a : alpha), (\forall (c : alpha), (a \ne c \Rightarrow \forall (s : k), (\forall (t : k), (\operatorname{smul}\left(s, w\left(a\right)\right) + \operatorname{smul}\left(t, w\left(c\right)\right) = 0 \Rightarrow \left(s = 0 \land t = 0\right))))) \Rightarrow \forall (D : \operatorname{derivations}\left(mu\right)), (\forall (i : I), (\forall (j : I), (label\left(i\right) \ne label\left(j\right) \Rightarrow \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), j\right) = 0)))\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_cross_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized natural squares with separated representative lines, every actual derivation has zero coefficients between different label classes. Nonzero-representative and semisimplicity assumptions are not needed for this implication beyond the stated separation law.

**Theorem 1.6 (Skew off-diagonal coefficients).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (alpha : \operatorname{Type}\left(\right)), (\forall (label : I \to alpha), (\forall (w : alpha \to V), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \left(\forall (i : I), (mu\left(b\left(i\right), b\left(i\right)\right) = w\left(label\left(i\right)\right)) \Rightarrow \left(\forall (a : alpha), (w\left(a\right) \ne 0) \Rightarrow \left(\forall (a : alpha), (\forall (c : alpha), (a \ne c \Rightarrow \forall (s : k), (\forall (t : k), (\operatorname{smul}\left(s, w\left(a\right)\right) + \operatorname{smul}\left(t, w\left(c\right)\right) = 0 \Rightarrow \left(s = 0 \land t = 0\right))))) \Rightarrow \forall (D : \operatorname{derivations}\left(mu\right)), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), j\right) = -\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(j\right)\right), i\right))))\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_off_diagonal_skew` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With normalized nonzero square representatives and separated distinct classes, the off-diagonal coefficients of every actual derivation are skew. The diagonal coefficients are not asserted to vanish.

**Theorem 1.7 (Constant diagonal within one class).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), ([\operatorname{CharZero}\left(k\right)] \forall (alpha : \operatorname{Type}\left(\right)), (\forall (label : I \to alpha), (\forall (w : alpha \to V), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \left(\forall (i : I), (mu\left(b\left(i\right), b\left(i\right)\right) = w\left(label\left(i\right)\right)) \Rightarrow \left(\forall (a : alpha), (w\left(a\right) \ne 0) \Rightarrow \forall (D : \operatorname{derivations}\left(mu\right)), (\forall (i : I), (\forall (j : I), (label\left(i\right) = label\left(j\right) \Rightarrow \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), i\right) = \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(j\right)\right), j\right))))\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_diagonal_eq_on_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In characteristic zero, two natural basis indices with the same normalized nonzero square have equal diagonal coefficients under every actual derivation. Class separation and semisimplicity are not hypotheses of this equality.

**Theorem 1.8 (Commutators have zero diagonal).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (alpha : \operatorname{Type}\left(\right)), (\forall (label : I \to alpha), (\forall (w : alpha \to V), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \left(\forall (i : I), (mu\left(b\left(i\right), b\left(i\right)\right) = w\left(label\left(i\right)\right)) \Rightarrow \left(\forall (a : alpha), (w\left(a\right) \ne 0) \Rightarrow \left(\forall (a : alpha), (\forall (c : alpha), (a \ne c \Rightarrow \forall (s : k), (\forall (t : k), (\operatorname{smul}\left(s, w\left(a\right)\right) + \operatorname{smul}\left(t, w\left(c\right)\right) = 0 \Rightarrow \left(s = 0 \land t = 0\right))))) \Rightarrow \forall (D : \operatorname{derivations}\left(mu\right)), (\forall (E : \operatorname{derivations}\left(mu\right)), (\forall (i : I), (\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(\operatorname{Bracket}.\operatorname{bracket}\left(D, E\right)\left(b\left(i\right)\right), i\right) = 0)))\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_bracket_diagonal_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the normalized nonzero-square and class-separation hypotheses, the actual commutator of any two derivations has zero diagonal in the natural basis. This makes the diagonal map a Lie map to the abelian coordinate algebra.

**Theorem 1.9 (The semisimple diagonal implication).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (alpha : \operatorname{Type}\left(\right)), (\forall (label : I \to alpha), (\forall (w : alpha \to V), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \left(\forall (i : I), (mu\left(b\left(i\right), b\left(i\right)\right) = w\left(label\left(i\right)\right)) \Rightarrow \left(\forall (a : alpha), (w\left(a\right) \ne 0) \Rightarrow \left(\forall (a : alpha), (\forall (c : alpha), (a \ne c \Rightarrow \forall (s : k), (\forall (t : k), (\operatorname{smul}\left(s, w\left(a\right)\right) + \operatorname{smul}\left(t, w\left(c\right)\right) = 0 \Rightarrow \left(s = 0 \land t = 0\right))))) \Rightarrow [\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, \operatorname{derivations}\left(mu\right)\right)] \forall (D : \operatorname{derivations}\left(mu\right)), (\forall (i : I), (\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), i\right) = 0))\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.semisimple_diagonal_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the actual derivation algebra is semisimple, its perfectness and the zero commutator diagonal imply that each actual derivation has zero diagonal. The semisimplicity hypothesis is retained.

**Theorem 1.10 (The exact zero-diagonal consequences).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (alpha : \operatorname{Type}\left(\right)), (\forall (label : I \to alpha), (\forall (w : alpha \to V), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \left(\forall (i : I), (mu\left(b\left(i\right), b\left(i\right)\right) = w\left(label\left(i\right)\right)) \Rightarrow \left(\forall (a : alpha), (w\left(a\right) \ne 0) \Rightarrow \left(\forall (a : alpha), (\forall (c : alpha), (a \ne c \Rightarrow \forall (s : k), (\forall (t : k), (\operatorname{smul}\left(s, w\left(a\right)\right) + \operatorname{smul}\left(t, w\left(c\right)\right) = 0 \Rightarrow \left(s = 0 \land t = 0\right))))) \Rightarrow \forall (D : \operatorname{derivations}\left(mu\right)), (\forall (i : I), (\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), i\right) = 0) \Rightarrow \left(\forall (i : I), (\forall (j : I), (label\left(i\right) \ne label\left(j\right) \Rightarrow \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), j\right) = 0)) \land \left(\forall (i : I), (\forall (j : I), (\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), j\right) = -\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(j\right)\right), i\right))) \land \forall (a : alpha), (a \in \operatorname{Set}.\operatorname{range}\left(label\right) \Rightarrow D\left(w\left(a\right)\right) = 0)\right)\right))\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.properties_of_diagonal_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual derivation with zero diagonal has zero cross-class coefficients, fully skew coefficients and annihilates every representative whose label occurs. This statement assumes zero diagonal directly and does not assume semisimplicity.

**Theorem 1.11 (Converse from skew coefficients and killed squares).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (alpha : \operatorname{Type}\left(\right)), (\forall (label : I \to alpha), (\forall (w : alpha \to V), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \left(\forall (i : I), (mu\left(b\left(i\right), b\left(i\right)\right) = w\left(label\left(i\right)\right)) \Rightarrow \forall (D : \operatorname{Module}.\operatorname{End}\left(k, V\right)), (\left(\forall (i : I), (\forall (j : I), (label\left(i\right) \ne label\left(j\right) \Rightarrow \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), j\right) = 0)) \land \left(\forall (i : I), (\forall (j : I), (\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), j\right) = -\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(j\right)\right), i\right))) \land \forall (a : alpha), (a \in \operatorname{Set}.\operatorname{range}\left(label\right) \Rightarrow D\left(w\left(a\right)\right) = 0)\right)\right) \Rightarrow D \in \operatorname{derivations}\left(mu\right))\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_of_skew_killing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized natural squares, any linear endomorphism with zero cross-class coefficients, skew coefficients and zero action on the occurring square representatives is an actual derivation. This converse needs neither nonzero representatives, class separation nor semisimplicity.

**Theorem 1.12 (The preserved semisimple equivalence).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (alpha : \operatorname{Type}\left(\right)), (\forall (label : I \to alpha), (\forall (w : alpha \to V), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \left(\forall (i : I), (mu\left(b\left(i\right), b\left(i\right)\right) = w\left(label\left(i\right)\right)) \Rightarrow \left(\forall (a : alpha), (w\left(a\right) \ne 0) \Rightarrow \left(\forall (a : alpha), (\forall (c : alpha), (a \ne c \Rightarrow \forall (s : k), (\forall (t : k), (\operatorname{smul}\left(s, w\left(a\right)\right) + \operatorname{smul}\left(t, w\left(c\right)\right) = 0 \Rightarrow \left(s = 0 \land t = 0\right))))) \Rightarrow [\operatorname{LieAlgebra}.\operatorname{IsSemisimple}\left(k, \operatorname{derivations}\left(mu\right)\right)] \forall (D : \operatorname{Module}.\operatorname{End}\left(k, V\right)), (D \in \operatorname{derivations}\left(mu\right) \Leftrightarrow \left(\forall (i : I), (\forall (j : I), (label\left(i\right) \ne label\left(j\right) \Rightarrow \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), j\right) = 0)) \land \left(\forall (i : I), (\forall (j : I), (\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), j\right) = -\operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(j\right)\right), i\right))) \land \forall (a : alpha), (a \in \operatorname{Set}.\operatorname{range}\left(label\right) \Rightarrow D\left(w\left(a\right)\right) = 0)\right)\right))\right)\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.semisimple_normalized_derivation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original semisimple-only equivalence identifies actual derivations with the zero-cross-class, skew, representative-killing conditions. It retains every original hypothesis and is separate from the new arbitrary-Ann0 radical-quotient theorem.

**Definition 1.13 (The actual diagonal Lie map).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}\left(\right)), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (mu : \operatorname{LinearMap}\left(k, V, \operatorname{LinearMap}\left(k, V, V\right)\right)), (\forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] \forall (b : \operatorname{Module}.\operatorname{Basis}\left(I, k, V\right)), (\forall (alpha : \operatorname{Type}\left(\right)), (\forall (label : I \to alpha), (\forall (w : alpha \to V), (\forall (i : I), (\forall (j : I), (i \ne j \Rightarrow mu\left(b\left(i\right), b\left(j\right)\right) = 0)) \Rightarrow \left(\forall (i : I), (mu\left(b\left(i\right), b\left(i\right)\right) = w\left(label\left(i\right)\right)) \Rightarrow \left(\forall (a : alpha), (w\left(a\right) \ne 0) \Rightarrow \left(\forall (a : alpha), (\forall (c : alpha), (a \ne c \Rightarrow \forall (s : k), (\forall (t : k), (\operatorname{smul}\left(s, w\left(a\right)\right) + \operatorname{smul}\left(t, w\left(c\right)\right) = 0 \Rightarrow \left(s = 0 \land t = 0\right))))) \Rightarrow \left(\operatorname{Normalized}.\operatorname{diagonalHom}\left(mu, b, label, w\right) : \operatorname{LieHom}\left(k, \operatorname{derivations}\left(mu\right), I \to k\right) \land \forall (D : \operatorname{derivations}\left(mu\right)), (\forall (i : I), (\operatorname{Normalized}.\operatorname{diagonalHom}\left(mu, b, label, w\right)\left(D, i\right) = \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(b\right)\left(D\left(b\left(i\right)\right), i\right)))\right)\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.diagonalHom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map sends an actual derivation to its natural-basis diagonal coefficients. Its target has the scalar commutator, which is zero. The proved zero diagonal of brackets verifies the Lie-map law without a semisimplicity hypothesis.

**Theorem 1.14 (Standard-form skew adjoints in coordinates).**

$$\forall (k : \operatorname{Type}\left(\right)), ([\operatorname{Field}\left(k\right)] \forall (I : \operatorname{Type}\left(\right)), ([\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall (D : \operatorname{Module}.\operatorname{End}\left(k, I \to k\right)), (\operatorname{LinearMap}.\operatorname{BilinForm}.\operatorname{IsSkewAdjoint}\left(\operatorname{Matrix}\left(\right).\operatorname{toLinearMap}\left(\right)_{2}'\left(k, 1 : \operatorname{Matrix}\left(I, I, k\right)\right), D\right) \Leftrightarrow \forall (i : I), (\forall (j : I), (D\left(\operatorname{Pi}.\operatorname{single}\left(i, 1\right), j\right) = -D\left(\operatorname{Pi}.\operatorname{single}\left(j, 1\right), i\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.skew_iff_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual standard symmetric form on a finite coordinate space, an endomorphism is skew adjoint exactly when its basis coefficients are skew. The proof checks the bilinear identity on the canonical coordinate basis; it is reused unchanged by the block constructions.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_bracket_diagonal_zero`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_cross_zero`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_diagonal_eq_on_class`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_of_skew_killing`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.derivation_off_diagonal_skew`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.diagonalHom`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.mul_basis_left`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.mul_basis_right`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.properties_of_diagonal_zero`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.semisimple_diagonal_zero`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.semisimple_normalized_derivation_iff`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.separate_of_distinct_lines`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.skew_iff_coefficients`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/NaturalBasisDerivationEquations.square_equation`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction](DerivationAnnihilatorObstruction.md)
- Dependency: [D5/S3/QuadraticForms/OrthogonalPointwiseStabilizers](../OrthogonalPointwiseStabilizers.md)
