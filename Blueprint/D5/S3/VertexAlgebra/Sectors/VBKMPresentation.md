# VBKMPresentation

## Abstract

Virasoro and Borcherds presentation, action, and ideal structure.

**Definition 1.1 (EnhancedCartanData).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \operatorname{EnhancedCartanData} I J H V = \{\operatorname{pairing} : H \to_{l} [\mathbb{C} ] V \to_{l} [\mathbb{C} ] \mathbb{C} , \operatorname{coroot} : I \to H, \operatorname{root} : I \to V, \operatorname{degree} : J \to H, \operatorname{central} : J \to H, \operatorname{virRoot} : J \to V\}$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.EnhancedCartanData` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The two sets index ordinary and Virasoro roots; the two vector spaces carry coroots and roots, paired bilinearly.

**Definition 1.2 (matrix).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (i k : I), (\operatorname{matrix} F i k : \mathbb{C} ) = (\operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{coroot} i) (\operatorname{F}.\operatorname{root} k))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.matrix` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies matrix.

**Definition 1.3 (PositiveReal).**

$$\forall (z : \mathbb{C} ), (\operatorname{PositiveReal} z : \operatorname{Prop}) = (\exists r : \mathbb{R} , 0 < r \land z = (r : \mathbb{C} ))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.PositiveReal` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies PositiveReal.

**Definition 1.4 (NonpositiveInteger).**

$$\forall (z : \mathbb{C} ), (\operatorname{NonpositiveInteger} z : \operatorname{Prop}) = (\exists k : \mathbb{Z} , k \leq 0 \land z = (k : \mathbb{C} ))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.NonpositiveInteger` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies NonpositiveInteger.

**Definition 1.5 (FiniteDecompositions).**

$$\forall (A V : \operatorname{Type}), [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (r : A \to V), (\operatorname{FiniteDecompositions} r : \operatorname{Prop}) = (\forall v : V, \operatorname{Set}.\operatorname{Finite} \{m : A \to_{0} \mathbb{N} | (\operatorname{m}.\operatorname{sum} \operatorname{fun} a n \mapsto (n : \mathbb{C} ) \cdot r a) = v\})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.FiniteDecompositions` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies FiniteDecompositions.

**Definition 1.6 (simpleRoot).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \operatorname{simpleRoot} F = (\operatorname{fun} z \mapsto \operatorname{match} z \operatorname{with} | \operatorname{Sum}.\operatorname{inl} i \mapsto \operatorname{F}.\operatorname{root} i | \operatorname{Sum}.\operatorname{inr} (j,n) \mapsto (val\left(n\right) : \mathbb{C} ) \cdot \operatorname{F}.\operatorname{virRoot} j)$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.simpleRoot` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies simpleRoot.

**Definition 1.7 (GeneralizedCartan).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{GeneralizedCartan} F : \operatorname{Prop}) = (\operatorname{Submodule}.\operatorname{span} \mathbb{C} (\operatorname{Set}.\operatorname{range} \operatorname{F}.\operatorname{coroot}) = \operatorname{Top}.\operatorname{top} \land (\forall i k : I, i \neq k \to \operatorname{PositiveReal} (\operatorname{F}.\operatorname{matrix} i i) \to \operatorname{NonpositiveInteger} (2 * \operatorname{F}.\operatorname{matrix} i k / \operatorname{F}.\operatorname{matrix} i i)) \land (\forall i k : I, \operatorname{F}.\operatorname{matrix} i k = 0 \iff \operatorname{F}.\operatorname{matrix} k i = 0) \land \operatorname{FiniteDecompositions} \operatorname{F}.\operatorname{root})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.GeneralizedCartan` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

Definition 2.1, pages 4–5: “We call the entire choice (h,h∨,I,αᵢ,hᵢ) a generalized Cartan datum if A is a generalized Cartan matrix and for any α∈h∨, the number of ways to write” α as a nonnegative integral sum of simple roots “is finite.” Finite-support multiplicities count decompositions without ordering repeated summands. The positive-real integrality clause concerns distinct roots.

**Definition 1.8 (IsEnhanced).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{IsEnhanced} F : \operatorname{Prop}) = (\operatorname{F}.\operatorname{GeneralizedCartan} \land (\forall j : J, \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} j) (\operatorname{F}.\operatorname{virRoot} j) = 0 \land \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{degree} j) (\operatorname{F}.\operatorname{virRoot} j) = -1) \land (\forall (i : I) (j : J), \operatorname{PositiveReal} (\operatorname{F}.\operatorname{matrix} i i) \to \operatorname{NonpositiveInteger} (\operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{coroot} i) (\operatorname{F}.\operatorname{virRoot} j))) \land \operatorname{FiniteDecompositions} \operatorname{F}.\operatorname{simpleRoot} \land (\forall (i : I) (j : J), \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} j) (\operatorname{F}.\operatorname{root} i) = 0 \iff \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{coroot} i) (\operatorname{F}.\operatorname{virRoot} j) = 0) \land (\forall j k : J, \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} j) (\operatorname{F}.\operatorname{virRoot} k) = 0 \iff \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} k) (\operatorname{F}.\operatorname{virRoot} j) = 0) \land (\forall (i : I) (j : J), \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} j) (\operatorname{F}.\operatorname{root} i) = 0 \to \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{degree} j) (\operatorname{F}.\operatorname{root} i) = 0) \land (\forall j k : J, k \neq j \to \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} j) (\operatorname{F}.\operatorname{virRoot} k) = 0 \to \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{degree} j) (\operatorname{F}.\operatorname{virRoot} k) = 0))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.IsEnhanced` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

Definition 3.1, page 7: “Fix sets I and J, possibly empty. An enhanced generalized Cartan datum is a tuple (h,h∨,I,J,αᵢ,hᵢ,γⱼ,cⱼ,bⱼ) such that” the generalized Cartan condition and the displayed eight clauses hold. The pairing evaluates roots on coroots. Positive mode roots use n > 0; the zero mode is Cartan.

**Definition 1.9 (Symmetrizable).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{Symmetrizable} F : \operatorname{Prop}) = (\exists (T : H \equiv_{l} [\mathbb{C} ] H) (a : I \to \mathbb{C} ) (b c : J \to \mathbb{C} ), (\forall i : I, a i \neq 0 \land T (\operatorname{F}.\operatorname{coroot} i) = a i \cdot \operatorname{F}.\operatorname{coroot} i) \land (\forall j : J, b j \neq 0 \land T (\operatorname{F}.\operatorname{degree} j) = b j \cdot \operatorname{F}.\operatorname{degree} j) \land (\forall j : J, c j \neq 0 \land T (\operatorname{F}.\operatorname{central} j) = c j \cdot \operatorname{F}.\operatorname{central} j) \land (\forall i k : I, \operatorname{F}.\operatorname{pairing} (T (\operatorname{F}.\operatorname{coroot} i)) (\operatorname{F}.\operatorname{root} k) = \operatorname{F}.\operatorname{pairing} (T (\operatorname{F}.\operatorname{coroot} k)) (\operatorname{F}.\operatorname{root} i)) \land (\forall (i : I) (j : J), \operatorname{F}.\operatorname{pairing} (T (\operatorname{F}.\operatorname{central} j)) (\operatorname{F}.\operatorname{root} i) = \operatorname{F}.\operatorname{pairing} (T (\operatorname{F}.\operatorname{coroot} i)) (\operatorname{F}.\operatorname{virRoot} j)) \land (\forall j k : J, \operatorname{F}.\operatorname{pairing} (T (\operatorname{F}.\operatorname{central} j)) (\operatorname{F}.\operatorname{virRoot} k) = \operatorname{F}.\operatorname{pairing} (T (\operatorname{F}.\operatorname{central} k)) (\operatorname{F}.\operatorname{virRoot} j)))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.Symmetrizable` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

Definition 4.1, page 13: “We call an enhanced generalized Cartan datum F=(h,h∨,I,J,αᵢ,hᵢ,γⱼ,cⱼ,bⱼ) symmetrizable if there exists an automorphism of h acting on elements hᵢ,cⱼ,bⱼ by rescaling (by possibly distinct constants) such that” the ordinary Cartan matrix becomes symmetric and the two displayed cross-pairings agree.

**Definition 1.10 (Condition43).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{Condition43} F : \operatorname{Prop}) = ((\forall (i : I) (j : J), \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} j) (\operatorname{F}.\operatorname{root} i) = 0 \iff \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{degree} j) (\operatorname{F}.\operatorname{root} i) = 0) \land (\forall j k : J, k \neq j \to (\operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} j) (\operatorname{F}.\operatorname{virRoot} k) = 0 \iff \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{degree} j) (\operatorname{F}.\operatorname{virRoot} k) = 0)))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.Condition43` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

Equation (4.3), page 18: “α(cⱼ)=0 if and only if α(bⱼ)=0 for any α∈{αᵢ,γₖ:i∈I,k∈J∖j}.” The first clause ranges over ordinary roots and the second over distinct Virasoro indices.

**Definition 1.11 (deform).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (s t : \mathbb{C} ), (\operatorname{deform} F s t : \operatorname{EnhancedCartanData} I J H V) = (\{F \operatorname{with} \operatorname{degree} := \operatorname{fun} j \mapsto \operatorname{F}.\operatorname{degree} j + ((1 / 2 : \mathbb{C} ) * (t / s)^{2}) \cdot \operatorname{F}.\operatorname{central} j \})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.deform` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies deform.

**Definition 1.12 (heisenberg).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \operatorname{heisenberg} F = \{\operatorname{pairing} := \operatorname{F}.\operatorname{pairing}, \operatorname{coroot} := \operatorname{fun} z \mapsto \operatorname{match} z \operatorname{with} | \operatorname{Sum}.\operatorname{inl} i \mapsto \operatorname{F}.\operatorname{coroot} i | \operatorname{Sum}.\operatorname{inr} (j,n) \mapsto (val\left(n\right) : \mathbb{C} ) \cdot \operatorname{F}.\operatorname{central} j, \operatorname{root} := \operatorname{F}.\operatorname{simpleRoot}, \operatorname{degree} := \operatorname{PEmpty}.\operatorname{elim}, \operatorname{central} := \operatorname{PEmpty}.\operatorname{elim}, \operatorname{virRoot} := \operatorname{PEmpty}.\operatorname{elim} \}$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.heisenberg` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies heisenberg.

**Definition 1.13 (h).**

$$\forall (I J H : \operatorname{Type}), \forall (z : H), (h z : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))) = (\operatorname{FreeLieAlgebra}.\operatorname{of} \mathbb{C} (\operatorname{Sum}.\operatorname{inl} z))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.h` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies h.

**Definition 1.14 (e).**

$$\forall (I J H : \operatorname{Type}), \forall (i : I), (e i : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))) = (\operatorname{FreeLieAlgebra}.\operatorname{of} \mathbb{C} (\operatorname{Sum}.\operatorname{inr} (\operatorname{Sum}.\operatorname{inl} i)))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.e` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies e.

**Definition 1.15 (f).**

$$\forall (I J H : \operatorname{Type}), \forall (i : I), (f i : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))) = (\operatorname{FreeLieAlgebra}.\operatorname{of} \mathbb{C} (\operatorname{Sum}.\operatorname{inr} (\operatorname{Sum}.\operatorname{inr} (\operatorname{Sum}.\operatorname{inl} i))))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.f` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies f.

**Definition 1.16 (L).**

$$\forall (I J H : \operatorname{Type}), \forall (j : J), \forall (n : \mathbb{Z} ), (L j n : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))) = (\operatorname{FreeLieAlgebra}.\operatorname{of} \mathbb{C} (\operatorname{Sum}.\operatorname{inr} (\operatorname{Sum}.\operatorname{inr} (\operatorname{Sum}.\operatorname{inr} (j, n)))))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.L` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies L.

**Definition 1.17 (presentationRelations).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{presentationRelations} F : \operatorname{Set} ((\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} ))))))) = (\{z | (\exists a b : H, z = h (a + b) - h a - h b) \lor (\exists (a : H) (c : \mathbb{C} ), z = h (c \cdot a) - c \cdot h a) \lor (\exists a b : H, z = [ (h a : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))), h b] ) \lor (\exists (a : H) (i : I), z = [ (h a : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))), e i] - \operatorname{F}.\operatorname{pairing} a (\operatorname{F}.\operatorname{root} i) \cdot e i) \lor (\exists (a : H) (i : I), z = [ (h a : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))), f i] + \operatorname{F}.\operatorname{pairing} a (\operatorname{F}.\operatorname{root} i) \cdot f i) \lor (\exists i k : I, z = [ (e i : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))), f k] - (\operatorname{if} i = k \operatorname{then} h (\operatorname{F}.\operatorname{coroot} i) \operatorname{else} 0)) \lor (\exists (a : H) (j : J) (n : \mathbb{Z} ), z = [ (h a : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))), L j n] - ((n : \mathbb{C} ) * \operatorname{F}.\operatorname{pairing} a (\operatorname{F}.\operatorname{virRoot} j)) \cdot L j n) \lor (\exists (j : J) (n m : \mathbb{Z} ), z = [ (L j n : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))), L j m] - ((n - m : \mathbb{Z} ) : \mathbb{C} ) \cdot L j (n + m) - (\operatorname{if} n = -m \operatorname{then} ((n^{3} - n : \mathbb{Z} ) : \mathbb{C} ) \cdot h (\operatorname{F}.\operatorname{central} j) \operatorname{else} 0)) \lor (\exists j : J, z = L j 0 - h (\operatorname{F}.\operatorname{degree} j)) \lor (\exists (j k : J) (n m : \mathbb{Z} ), j \neq k \land n * m < 0 \land z = [ (L j n : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))), L k m] ) \lor (\exists (i : I) (j : J) (n : \mathbb{Z} ), n < 0 \land z = [ (e i : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))), L j n] ) \lor (\exists (i : I) (j : J) (n : \mathbb{Z} ), 0 < n \land z = [ (f i : (\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))), L j n] )\})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.presentationRelations` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies presentationRelations.

**Definition 1.18 (presentationIdeal).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{presentationIdeal} F : \operatorname{LieIdeal} \mathbb{C} ((\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} ))))))) = (\operatorname{LieSubmodule}.\operatorname{lieSpan} \mathbb{C} ((\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))))) (\operatorname{presentationRelations} F))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.presentationIdeal` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies presentationIdeal.

**Definition 1.19 (Presented).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \operatorname{Presented} F = ((\operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} ))))) / \operatorname{presentationIdeal} F)$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.Presented` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies Presented.

**Definition 1.20 (ph).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (a : H), (\operatorname{ph} F a : \operatorname{Presented} F) = (\operatorname{Submodule}.\operatorname{Quotient}.\operatorname{mk} (h a))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies ph.

**Definition 1.21 (pe).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (i : I), (\operatorname{pe} F i : \operatorname{Presented} F) = (\operatorname{Submodule}.\operatorname{Quotient}.\operatorname{mk} (e i))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pe` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies pe.

**Definition 1.22 (pf).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (i : I), (\operatorname{pf} F i : \operatorname{Presented} F) = (\operatorname{Submodule}.\operatorname{Quotient}.\operatorname{mk} (f i))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pf` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies pf.

**Definition 1.23 (pL).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (j : J), \forall (n : \mathbb{Z} ), (\operatorname{pL} F j n : \operatorname{Presented} F) = (\operatorname{Submodule}.\operatorname{Quotient}.\operatorname{mk} (L j n))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pL` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies pL.

**Definition 1.24 (cyclic).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (S : \operatorname{Set} A), \forall (w : A), (\operatorname{cyclic} S w : \operatorname{Submodule} \mathbb{C} A) = ((\operatorname{LieSubmodule}.\operatorname{lieSpan} \mathbb{C} (\operatorname{LieSubalgebra}.\operatorname{lieSpan} \mathbb{C} A S) (\{w\} : \operatorname{Set} A)).\operatorname{toSubmodule})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.cyclic` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies cyclic.

**Definition 1.25 (HighestProper).**

$$\forall (A : \operatorname{Type}), [\operatorname{LieRing} A], [\operatorname{LieAlgebra} \mathbb{C} A], \forall (S T D : \operatorname{Set} A), \forall (w x : A), (\operatorname{HighestProper} S T D w x : \operatorname{Prop}) = (x \neq 0 \land x \in \operatorname{cyclic} S w \land (\forall y \in T, [ y, x] = 0) \land (\forall y \in D, \exists a : \mathbb{C} , [ y, x] = a \cdot x) \land \operatorname{cyclic} S x < \operatorname{cyclic} S w)$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.HighestProper` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

A nonzero vector belongs to the cyclic submodule, is killed by the opposite generators, is a Cartan eigenvector, and generates a strictly smaller cyclic submodule.

**Definition 1.26 (rankOne).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (i : I), (\operatorname{rankOne} F i : \operatorname{Set} (\operatorname{Presented} F)) = (\{\operatorname{pe} F i, \operatorname{pf} F i, \operatorname{ph} F (\operatorname{F}.\operatorname{coroot} i)\})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.rankOne` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

Section 3.2, page 8: “For i∈I, let gᵢ be the algebra generated by eᵢ,hᵢ,fᵢ with the imposed relations (hence isomorphic to sl₂ or Heisenberg), and for j∈J, let Virʲ be the Virasoro algebra generated by Lʲₙ and cⱼ.” The displayed set gives the ordinary generators before taking their Lie span.

**Definition 1.27 (virasoro).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (j : J), (\operatorname{virasoro} F j : \operatorname{Set} (\operatorname{Presented} F)) = (\operatorname{Set}.\operatorname{range} (\operatorname{pL} F j) \cup \{\operatorname{ph} F (\operatorname{F}.\operatorname{central} j)\})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.virasoro` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

Section 3.2, page 8: “For i∈I, let gᵢ be the algebra generated by eᵢ,hᵢ,fᵢ with the imposed relations (hence isomorphic to sl₂ or Heisenberg), and for j∈J, let Virʲ be the Virasoro algebra generated by Lʲₙ and cⱼ.” The displayed set contains every integer mode and the central image.

**Definition 1.28 (sideSeed).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (\operatorname{side} : \operatorname{Bool}), \forall (i : I), (\operatorname{sideSeed} F \operatorname{side} i : \operatorname{Presented} F) = (\operatorname{if} \operatorname{side} \operatorname{then} \operatorname{pe} F i \operatorname{else} \operatorname{pf} F i)$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.sideSeed` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies sideSeed.

**Definition 1.29 (modeSign).**

$$\forall (\operatorname{side} : \operatorname{Bool}), (\operatorname{modeSign} \operatorname{side} : \mathbb{Z} ) = (\operatorname{if} \operatorname{side} \operatorname{then} 1 \operatorname{else} -1)$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.modeSign` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies modeSign.

**Definition 1.30 (localRelations).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{localRelations} F : \operatorname{Set} (\operatorname{Presented} F)) = (\{x | \exists \operatorname{side} : \operatorname{Bool}, (\exists i k : I, i \neq k \land \operatorname{HighestProper} (\operatorname{rankOne} F i) \{\operatorname{sideSeed} F (!\operatorname{side}) i\} \{\operatorname{ph} F (\operatorname{F}.\operatorname{coroot} i)\} (\operatorname{sideSeed} F \operatorname{side} k) x) \lor (\exists (i : I) (j : J) (n : \mathbb{Z} ), 0 < n \land \operatorname{HighestProper} (\operatorname{rankOne} F i) \{\operatorname{sideSeed} F (!\operatorname{side}) i\} \{\operatorname{ph} F (\operatorname{F}.\operatorname{coroot} i)\} (\operatorname{pL} F j (\operatorname{modeSign} \operatorname{side} * n)) x) \lor (\exists (i : I) (j : J), \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} j) (\operatorname{F}.\operatorname{root} i) = 0 \land \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{degree} j) (\operatorname{F}.\operatorname{root} i) = 0 \land (\operatorname{HighestProper} (\operatorname{virasoro} F j) \{y | \exists n : \mathbb{Z} , 0 < n \land y = \operatorname{pL} F j (-\operatorname{modeSign} \operatorname{side} * n)\} \{\operatorname{ph} F (\operatorname{F}.\operatorname{degree} j), \operatorname{ph} F (\operatorname{F}.\operatorname{central} j)\} (\operatorname{sideSeed} F \operatorname{side} i) x \lor \exists m : \mathbb{Z} , 0 < m \land x = [ \operatorname{pL} F j (\operatorname{modeSign} \operatorname{side} * m), \operatorname{sideSeed} F \operatorname{side} i] )) \lor (\exists (j k : J) (n : \mathbb{Z} ), j \neq k \land 0 < n \land \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{central} j) (\operatorname{F}.\operatorname{virRoot} k) = 0 \land \operatorname{F}.\operatorname{pairing} (\operatorname{F}.\operatorname{degree} j) (\operatorname{F}.\operatorname{virRoot} k) = 0 \land (\operatorname{HighestProper} (\operatorname{virasoro} F j) \{y | \exists m : \mathbb{Z} , 0 < m \land y = \operatorname{pL} F j (-\operatorname{modeSign} \operatorname{side} * m)\} \{\operatorname{ph} F (\operatorname{F}.\operatorname{degree} j), \operatorname{ph} F (\operatorname{F}.\operatorname{central} j)\} (\operatorname{pL} F k (\operatorname{modeSign} \operatorname{side} * n)) x \lor \exists m : \mathbb{Z} , 0 < m \land x = [ \operatorname{pL} F j (\operatorname{modeSign} \operatorname{side} * m), \operatorname{pL} F k (\operatorname{modeSign} \operatorname{side} * n)] ))\})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.localRelations` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

Section 3.3, page 10: “Let X₋ be the set containing” “all highest weight vectors generating all these proper submodules in ñ₋,” and “All Lʲₘ.fᵢ and Lʲₘ.Lᵏₙ for m<0 in cases (iii)−(iv).” “Define X₊⊂ñ₊ in a similar way (so that X₊=ω(X₋)).” The four alternatives describe the two ordinary rank-one actions and the two Virasoro actions with both cross-pairings zero; both signs are included.

**Definition 1.31 (localIdeal).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{localIdeal} F : \operatorname{LieIdeal} \mathbb{C} (\operatorname{Presented} F)) = (\operatorname{LieSubmodule}.\operatorname{lieSpan} \mathbb{C} (\operatorname{Presented} F) (\operatorname{localRelations} F))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.localIdeal` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies localIdeal.

**Definition 1.32 (VBKM).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \operatorname{VBKM} F = (\operatorname{Presented} F / \operatorname{localIdeal} F)$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.VBKM` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

Section 3.3, page 12: “We define g=g(F):=g̃/Ĩ and call it the Virasoro-Borcherds-Kac-Moody algebra associated to F.” The second quotient divides the presented algebra by the ideal generated by all local relations.

**Definition 1.33 (cartanSubspace).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{cartanSubspace} F : \operatorname{Submodule} \mathbb{C} (\operatorname{VBKM} F)) = (\operatorname{Submodule}.\operatorname{span} \mathbb{C} (\operatorname{Set}.\operatorname{range} (\operatorname{fun} a : H \mapsto (\operatorname{Submodule}.\operatorname{Quotient}.\operatorname{mk} (\operatorname{ph} F a) : \operatorname{VBKM} F))))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.cartanSubspace` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies cartanSubspace.

**Definition 1.34 (IdealRigidity).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), (\operatorname{IdealRigidity} F : \operatorname{Prop}) = (\forall K : \operatorname{LieIdeal} \mathbb{C} (\operatorname{VBKM} F), \operatorname{inf} \operatorname{K}.\operatorname{toSubmodule} (\operatorname{cartanSubspace} F) = \perp \to K = \perp )$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.IdealRigidity` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies IdealRigidity.

**Definition 1.35 (claim).**

$$\operatorname{claim} \iff \forall (I J H V : \operatorname{Type}) [\operatorname{AddCommGroup} H] [\operatorname{Module} \mathbb{C} H] [\operatorname{AddCommGroup} V] [\operatorname{Module} \mathbb{C} V] (F : \operatorname{EnhancedCartanData} I J H V), \operatorname{F}.\operatorname{IsEnhanced} \to \operatorname{F}.\operatorname{Symmetrizable} \to \forall s t : \mathbb{C} , (s \neq 0 \lor t \neq 0) \to (\operatorname{if} s = 0 \operatorname{then} (\operatorname{F}.\operatorname{heisenberg}).\operatorname{IdealRigidity} \operatorname{else} (\operatorname{F}.\operatorname{deform} s t).\operatorname{Condition43} \to (\operatorname{F}.\operatorname{deform} s t).\operatorname{IdealRigidity})$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.claim` (`✓ std3`).

*Citation.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

Conjecture 4.8, page 18 of arXiv:2609.15729v2: “The statement of Theorem 4.5 holds for any x ∈ P¹ for which the corresponding VBKM algebra satisfies (4.3). In other words, the VBKM algebra g̃(Fₓ) contains no ideals not intersecting h.” Nonzero homogeneous pairs (s,t) represent P¹; the s=0 fiber is the BKM presentation and the other fibers use the stated deformation.

**Definition 1.36 (datum).**

$$(\forall (a v : \mathbb{C} \times \mathbb{C} ), \operatorname{datum}.\operatorname{pairing} a v = a.1 * v.1 + a.2 * v.2) \land (\forall (i : \operatorname{Bool}), \operatorname{datum}.\operatorname{coroot} i = (\operatorname{if} i \operatorname{then} (1,0) \operatorname{else} (0,1)) \land \operatorname{datum}.\operatorname{root} i = (\operatorname{if} i \operatorname{then} (-4/3,-1) \operatorname{else} (-1,-2/3))) \land (\forall (j : \operatorname{Unit}), \operatorname{datum}.\operatorname{degree} j = (-81/8,105/8) \land \operatorname{datum}.\operatorname{central} j = (1,-1) \land \operatorname{datum}.\operatorname{virRoot} j = (-1/3,-1/3))$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.datum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The rank-two datum has two imaginary ordinary roots and one Virasoro root; its degree, central element and bilinear pairing have the displayed rational coordinates.

**Theorem 1.37 (datum symmetrizable).**

$$\operatorname{datum}.\operatorname{Symmetrizable}$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.datum_symmetrizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies datum symmetrizable.

**Theorem 1.38 (datum condition43).**

$$\operatorname{datum}.\operatorname{Condition43}$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.datum_condition43` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies datum condition43.

**Theorem 1.39 (datum enhanced).**

$$\operatorname{datum}.\operatorname{IsEnhanced}$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.datum_enhanced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies datum enhanced.

**Definition 1.40 (presentationMap).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V) (z : \operatorname{FreeLieAlgebra} \mathbb{C} (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} ))))), \operatorname{presentationMap} F z = (\operatorname{presentationIdeal} F).\operatorname{toSubmodule}.\operatorname{mkQ} z$$

*Formalization.* `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.presentationMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed construction specifies presentationMap.

**Theorem 1.41 (ph commute).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (a b : H), [ \operatorname{ph} F a,\operatorname{ph} F b] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies ph commute.

**Theorem 1.42 (ph pe).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (a : H), \forall (i : I), [ \operatorname{ph} F a,\operatorname{pe} F i] = \operatorname{F}.\operatorname{pairing} a (\operatorname{F}.\operatorname{root} i) \cdot \operatorname{pe} F i$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph_pe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies ph pe.

**Theorem 1.43 (ph pf).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (a : H), \forall (i : I), [ \operatorname{ph} F a,\operatorname{pf} F i] = -(\operatorname{F}.\operatorname{pairing} a (\operatorname{F}.\operatorname{root} i) \cdot \operatorname{pf} F i)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph_pf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies ph pf.

**Theorem 1.44 (pe pf).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (i k : I), [ \operatorname{pe} F i,\operatorname{pf} F k] = \operatorname{if} i=k \operatorname{then} \operatorname{ph} F (\operatorname{F}.\operatorname{coroot} i) \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pe_pf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies pe pf.

**Theorem 1.45 (ph pL).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (a : H), \forall (j : J), \forall (n : \mathbb{Z} ), [ \operatorname{ph} F a,\operatorname{pL} F j n] = ((n : \mathbb{C} ) * \operatorname{F}.\operatorname{pairing} a (\operatorname{F}.\operatorname{virRoot} j)) \cdot \operatorname{pL} F j n$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph_pL` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies ph pL.

**Theorem 1.46 (pL commute).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (j : J), \forall (n m : \mathbb{Z} ), [ \operatorname{pL} F j n,\operatorname{pL} F j m] = ((n-m : \mathbb{Z} ) : \mathbb{C} ) \cdot \operatorname{pL} F j (n+m) + \operatorname{if} n = -m \operatorname{then} ((n^{3}-n : \mathbb{Z} ) : \mathbb{C} ) \cdot \operatorname{ph} F (\operatorname{F}.\operatorname{central} j) \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pL_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies pL commute.

**Theorem 1.47 (pL zero).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (j : J), \operatorname{pL} F j 0 = \operatorname{ph} F (\operatorname{F}.\operatorname{degree} j)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pL_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies pL zero.

**Theorem 1.48 (pe negative).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (i : I), \forall (j : J), \forall (n : \mathbb{Z} ), (n < 0) \to [ \operatorname{pe} F i,\operatorname{pL} F j n] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pe_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies pe negative.

**Theorem 1.49 (pf positive).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (i : I), \forall (j : J), \forall (n : \mathbb{Z} ), (0 < n) \to [ \operatorname{pf} F i,\operatorname{pL} F j n] = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pf_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies pf positive.

**Theorem 1.50 (presentation generates).**

$$\forall (I J H V : \operatorname{Type}), [\operatorname{AddCommGroup} H], [\operatorname{Module} \mathbb{C} H], [\operatorname{AddCommGroup} V], [\operatorname{Module} \mathbb{C} V], \forall (F : \operatorname{EnhancedCartanData} I J H V), \forall (G : \operatorname{Set} (\operatorname{Presented} F)), (\forall g : (\operatorname{Sum} H (\operatorname{Sum} I (\operatorname{Sum} I (J \times \mathbb{Z} )))), \operatorname{presentationMap} F (\operatorname{FreeLieAlgebra}.\operatorname{of} \mathbb{C} g) \in \operatorname{LieSubalgebra}.\operatorname{lieSpan} \mathbb{C} (\operatorname{Presented} F) G) \to \operatorname{LieSubalgebra}.\operatorname{lieSpan} \mathbb{C} (\operatorname{Presented} F) G = \operatorname{Top}.\operatorname{top} $$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.presentation_generates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vladyslav Zveryk (2026). *Virasoro extensions of generalized Kac-Moody algebras*. DOI: [10.48550/arXiv.2609.15729](https://doi.org/10.48550/arXiv.2609.15729). URL: <https://arxiv.org/abs/2609.15729v2>.

*Commentary.*

The displayed identity specifies presentation generates.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.Condition43`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.EnhancedCartanData`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.FiniteDecompositions`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.GeneralizedCartan`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.HighestProper`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.IdealRigidity`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.IsEnhanced`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.L`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.NonpositiveInteger`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.PositiveReal`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.Presented`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.Symmetrizable`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.VBKM`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.cartanSubspace`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.claim`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.cyclic`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.datum`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.datum_condition43`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.datum_enhanced`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.datum_symmetrizable`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.deform`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.e`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.f`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.h`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.heisenberg`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.localIdeal`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.localRelations`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.matrix`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.modeSign`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pL`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pL_commute`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pL_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pe`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pe_negative`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pe_pf`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pf`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.pf_positive`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph_commute`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph_pL`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph_pe`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.ph_pf`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.presentationIdeal`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.presentationMap`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.presentationRelations`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.presentation_generates`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.rankOne`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.sideSeed`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.simpleRoot`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/VBKMPresentation.virasoro`
