# FlatlandImageAlgebra

## Abstract

Two-camera image equations and their polynomial deformation argument.

**Definition 1.1 (ImagingDomain).**

$$\forall (n : \mathbb{N}) , ImagingDomain n = (\{s : (Fin n \to (Projectivization \mathbb{C} (Fin 4 \to \mathbb{C}))) \times (Fin 2 \to (Projectivization \mathbb{C} (Matrix (Fin 3) (Fin 4) \mathbb{C}))) // \forall j : Fin n , \forall i : Fin 2 , (s . 2 i) . rep *_{v} (s . 1 j) . rep \neq 0\})$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.ImagingDomain` (`✓ std3`).

*Citation.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Projective world points and two projective camera matrices whose products are all nonzero.

**Definition 1.2 (theta).**

$$\forall (n : \mathbb{N}) , \forall (s : ImagingDomain n) , (theta s : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C}))) = (fun j i \mapsto Projectivization . mk \mathbb{C} ((val\left(s\right) . 2 i) . rep *_{v} (val\left(s\right) . 1 j) . rep) (s . property j i))$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.theta` (`✓ std3`).

*Citation.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Definition 4.1, page 12: “For any $n$, $N$, and m• as above, we define the associated image variety (c.f. [2]) to be the closed image of the rational map”

The two camera images of each world point, as projective points. Here N = 3 and the two image planes have dimension two.

**Definition 1.3 (coordinates).**

$$\forall (n : \mathbb{N}) , \forall (p : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C}))) , (coordinates p : ((Fin n \times Fin 2) \times Fin 3) \to \mathbb{C}) = (fun k \mapsto (p k . 1 . 1 k . 1 . 2) . rep k . 2)$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.coordinates` (`✓ std3`).

*Citation.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

The representative coordinates of each projective image point.

**Definition 1.4 (Multihomogeneous).**

$$\forall (n : \mathbb{N}) , \forall (f : (MvPolynomial ((Fin n \times Fin 2) \times Fin 3) \mathbb{C})) , (Multihomogeneous f : Prop) = (\exists degree : Fin n \times Fin 2 \to \mathbb{N} , \forall b : Fin n \times Fin 2 , f . IsWeightedHomogeneous (fun k \mapsto if k . 1 = b then (1 : \mathbb{N}) else 0) (degree b))$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.Multihomogeneous` (`✓ std3`).

*Citation.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

A separate nonnegative homogeneous degree for each projective block.

**Definition 1.5 (imageClosure).**

$$\forall (n : \mathbb{N}) , (imageClosure n : Set ((Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C})))) = (\{p | \forall f : (MvPolynomial ((Fin n \times Fin 2) \times Fin 3) \mathbb{C}) , Multihomogeneous f \to (\forall s : ImagingDomain n , MvPolynomial . eval (coordinates (theta s)) f = 0) \to MvPolynomial . eval (coordinates p) f = 0\})$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.imageClosure` (`✓ std3`).

*Citation.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Definition 4.1, page 12: “For any $n$, $N$, and m• as above, we define the associated image variety (c.f. [2]) to be the closed image of the rational map”

The common zeros of all multihomogeneous polynomials vanishing on the rational image. Here N = 3 and the two image planes have dimension two.

**Definition 1.6 (segreMatrix).**

$$\forall (n : \mathbb{N}) , \forall (p : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C}))) , (segreMatrix p : Matrix (Fin n) (Fin 9) \mathbb{C}) = (fun j k \mapsto (p j 0) . rep ((finProdFinEquiv : Equiv (Fin 3 \times Fin 3) (Fin 9)) . symm k) . 1 * (p j 1) . rep ((finProdFinEquiv : Equiv (Fin 3 \times Fin 3) (Fin 9)) . symm k) . 2)$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.segreMatrix` (`✓ std3`).

*Citation.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Each row is the tensor product of the two image point representatives.

**Definition 1.7 (cofactorMatrix).**

$$\forall (n : \mathbb{N}) , \forall (p : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C}))) , \forall (I : Function . Embedding (Fin 8) (Fin n)) , (cofactorMatrix p I : Matrix (Fin 3) (Fin 3) \mathbb{C}) = (fun b a \mapsto (- 1 : \mathbb{C})^{val\left(finProdFinEquiv (a , b)\right)} * Matrix . det ((segreMatrix p) . submatrix I (finProdFinEquiv (a , b)) . succAbove))$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.cofactorMatrix` (`✓ std3`).

*Citation.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

The signed maximal minors of eight Segre rows, arranged by column vectorization.

**Definition 1.8 (equations).**

$$\forall (n : \mathbb{N}) , \forall (p : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C}))) , (equations p : Prop) = ((\forall J : Function . Embedding (Fin 9) (Fin n) , Matrix . det ((segreMatrix p) . submatrix J id) = 0) \land (\forall I : Function . Embedding (Fin 8) (Fin n) , Matrix . det (cofactorMatrix p I) = 0))$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.equations` (`✓ std3`).

*Citation.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

The nine-row Segre minors and the determinants obtained from every eight-row cofactor vector vanish.

**Definition 1.9 (canonicalA).**

$$\forall (K : Type) , \forall [Field K] , (canonicalA : Matrix (Fin 3) (Fin 4) K) = (! [! [1 , 0 , 0 , 0] , ! [0 , 1 , 0 , 0] , ! [0 , 0 , 1 , 0]])$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.canonicalA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

The first three coordinate projections on world space.

**Theorem 1.10 (singular_in_matrix_subspace).**

$$\forall (K m : Type) , \forall [Field K] , \forall [IsAlgClosed K] , \forall [Fintype m] , \forall [DecidableEq m] , \forall [Nonempty m] , \forall (W : Submodule K (Matrix m m K)) , \forall (U V : Matrix m m K) , (U \in W) \to (V \in W) \to (U \neq 0) \to (\forall a : K , V \neq a \cdot U) \to \exists F \in W , F \neq 0 \land F . det = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.singular_in_matrix_subspace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

A matrix subspace containing two independent matrices has a nonzero singular member over an algebraically closed field.

**Theorem 1.11 (homogeneous_substitution).**

$$\forall (R \sigma \tau : Type) , \forall [CommRing R] , \forall (w : \sigma \to \mathbb{N}) , \forall (v : \tau \to \mathbb{N}) , \forall (f : MvPolynomial \sigma R) , \forall (m : \mathbb{N}) , (f . IsWeightedHomogeneous w m) \to \forall (g : \sigma \to MvPolynomial \tau R) , (\forall i , (g i) . IsWeightedHomogeneous v (w i)) \to (MvPolynomial . eval_{2} MvPolynomial . C g f) . IsWeightedHomogeneous v m$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.homogeneous_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Substitution by forms of the required degrees preserves weighted homogeneity.

**Theorem 1.12 (homogeneous_determinant).**

$$\forall (R \sigma \iota : Type) , \forall [CommRing R] , \forall [Fintype \iota] , \forall [DecidableEq \iota] , \forall (w : \sigma \to \mathbb{N}) , \forall (M : Matrix \iota \iota (MvPolynomial \sigma R)) , \forall (d : \iota \to \mathbb{N}) , (\forall i j , (M i j) . IsWeightedHomogeneous w (d i)) \to M . det . IsWeightedHomogeneous w (\sum i , d i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.homogeneous_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

A determinant with fixed row degrees has their sum as its degree.

**Definition 1.13 (diagonalB).**

$$\forall (K : Type) , \forall [Field K] , \forall (c : K) , (diagonalB c : Matrix (Fin 3) (Fin 4) K) = (! [! [0 , 1 , 0 , 0] , ! [- c^{-1} , 0 , 0 , 0] , ! [0 , 0 , 1 , 1]])$$

*Formalization.* `D5/S3/Geometry/FlatlandImageAlgebra.diagonalB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

A second camera realizing a diagonal rank-two bilinear form.

**Theorem 1.14 (diagonal_rank_two_pair_curves).**

$$\forall (K : Type) , \forall [Field K] , \forall (c : K) , (c \neq 0) \to \forall (x y : Fin 3 \to K) , (x \neq 0) \to (y \neq 0) \to (x 0 * y 0 + c * x 1 * y 1 = 0) \to \exists Xc Yc : Fin 3 \to K [X] , (fun a \mapsto (Xc a) . eval 0) = x \land (fun a \mapsto (Yc a) . eval 0) = y \land (\forall t , (fun a \mapsto (Xc a) . eval t) \neq 0 \land (fun a \mapsto (Yc a) . eval t) \neq 0) \land (\forall t : K , t \neq 0 \to \exists q : Fin 4 \to K , \exists a b : K , a \neq 0 \land b \neq 0 \land canonicalA *_{v} q = a \cdot (fun k \mapsto (Xc k) . eval t) \land diagonalB c *_{v} q = b \cdot (fun k \mapsto (Yc k) . eval t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.diagonal_rank_two_pair_curves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Every compatible pair, including epipoles, is the specialization of polynomial curves reconstructed by these two cameras away from zero.

**Theorem 1.15 (eval_projective_representatives_zero_iff).**

$$\forall (B A : Type) , \forall [Fintype B] , \forall [Fintype A] , \forall [DecidableEq B] , \forall (f : MvPolynomial (B \times A) \mathbb{C}) , \forall (D : B \to \mathbb{N}) , (\forall b : B , f . IsWeightedHomogeneous (fun k : B \times A \mapsto if k . 1 = b then (1 : \mathbb{N}) else 0) (D b)) \to \forall (z : B \to A \to \mathbb{C}) , \forall (hz : \forall b , z b \neq 0) , MvPolynomial . eval (fun k \mapsto (Projectivization . mk \mathbb{C} (z k . 1) (hz k . 1)) . rep k . 2) f = 0 \iff MvPolynomial . eval (fun k \mapsto z k . 1 k . 2) f = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.eval_projective_representatives_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

A multihomogeneous zero is independent of the chosen projective representatives.

**Theorem 1.16 (imageClosure_polynomial_specialization).**

$$\forall (n : \mathbb{N}) , \forall (z : (Fin n \times Fin 2) \to Fin 3 \to Polynomial \mathbb{C}) , \forall (hz : \forall t b , (fun a \mapsto (z b a) . eval t) \neq 0) , (\forall t : \mathbb{C} , t \neq 0 \to (fun j i \mapsto Projectivization . mk \mathbb{C} (fun a \mapsto (z (j , i) a) . eval t) (hz t (j , i))) \in imageClosure n) \to (fun j i \mapsto Projectivization . mk \mathbb{C} (fun a \mapsto (z (j , i) a) . eval 0) (hz 0 (j , i))) \in imageClosure n$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.imageClosure_polynomial_specialization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

A nonzero polynomial curve in the closed image away from zero remains there at zero.

**Theorem 1.17 (raw_imaging_realization).**

$$\forall (n : \mathbb{N}) , \forall (A : Fin 2 \to Matrix (Fin 3) (Fin 4) \mathbb{C}) , \forall (q : Fin n \to Fin 4 \to \mathbb{C}) , (\forall i , A i \neq 0) \to (\forall j , q j \neq 0) \to \forall (hAq : \forall j i , A i *_{v} q j \neq 0) , \exists s : ImagingDomain n , theta s = fun j i \mapsto Projectivization . mk \mathbb{C} (A i *_{v} q j) (hAq j i)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.raw_imaging_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Nonzero raw camera products determine a point of the rational imaging domain.

**Theorem 1.18 (bilinear_projective_mk_zero_iff).**

$$\forall (F : Matrix (Fin 3) (Fin 3) \mathbb{C}) , \forall (x y : Fin 3 \to \mathbb{C}) , \forall (hx : x \neq 0) , \forall (hy : y \neq 0) , (Projectivization . mk \mathbb{C} y hy) . rep \cdot_{v} (F *_{v} (Projectivization . mk \mathbb{C} x hx) . rep) = 0 \iff y \cdot_{v} (F *_{v} x) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.bilinear_projective_mk_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

A bilinear zero is unchanged by passing to projective representatives.

**Theorem 1.19 (rank_one_closure_from_rank_two).**

$$\forall (n : \mathbb{N}) , (\forall (t : \mathbb{C}) , t \neq 0 \to \forall q : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C})) , (\forall j , (q j 0) . rep 0 * (q j 1) . rep 0 + t^{2} * (q j 0) . rep 1 * (q j 1) . rep 1 = 0) \to q \in imageClosure n) \to \forall (p : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C}))) , (\forall j , (p j 0) . rep 0 * (p j 1) . rep 0 = 0) \to p \in imageClosure n$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.rank_one_closure_from_rank_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Simultaneous polynomial deformation extends diagonal rank-two closure to the normalized rank-one case.

**Theorem 1.20 (kernel_nonzero_of_maximal_minors).**

$$\forall (K m : Type) , \forall [Field K] , \forall [Fintype m] , \forall (d : \mathbb{N}) , \forall (M : Matrix m (Fin d) K) , (\forall I : Function . Embedding (Fin d) m , (M . submatrix I id) . det = 0) \to \exists v : Fin d \to K , v \neq 0 \land M *_{v} v = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.kernel_nonzero_of_maximal_minors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Vanishing maximal row minors yield a nonzero right kernel vector.

**Theorem 1.21 (cofactor_in_full_kernel).**

$$\forall (K \iota : Type) , \forall [Field K] , \forall (d : \mathbb{N}) , \forall (M : Matrix \iota (Fin (d + 1)) K) , (\forall I : Function . Embedding (Fin (d + 1)) \iota , (M . submatrix I id) . det = 0) \to \forall (I : Function . Embedding (Fin d) \iota) , M *_{v} D5 . S3 . Arith . Lattices . CofactorKernel . cofactor (M . submatrix I id) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.cofactor_in_full_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

When all larger minors vanish, the cofactors of any selected rows lie in the full matrix kernel.

**Theorem 1.22 (kernel_eq_smul_cofactor).**

$$\forall (K : Type) , \forall [Field K] , \forall (d : \mathbb{N}) , \forall (A : Matrix (Fin d) (Fin (d + 1)) K) , (cofactor A \neq 0) \to \forall (x : Fin (d + 1) \to K) , (A *_{v} x = 0) \to \exists a : K , x = a \cdot cofactor A$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.kernel_eq_smul_cofactor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

A nonzero maximal cofactor vector spans the kernel.

**Theorem 1.23 (finite_row_basis).**

$$\forall (K \iota d : Type) , \forall [Field K] , \forall [Fintype \iota] , \forall [Fintype d] , \forall (M : Matrix \iota d K) , \exists I : Function . Embedding (Fin M . rank) \iota , Submodule . span K (Set . range (M . submatrix I id) . row) = Submodule . span K (Set . range M . row) \land LinearIndependent K (M . submatrix I id) . row$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.finite_row_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

A finite subset of the rows is a basis for their span.

**Theorem 1.24 (cofactor_nonzero_of_independent_rows).**

$$\forall (K : Type) , \forall [Field K] , \forall (d : \mathbb{N}) , \forall (A : Matrix (Fin d) (Fin (d + 1)) K) , (LinearIndependent K A . row) \to cofactor A \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageAlgebra.cofactor_nonzero_of_independent_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Independent rows have a nonzero maximal cofactor vector.

## References

- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.ImagingDomain`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.Multihomogeneous`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.bilinear_projective_mk_zero_iff`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.canonicalA`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.cofactorMatrix`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.cofactor_in_full_kernel`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.cofactor_nonzero_of_independent_rows`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.coordinates`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.diagonalB`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.diagonal_rank_two_pair_curves`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.equations`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.eval_projective_representatives_zero_iff`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.finite_row_basis`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.homogeneous_determinant`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.homogeneous_substitution`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.imageClosure`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.imageClosure_polynomial_specialization`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.kernel_eq_smul_cofactor`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.kernel_nonzero_of_maximal_minors`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.rank_one_closure_from_rank_two`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.raw_imaging_realization`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.segreMatrix`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.singular_in_matrix_subspace`
- Truth anchor: `D5/S3/Geometry/FlatlandImageAlgebra.theta`
- Dependency: [D5/S3/Arith/Lattices/CofactorKernel](../Arith/Lattices/CofactorKernel.md)
