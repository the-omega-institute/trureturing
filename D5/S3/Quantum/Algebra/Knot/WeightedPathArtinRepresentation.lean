/- GID: D5/S3/Quantum/Algebra/Knot/WeightedPathArtinRepresentation
   generality: G
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite Artin presentation acts by units on the weighted path block algebra. -/
import D5.S3.Quantum.Algebra.Knot.WeightedPathReverseTemperleyLieb
import D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality
import Mathlib.GroupTheory.PresentedGroup

set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace
open D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality
open D5.S3.Quantum.Algebra.Knot.WeightedPathReverseTemperleyLieb

attribute [local instance] Classical.propDecidable
variable {L : Type*} [Fintype L] [DecidableEq L]
local instance (R : L → L → Prop) (n : ℕ) (s t : L) : DecidableEq (LegalPath R n s t) :=
  Classical.decEq _

/-- The distant commutator in the free group on n - 1 Artin generators. -/
def distantWord (n : ℕ) (i j : Fin (n - 1)) : FreeGroup (Fin (n - 1)) :=
  FreeGroup.of i * FreeGroup.of j * (FreeGroup.of j * FreeGroup.of i)⁻¹

/-- The adjacent three-letter Artin relation as a free-group relator. -/
def adjacentWord (n : ℕ) (i j : Fin (n - 1)) : FreeGroup (Fin (n - 1)) :=
  (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i) *
    (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹

/-- Literal finite Artin presentation; no geometric braid identification is assumed. -/
def artinRelators (n : ℕ) : Set (FreeGroup (Fin (n - 1))) :=
  { r | (∃ i j, (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧ r = distantWord n i j) ∨
      (∃ i j, i.val + 1 = j.val ∧ r = adjacentWord n i j) }

/-- The n-strand Artin group defined by its actual group presentation. -/
abbrev Artin (n : ℕ) := PresentedGroup (artinRelators n)

private theorem generator_range (n : ℕ) (i : Fin (n - 1)) : 0 < i.val + 1 ∧ i.val + 1 < n := by
  have := i.is_lt
  omega

/-- The proposed braid generator on the full endpoint block algebra. -/
def rho (R : L → L → Prop) (d : L → ℝ) (δ : ℝ) (A : ℂ)
    (n : ℕ) (s : L) (i : Fin (n - 1)) : C R n s :=
  A⁻¹ • 1 + (A * (δ : ℂ)) •
    localProjection R d δ n s (i.val + 1) (generator_range n i)

/-- Its explicit inverse candidate, using the same literal projection. -/
def rhoInverse (R : L → L → Prop) (d : L → ℝ) (δ : ℝ) (A : ℂ)
    (n : ℕ) (s : L) (i : Fin (n - 1)) : C R n s :=
  A • 1 + (A⁻¹ * (δ : ℂ)) •
    localProjection R d δ n s (i.val + 1) (generator_range n i)

private theorem matrix_inverse {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℂ) (hP : P * P = P) (δ A : ℂ) (hA : A ≠ 0)
    (hparameter : δ = -A ^ 2 - A⁻¹ ^ 2) :
    (A⁻¹ • 1 + (A * δ) • P) * (A • 1 + (A⁻¹ * δ) • P) = 1 ∧
    (A • 1 + (A⁻¹ * δ) • P) * (A⁻¹ • 1 + (A * δ) • P) = 1 := by
  constructor <;>
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      one_mul, mul_one, hP, smul_smul] <;>
    ext x y <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] <;>
    rw [hparameter] <;> field_simp <;> ring

private theorem matrix_distant {X : Type*} [Fintype X] [DecidableEq X]
    (P Q : Matrix X X ℂ) (hPQ : P * Q = Q * P) (δ A : ℂ) :
    (A⁻¹ • 1 + (A * δ) • P) * (A⁻¹ • 1 + (A * δ) • Q) =
      (A⁻¹ • 1 + (A * δ) • Q) * (A⁻¹ • 1 + (A * δ) • P) := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, smul_smul, hPQ]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem matrix_adjacent {X : Type*} [Fintype X] [DecidableEq X]
    (P Q : Matrix X X ℂ) (hP : P * P = P) (hQ : Q * Q = Q)
    (δ A : ℂ) (hδ : δ ≠ 0) (hA : A ≠ 0)
    (hparameter : δ = -A ^ 2 - A⁻¹ ^ 2)
    (hPQP : P * Q * P = (δ⁻¹ ^ 2) • P) (hQPQ : Q * P * Q = (δ⁻¹ ^ 2) • Q) :
    (A⁻¹ • 1 + (A * δ) • P) * (A⁻¹ • 1 + (A * δ) • Q) *
        (A⁻¹ • 1 + (A * δ) • P) =
      (A⁻¹ • 1 + (A * δ) • Q) * (A⁻¹ • 1 + (A * δ) • P) *
        (A⁻¹ • 1 + (A * δ) • Q) := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, smul_smul, ← mul_assoc, hP, hQ, hPQP, hQPQ]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  -- Keep delta nonzero available before replacing it with the parameter polynomial.
  field_simp
  rw [hparameter]
  field_simp
  ring

private theorem rho_inverse
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (s : L) (i : Fin (n - 1)) :
    rho R d δ A n s i * rhoInverse R d δ A n s i = 1 ∧
      rhoInverse R d δ A n s i * rho R d δ A n s i = 1 := by
  have h (t : L) := matrix_inverse
    (pathProjection R d δ n s t (i.val + 1) (generator_range n i))
    ((weighted_legal_path_temperley_lieb R hR d hd δ hδ hPF n s t).1
      (i.val + 1) (generator_range n i)).2
    (δ : ℂ) A hA hparameter
  constructor
  · funext t
    exact (h t).1
  · funext t
    exact (h t).2

/-- Genuine units, with both inverse identities verified on every endpoint block. -/
def rhoUnit
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (s : L) (i : Fin (n - 1)) : (C R n s)ˣ where
  val := rho R d δ A n s i
  inv := rhoInverse R d δ A n s i
  val_inv := (rho_inverse R hR d hd δ hδ hPF A hA hparameter n s i).1
  inv_val := (rho_inverse R hR d hd δ hδ hPF A hA hparameter n s i).2

private theorem rhoUnit_distant
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (s : L) (i j : Fin (n - 1))
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    rhoUnit R hR d hd δ hδ hPF A hA hparameter n s i *
        rhoUnit R hR d hd δ hδ hPF A hA hparameter n s j =
      rhoUnit R hR d hd δ hδ hPF A hA hparameter n s j *
        rhoUnit R hR d hd δ hδ hPF A hA hparameter n s i := by
  apply Units.ext
  funext t
  exact matrix_distant _ _
    ((weighted_legal_path_temperley_lieb R hR d hd δ hδ hPF n s t).2.2
      (i.val + 1) (j.val + 1) (generator_range n i) (generator_range n j) (by omega))
    (δ : ℂ) A

private theorem rhoUnit_adjacent
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (s : L) (i j : Fin (n - 1)) (hij : i.val + 1 = j.val) :
    rhoUnit R hR d hd δ hδ hPF A hA hparameter n s i *
        rhoUnit R hR d hd δ hδ hPF A hA hparameter n s j *
        rhoUnit R hR d hd δ hδ hPF A hA hparameter n s i =
      rhoUnit R hR d hd δ hδ hPF A hA hparameter n s j *
        rhoUnit R hR d hd δ hδ hPF A hA hparameter n s i *
        rhoUnit R hR d hd δ hδ hPF A hA hparameter n s j := by
  apply Units.ext
  funext t
  have hp := weighted_legal_path_temperley_lieb R hR d hd δ hδ hPF n s t
  have hi : 0 < i.val + 1 ∧ (i.val + 1) + 1 < n := by
    have := generator_range n j
    omega
  have hforward := hp.2.1 (i.val + 1) hi
  have hreverse := weighted_path_reverse_temperley_lieb R hR d hd δ hδ hPF n s t
    (i.val + 1) hi
  have hidx : j.val + 1 = (i.val + 1) + 1 := by omega
  have hQindex : pathProjection R d δ n s t (j.val + 1) (generator_range n j) =
      pathProjection R d δ n s t ((i.val + 1) + 1) ⟨by omega, hi.2⟩ := by
    congr 1
  apply matrix_adjacent _ _ (hp.1 (i.val + 1) (generator_range n i)).2
    (hp.1 (j.val + 1) (generator_range n j)).2 (δ : ℂ) A
    (by exact_mod_cast ne_of_gt hδ) hA hparameter
  · rw [hQindex]
    exact hforward
  · rw [hQindex]
    exact hreverse

private theorem rho_relators
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (s : L) :
    ∀ r ∈ artinRelators n,
      FreeGroup.lift (rhoUnit R hR d hd δ hδ hPF A hA hparameter n s) r = 1 := by
  intro r hr
  rcases hr with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩
  · simp only [distantWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [rhoUnit_distant R hR d hd δ hδ hPF A hA hparameter n s i j hij]
    exact mul_inv_cancel _
  · simp only [adjacentWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [rhoUnit_adjacent R hR d hd δ hδ hPF A hA hparameter n s i j hij]
    exact mul_inv_cancel _

/-- The actual Artin group representation, not merely a family of generator equations. -/
def representation
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (s : L) : Artin n →* (C R n s)ˣ :=
  PresentedGroup.toGroup (rho_relators R hR d hd δ hδ hPF A hA hparameter n s)

/-- Inclusion of the old generator slots after adjoining one strand. -/
def includeGenerator (n : ℕ) (i : Fin (n - 1)) : Fin ((n + 1)-1) :=
  ⟨i.val, by have := i.is_lt; omega⟩

private theorem include_relators (n : ℕ) :
    (artinRelators n).MapsTo (FreeGroup.map (includeGenerator n)) (artinRelators (n + 1)) := by
  intro r hr
  rcases hr with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩
  · refine Or.inl ⟨includeGenerator n i, includeGenerator n j, hij, ?_⟩
    simp [distantWord]
  · refine Or.inr ⟨includeGenerator n i, includeGenerator n j, hij, ?_⟩
    simp [adjacentWord]

/-- Actual homomorphism of Artin presentation quotients, without an injectivity claim. -/
def strandInclusion (n : ℕ) : Artin n →* Artin (n + 1) :=
  PresentedGroup.map (FreeGroup.map (includeGenerator n)) (include_relators n)

private theorem strandInclusion_of (n : ℕ) (i : Fin (n - 1)) :
    strandInclusion n (PresentedGroup.of i) = PresentedGroup.of (includeGenerator n i) := by
  change PresentedGroup.mk (artinRelators (n + 1))
    (FreeGroup.map (includeGenerator n) (FreeGroup.of i)) = _
  simp only [FreeGroup.map.of]
  rfl

private theorem representation_natural
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (s : L) :
    (Units.map (iotaHom R n s).toAlgHom.toMonoidHom).comp
        (representation R hR d hd δ hδ hPF A hA hparameter n s) =
      (representation R hR d hd δ hδ hPF A hA hparameter (n + 1) s).comp
        (strandInclusion n) := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply, strandInclusion_of, representation, PresentedGroup.toGroup.of]
  apply Units.ext
  change iotaHom R n s (A⁻¹ • 1 + (A * (δ : ℂ)) •
      localProjection R d δ n s (i.val + 1) (generator_range n i)) =
    A⁻¹ • 1 + (A * (δ : ℂ)) • localProjection R d δ (n + 1) s
      ((includeGenerator n i).val + 1) (generator_range (n + 1) (includeGenerator n i))
  rw [map_add, map_smul, map_smul, map_one]
  change A⁻¹ • 1 + (A * (δ : ℂ)) •
      iota R n s (localProjection R d δ n s (i.val + 1) (generator_range n i)) = _
  rw [(weighted_path_projection_naturality R d δ).1 n s (i.val + 1) (generator_range n i)]
  rfl

private theorem exponent_relators (n : ℕ) :
    ∀ r ∈ artinRelators n,
      FreeGroup.lift (fun _ : Fin (n - 1) => Multiplicative.ofAdd (1 : ℤ)) r = 1 := by
  intro r hr
  rcases hr with ⟨i, j, _, rfl⟩ | ⟨i, j, _, rfl⟩
  · simp [distantWord]
  · simp [adjacentWord]

/-- Integer exponent sum, descended to the actual presentation quotient. -/
def exponentHom (n : ℕ) : Artin n →* Multiplicative ℤ :=
  PresentedGroup.toGroup (exponent_relators n)

/-- Writhe is integer-valued, so both signed stabilizations are meaningful. -/
def writhe (n : ℕ) (b : Artin n) : ℤ := (exponentHom n b).toAdd

private theorem exponent_natural (n : ℕ) :
    (exponentHom (n + 1)).comp (strandInclusion n) = exponentHom n := by
  apply PresentedGroup.ext
  intro i
  simp [exponentHom, strandInclusion_of]

/-- The last generator after adding a strand; its index is n, not a truncated zero index. -/
def lastGenerator (n : ℕ) (hn : 0 < n) : Artin (n + 1) :=
  PresentedGroup.of (⟨n - 1, by omega⟩ : Fin ((n + 1) - 1))

/-- Every algebraic braid with a strictly positive strand count. -/
abbrev PositiveBraid := Σ n : {n : ℕ // 0 < n}, Artin n.val

/-- Markov moves are defined independently of any trace or proposed invariant. -/
inductive MarkovStep : PositiveBraid → PositiveBraid → Prop
  | conjugation (n : ℕ) (hn : 0 < n) (b c : Artin n) :
      MarkovStep ⟨⟨n, hn⟩, b⟩ ⟨⟨n, hn⟩, c * b * c⁻¹⟩
  | positive (n : ℕ) (hn : 0 < n) (b : Artin n) :
      MarkovStep ⟨⟨n, hn⟩, b⟩
        ⟨⟨n + 1, by omega⟩, strandInclusion n b * lastGenerator n hn⟩
  | negative (n : ℕ) (hn : 0 < n) (b : Artin n) :
      MarkovStep ⟨⟨n, hn⟩, b⟩
        ⟨⟨n + 1, by omega⟩, strandInclusion n b * (lastGenerator n hn)⁻¹⟩

/-- Finite equivalence chains of the actual algebraic Markov moves. -/
abbrev MarkovEquivalent := Relation.EqvGen MarkovStep

/-- This quotient is algebraic; no geometric closure identification is assumed. -/
abbrev AlgebraicMarkovClass := Quotient (Relation.EqvGen.setoid MarkovStep)

private theorem tau_add (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s : L) (X Y : C R n s) :
    tau R d δ n s (X + Y) = tau R d δ n s X + tau R d δ n s Y := by
  simp only [tau, Pi.add_apply, Matrix.trace_add, mul_add, Finset.sum_add_distrib, add_div]

private theorem trace_last_linear
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (n : ℕ) (hn : 0 < n) (s : L) (X : C R n s) (a b : ℂ) :
    tau R d δ (n + 1) s
        (iota R n s X * (a • 1 + b • lastProjection R d δ n hn s)) =
      (a + b * (δ : ℂ)⁻¹ ^ 2) * tau R d δ n s X := by
  obtain ⟨_, _, _, _, _, _, _, hc, _, hl⟩ :=
    weighted_path_markov_trace R hR d hd δ hδ hPF n s
  rw [mul_add, mul_smul_comm, mul_one, mul_smul_comm, tau_add, tau_smul,
    tau_smul, hc, (hl hn).2.1]
  ring

private theorem signed_trace_constants
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (hn : 0 < n) (s : L) (X : C R n s) :
    tau R d δ (n + 1) s
        (iota R n s X * (A⁻¹ • 1 + (A * (δ : ℂ)) • lastProjection R d δ n hn s)) =
        (-(A⁻¹ ^ 3) / (δ : ℂ)) * tau R d δ n s X ∧
      tau R d δ (n + 1) s
        (iota R n s X * (A • 1 + (A⁻¹ * (δ : ℂ)) • lastProjection R d δ n hn s)) =
        (-(A ^ 3) / (δ : ℂ)) * tau R d δ n s X := by
  have hdc : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
  constructor
  · rw [trace_last_linear R hR d hd δ hδ hPF]
    congr 1
    field_simp [hA, hdc]
    rw [hparameter]
    field_simp [hA]
    ring
  · rw [trace_last_linear R hR d hd δ hδ hPF]
    congr 1
    field_simp [hA, hdc]
    rw [hparameter]
    field_simp [hA]
    ring

private theorem writhe_include (n : ℕ) (b : Artin n) :
    writhe (n + 1) (strandInclusion n b) = writhe n b := by
  exact congrArg Multiplicative.toAdd
    (congrArg (fun f : Artin n →* Multiplicative ℤ => f b) (exponent_natural n))

private theorem writhe_last (n : ℕ) (hn : 0 < n) :
    writhe (n + 1) (lastGenerator n hn) = 1 := by
  simp [writhe, exponentHom, lastGenerator]

private theorem writhe_positive (n : ℕ) (hn : 0 < n) (b : Artin n) :
    writhe (n + 1) (strandInclusion n b * lastGenerator n hn) = writhe n b + 1 := by
  change (exponentHom (n + 1) _).toAdd = _
  rw [map_mul, toAdd_mul]
  change writhe (n + 1) (strandInclusion n b) + writhe (n + 1) (lastGenerator n hn) = _
  rw [writhe_include, writhe_last]

private theorem writhe_negative (n : ℕ) (hn : 0 < n) (b : Artin n) :
    writhe (n + 1) (strandInclusion n b * (lastGenerator n hn)⁻¹) = writhe n b - 1 := by
  change (exponentHom (n + 1) _).toAdd = _
  rw [map_mul, toAdd_mul, map_inv, toAdd_inv]
  change writhe (n + 1) (strandInclusion n b) - writhe (n + 1) (lastGenerator n hn) = _
  rw [writhe_include, writhe_last]

private theorem writhe_conjugation (n : ℕ) (b c : Artin n) :
    writhe n (c * b * c⁻¹) = writhe n b := by
  simp only [writhe, map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

private theorem representation_include
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (s : L) (b : Artin n) :
    (representation R hR d hd δ hδ hPF A hA hparameter (n + 1) s (strandInclusion n b) :
        C R (n + 1) s) =
      iota R n s (representation R hR d hd δ hδ hPF A hA hparameter n s b : C R n s) := by
  have h := congrArg (fun f : Artin n →* (C R (n + 1) s)ˣ => f b)
    (representation_natural R hR d hd δ hδ hPF A hA hparameter n s)
  exact congrArg Units.val h.symm

private theorem representation_last
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (hn : 0 < n) (s : L) :
    (representation R hR d hd δ hδ hPF A hA hparameter (n + 1) s (lastGenerator n hn) :
        C R (n + 1) s) =
      A⁻¹ • 1 + (A * (δ : ℂ)) • lastProjection R d δ n hn s ∧
    (representation R hR d hd δ hδ hPF A hA hparameter (n + 1) s (lastGenerator n hn)⁻¹ :
        C R (n + 1) s) =
      A • 1 + (A⁻¹ * (δ : ℂ)) • lastProjection R d δ n hn s := by
  have hi : (n - 1) + 1 = n := by omega
  have hlocal : localProjection R d δ (n + 1) s ((n - 1) + 1) ⟨by omega, by omega⟩ =
      lastProjection R d δ n hn s := by
    funext t
    change pathProjection R d δ (n + 1) s t ((n - 1) + 1) _ =
      pathProjection R d δ (n + 1) s t n _
    congr 1
  constructor
  · simp only [representation, lastGenerator, PresentedGroup.toGroup.of]
    change A⁻¹ • 1 + (A * (δ : ℂ)) •
      localProjection R d δ (n + 1) s ((n - 1) + 1) ⟨by omega, by omega⟩ = _
    rw [hlocal]
  · rw [map_inv]
    simp only [representation, lastGenerator, PresentedGroup.toGroup.of]
    change A • 1 + (A⁻¹ * (δ : ℂ)) •
      localProjection R d δ (n + 1) s ((n - 1) + 1) ⟨by omega, by omega⟩ = _
    rw [hlocal]

/-- Writhe-normalized path trace, on positive strand layers and with integer exponent. -/
def normalizedTrace
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (s : L) (b : PositiveBraid) : ℂ :=
  (δ : ℂ) ^ (b.1.val - 1) * (-A ^ 3) ^ writhe b.1.val b.2 *
    tau R d δ b.1.val s
      (representation R hR d hd δ hδ hPF A hA hparameter b.1.val s b.2 : C R b.1.val s)

private theorem normalization_positive (δ A : ℂ) (hδ : δ ≠ 0) (hA : A ≠ 0)
    (n : ℕ) (hn : 0 < n) (w : ℤ) (z : ℂ) :
    δ ^ ((n + 1) - 1) * (-A ^ 3) ^ (w + 1) * (-(A⁻¹ ^ 3) / δ * z) =
      δ ^ (n - 1) * (-A ^ 3) ^ w * z := by
  have hc : -A ^ 3 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hA)
  have hp : δ ^ n = δ ^ (n - 1) * δ := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  simp only [Nat.add_sub_cancel]
  rw [hp, zpow_add_one₀ hc]
  field_simp [hA, hδ]

private theorem normalization_negative (δ A : ℂ) (hδ : δ ≠ 0) (hA : A ≠ 0)
    (n : ℕ) (hn : 0 < n) (w : ℤ) (z : ℂ) :
    δ ^ ((n + 1) - 1) * (-A ^ 3) ^ (w - 1) * (-(A ^ 3) / δ * z) =
      δ ^ (n - 1) * (-A ^ 3) ^ w * z := by
  have hc : -A ^ 3 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hA)
  have hp : δ ^ n = δ ^ (n - 1) * δ := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  simp only [Nat.add_sub_cancel]
  rw [hp, zpow_sub_one₀ hc]
  field_simp [hA, hδ]

private theorem trace_conjugation
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (s : L) (b c : Artin n) :
    tau R d δ n s
      (representation R hR d hd δ hδ hPF A hA hparameter n s (c * b * c⁻¹) : C R n s) =
    tau R d δ n s
      (representation R hR d hd δ hδ hPF A hA hparameter n s b : C R n s) := by
  let ρ := representation R hR d hd δ hδ hPF A hA hparameter n s
  change tau R d δ n s (ρ (c * b * c⁻¹) : C R n s) = _
  rw [map_mul, map_mul, map_inv]
  change tau R d δ n s
    ((ρ c : C R n s) * (ρ b : C R n s) * (((ρ c)⁻¹ : (C R n s)ˣ) : C R n s)) = _
  rw [(weighted_path_projection_naturality R d δ).2 n s
    ((ρ c : C R n s) * (ρ b : C R n s)) (((ρ c)⁻¹ : (C R n s)ˣ) : C R n s)]
  rw [← mul_assoc, Units.inv_mul, one_mul]

private theorem trace_stabilization
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (n : ℕ) (hn : 0 < n) (s : L) (b : Artin n) :
    tau R d δ (n + 1) s
      (representation R hR d hd δ hδ hPF A hA hparameter (n + 1) s
        (strandInclusion n b * lastGenerator n hn) : C R (n + 1) s) =
      (-(A⁻¹ ^ 3) / (δ : ℂ)) * tau R d δ n s
        (representation R hR d hd δ hδ hPF A hA hparameter n s b : C R n s) ∧
    tau R d δ (n + 1) s
      (representation R hR d hd δ hδ hPF A hA hparameter (n + 1) s
        (strandInclusion n b * (lastGenerator n hn)⁻¹) : C R (n + 1) s) =
      (-(A ^ 3) / (δ : ℂ)) * tau R d δ n s
        (representation R hR d hd δ hδ hPF A hA hparameter n s b : C R n s) := by
  have hlast := representation_last R hR d hd δ hδ hPF A hA hparameter n hn s
  have hinc := representation_include R hR d hd δ hδ hPF A hA hparameter n s b
  have htrace := signed_trace_constants R hR d hd δ hδ hPF A hA hparameter n hn s
    (representation R hR d hd δ hδ hPF A hA hparameter n s b : C R n s)
  constructor
  · rw [map_mul, Units.val_mul, hinc, hlast.1]
    exact htrace.1
  · rw [map_mul, Units.val_mul, hinc, hlast.2]
    exact htrace.2

private theorem normalizedTrace_step
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (s : L) {b c : PositiveBraid} (h : MarkovStep b c) :
    normalizedTrace R hR d hd δ hδ hPF A hA hparameter s b =
      normalizedTrace R hR d hd δ hδ hPF A hA hparameter s c := by
  have hdc : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ
  cases h with
  | conjugation n hn b c =>
    simp only [normalizedTrace, writhe_conjugation,
      trace_conjugation R hR d hd δ hδ hPF A hA hparameter]
  | positive n hn b =>
    simp only [normalizedTrace, writhe_positive]
    rw [(trace_stabilization R hR d hd δ hδ hPF A hA hparameter n hn s b).1]
    exact (normalization_positive (δ : ℂ) A hdc hA n hn (writhe n b) _).symm
  | negative n hn b =>
    simp only [normalizedTrace, writhe_negative]
    rw [(trace_stabilization R hR d hd δ hδ hPF A hA hparameter n hn s b).2]
    exact (normalization_negative (δ : ℂ) A hdc hA n hn (writhe n b) _).symm

/-- The actual path-model trace is invariant under all finite algebraic Markov chains.
This is not a theorem identifying those chains with geometric link isotopy. -/
theorem weighted_path_artin_markov_invariant
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (s : L) {b c : PositiveBraid} (h : MarkovEquivalent b c) :
    normalizedTrace R hR d hd δ hδ hPF A hA hparameter s b =
      normalizedTrace R hR d hd δ hδ hPF A hA hparameter s c := by
  induction h with
  | rel b c h => exact normalizedTrace_step R hR d hd δ hδ hPF A hA hparameter s h
  | refl b => rfl
  | symm b c _ ih => exact ih.symm
  | trans b c e _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A well-defined function on the algebraic Markov quotient. -/
def markovValue
    (R : L → L → Prop) [DecidableRel R] (hR : Std.Symm R)
    (d : L → ℝ) (hd : ∀ a, 0 < d a) (δ : ℝ) (hδ : 0 < δ)
    (hPF : ∀ a, (∑ b : L with R a b, d b) = δ * d a)
    (A : ℂ) (hA : A ≠ 0) (hparameter : (δ : ℂ) = -A ^ 2 - A⁻¹ ^ 2)
    (s : L) : AlgebraicMarkovClass → ℂ :=
  Quotient.lift (normalizedTrace R hR d hd δ hδ hPF A hA hparameter s)
    (fun _ _ h => weighted_path_artin_markov_invariant R hR d hd δ hδ hPF A hA hparameter s h)

#print axioms representation
#print axioms weighted_path_artin_markov_invariant
#print axioms markovValue
end D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
