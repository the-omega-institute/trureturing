/- GID: D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compatibility under all Heisenberg channels equals compatibility in all subspaces. -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence

/-- A family is jointly measurable if all effects are marginals of one parent POVM. -/
def FamilyJointlyMeasurable {d : ℕ} {X : Type} [Fintype X]
    {Ω : X → Type} [∀ x, Fintype (Ω x)]
    (M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ) : Prop := by
  classical
  exact ∃ G : ((x : X) → Ω x) → Matrix (Fin d) (Fin d) ℂ,
    IsPOVM G ∧ ∀ x b, (∑ a with a x = b, G a) = M x b

/-- Compression compatibility and unital completely positive compatibility agree. -/
def claim : Prop :=
  ∀ (d n : ℕ), 1 ≤ n → n ≤ d →
    ∀ (X : Type) [Fintype X] (Ω : X → Type) [∀ x, Fintype (Ω x)]
      (M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ),
      (∀ x, IsPOVM (M x)) →
      ((∀ V : Matrix (Fin d) (Fin n) ℂ, Vᴴ * V = 1 →
        FamilyJointlyMeasurable (fun x b => Vᴴ * M x b * V)) ↔
       (∀ Φ : MatrixMap (Fin d) (Fin n) ℂ, Φ.IsCompletelyPositive → Φ 1 = 1 →
        FamilyJointlyMeasurable (fun x b => Φ (M x b))))

private def compressionMap {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℂ) :
    MatrixMap (Fin d) (Fin n) ℂ :=
  MatrixMap.of_kraus (fun _ : Unit => Vᴴ) (fun _ : Unit => Vᴴ)

private theorem compression_channel {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℂ)
    (hV : Vᴴ * V = 1) :
    (compressionMap V).IsCompletelyPositive ∧ compressionMap V 1 = 1 ∧
      ∀ A, compressionMap V A = Vᴴ * A * V := by
  have hA (A : Matrix (Fin d) (Fin d) ℂ) : compressionMap V A = Vᴴ * A * V := by
    simp only [compressionMap, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_conjTranspose,
      Fintype.sum_unique]
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive (fun _ : Unit => Vᴴ), ?_, hA⟩
  rw [hA, Matrix.mul_one, hV]

private theorem heisenberg_kraus {d n : ℕ}
    (Φ : MatrixMap (Fin d) (Fin n) ℂ) (hCP : Φ.IsCompletelyPositive) (hu : Φ 1 = 1) :
    ∃ K : (Fin n × Fin d) → Matrix (Fin d) (Fin n) ℂ,
      (∑ r, (K r)ᴴ * K r) = 1 ∧ ∀ A, Φ A = ∑ r, (K r)ᴴ * A * K r := by
  obtain ⟨L, hL⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Φ hCP
  refine ⟨fun r => (L r)ᴴ, ?_, ?_⟩
  · rw [hL] at hu
    simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.mul_one, Matrix.conjTranspose_conjTranspose] using hu
  · intro A
    rw [hL]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.conjTranspose_conjTranspose]

private theorem isometric_factorization {d n : ℕ} (hnd : n ≤ d)
    (K : Matrix (Fin d) (Fin n) ℂ) :
    ∃ (V : Matrix (Fin d) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ),
      Vᴴ * V = 1 ∧ K = V * C := by
  classical
  let col : Fin n → EuclideanSpace ℂ (Fin d) :=
    fun j => WithLp.toLp 2 (fun i => K i j)
  let f : Fin d → EuclideanSpace ℂ (Fin d) :=
    fun j => if hj : j.val < n then col ⟨j.val, hj⟩ else 0
  have hf (j : Fin n) : f (Fin.castLE hnd j) = col j := by
    dsimp only [f, Fin.castLE]
    rw [dite_eq_left j.isLt]
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = Fintype.card (Fin d) :=
    finrank_euclideanSpace
  let q := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  let V : Matrix (Fin d) (Fin n) ℂ := fun i j => q (Fin.castLE hnd j) i
  let C : Matrix (Fin n) (Fin n) ℂ := fun i j => q.repr (col j) (Fin.castLE hnd i)
  have htail (j : Fin n) (i : Fin d) (hi : n ≤ i.val) : q.repr (col j) i = 0 := by
    have hij : Fin.castLE hnd j < i := Nat.lt_of_lt_of_le j.isLt hi
    have hz := InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular' hdim f hij
    change q.repr (f (Fin.castLE hnd j)) i = 0 at hz
    rw [hf j] at hz
    exact hz
  refine ⟨V, C, ?_, ?_⟩
  · ext i j
    rw [← inner_matrix_col_col V V i j, Matrix.one_apply]
    change inner ℂ (q (Fin.castLE hnd i)) (q (Fin.castLE hnd j)) =
      if i = j then 1 else 0
    rw [q.inner_eq_ite]
    by_cases hij : i = j
    · rw [if_pos (congrArg (Fin.castLE hnd) hij), if_pos hij]
    · rw [if_neg (fun h => hij (Fin.castLE_injective hnd h)), if_neg hij]
  · symm
    ext i j
    change (∑ k : Fin n,
      q (Fin.castLE hnd k) i * q.repr (col j) (Fin.castLE hnd k)) = K i j
    let s : Finset (Fin d) := Finset.univ.image (Fin.castLE hnd)
    have hsum : (∑ k : Fin d, q k i * q.repr (col j) k) = K i j := by
      have h := congrArg (fun v : EuclideanSpace ℂ (Fin d) => v i)
        (q.sum_repr (col j))
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] at h
      change (∑ k : Fin d, q.repr (col j) k * q k i) = K i j at h
      calc
        _ = ∑ k : Fin d, q.repr (col j) k * q k i :=
          Finset.sum_congr rfl (fun k _ => mul_comm _ _)
        _ = _ := h
    calc
      _ = ∑ k ∈ s, q k i * q.repr (col j) k :=
        (Finset.sum_image (Fin.castLE_injective hnd).injOn).symm
      _ = ∑ k : Fin d, q k i * q.repr (col j) k := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        have hn : n ≤ k.val := by
          by_contra hn
          have hkn : k.val < n := Nat.lt_of_not_ge hn
          apply hk
          exact Finset.mem_image.mpr ⟨⟨k.val, hkn⟩, Finset.mem_univ _, rfl⟩
        rw [htail j k hn, mul_zero]
      _ = _ := hsum

private theorem sum_compressed_parents {n : ℕ} {X R : Type} [Fintype X] [Fintype R]
    {Ω : X → Type} [∀ x, Fintype (Ω x)]
    (C : R → Matrix (Fin n) (Fin n) ℂ)
    (N : R → (x : X) → Ω x → Matrix (Fin n) (Fin n) ℂ)
    (hC : (∑ r, (C r)ᴴ * C r) = 1)
    (hN : ∀ r, FamilyJointlyMeasurable (N r)) :
    FamilyJointlyMeasurable (fun x b => ∑ r, (C r)ᴴ * N r x b * C r) := by
  classical
  choose G hG hm using hN
  refine ⟨fun a => ∑ r, (C r)ᴴ * G r a * C r, ⟨?_, ?_⟩, ?_⟩
  · intro a
    exact Matrix.posSemidef_sum _ (fun r _ =>
      ((hG r).1 a).conjTranspose_mul_mul_same (C r))
  · rw [Finset.sum_comm]
    calc
      _ = ∑ r, (C r)ᴴ * C r := by
        apply Finset.sum_congr rfl
        intro r _
        rw [← Matrix.sum_mul, ← Matrix.mul_sum, (hG r).2, Matrix.mul_one]
      _ = 1 := hC
  · intro x b
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hm r x b]

private theorem channels_of_compressions {d n : ℕ} (hnd : n ≤ d)
    {X : Type} [Fintype X] {Ω : X → Type} [∀ x, Fintype (Ω x)]
    (M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ V : Matrix (Fin d) (Fin n) ℂ, Vᴴ * V = 1 →
      FamilyJointlyMeasurable (fun x b => Vᴴ * M x b * V))
    (Φ : MatrixMap (Fin d) (Fin n) ℂ) (hCP : Φ.IsCompletelyPositive) (hu : Φ 1 = 1) :
    FamilyJointlyMeasurable (fun x b => Φ (M x b)) := by
  obtain ⟨K, hK, hΦ⟩ := heisenberg_kraus Φ hCP hu
  choose V C hV hfactor using fun r => isometric_factorization hnd (K r)
  have hC : (∑ r, (C r)ᴴ * C r) = 1 := by
    sorry
  have hp := sum_compressed_parents C (fun r x b => (V r)ᴴ * M x b * V r) hC
    (fun r => hM (V r) (hV r))
  have heq : (fun x b => ∑ r, (C r)ᴴ * ((V r)ᴴ * M x b * V r) * C r) =
      (fun x b => Φ (M x b)) := by
    sorry
  rw [heq] at hp
  exact hp

private theorem compressions_of_channels {d n : ℕ}
    {X : Type} [Fintype X] {Ω : X → Type} [∀ x, Fintype (Ω x)]
    (M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ Φ : MatrixMap (Fin d) (Fin n) ℂ, Φ.IsCompletelyPositive → Φ 1 = 1 →
      FamilyJointlyMeasurable (fun x b => Φ (M x b)))
    (V : Matrix (Fin d) (Fin n) ℂ) (hV : Vᴴ * V = 1) :
    FamilyJointlyMeasurable (fun x b => Vᴴ * M x b * V) := by
  obtain ⟨hCP, hu, hA⟩ := compression_channel V hV
  have hp := hM (compressionMap V) hCP hu
  have heq : (fun x b => compressionMap V (M x b)) =
      (fun x b => Vᴴ * M x b * V) := funext fun x => funext fun b => hA (M x b)
  rw [heq] at hp
  exact hp

/-- Every isometric compression is compatible exactly when every Heisenberg image is. -/
theorem result : claim := by
  intro d n _ hnd X _ Ω _ M _
  exact ⟨channels_of_compressions hnd M, compressions_of_channels M⟩

end D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence
