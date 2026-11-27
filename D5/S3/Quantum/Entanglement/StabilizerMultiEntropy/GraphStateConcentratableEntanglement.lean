/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateConcentratableEntanglement
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateConcentratableEntanglement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prove all-real-power subsystem monotonicity of generalized concentratable entanglement for finite graph states. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith

/-! Real power-trace GCE is monotone on subsystem inclusions of finite graph states.
The proof computes a normalized cut projector, then applies the four-functions inequality
to its symmetric, log-supermodular moment weights. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
open Matrix
open scoped Classical ComplexOrder MatrixOrder FinsetFamily
local notation "𝔽" => ZMod 2
section
open Finset
variable {V K : Type*} [Fintype V] [DecidableEq V] [Field K] [LinearOrder K]
  [IsStrictOrderedRing K]
private def Objective (w : Finset V → K) (s : Finset V) : K :=
  (∑ a ∈ s.powerset, w a) / (s.powerset.card : K)
variable (w : Finset V → K)
omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Complement symmetry equalizes the two weights of the complete one-site fiber. -/
private theorem full_fibers_equal (hcomp : ∀ a, w (univ \ a) = w a) (i : V) :
    (∑ a ∈ (univ.erase i : Finset V).powerset, w a) =
      ∑ a ∈ (univ.erase i : Finset V).powerset, w (insert i a) := by
  let u := (univ : Finset V).erase i
  change (∑ a ∈ u.powerset, w a) = ∑ a ∈ u.powerset, w (insert i a)
  apply sum_bij (fun a _ => u \ a)
  · intro a ha
    exact mem_powerset.mpr sdiff_subset
  · intro a ha b hb he
    have e := congrArg (fun t => u \ t) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_powerset.mp ha),
      Finset.sdiff_sdiff_eq_self (mem_powerset.mp hb)] using e
  · intro a ha
    exact ⟨u \ a, mem_powerset.mpr sdiff_subset,
      Finset.sdiff_sdiff_eq_self (mem_powerset.mp ha)⟩
  · intro a ha
    have hi : i ∉ a := notMem_mono (mem_powerset.mp ha) (notMem_erase i _)
    have hc : insert i (u \ a) = univ \ a := by
      ext j
      by_cases h : j = i
      · subst j
        simp [hi]
      · simp [u, h]
    rw [hc,hcomp]
/-- In any downward-closed subfamily of the other sites, insertion of one site
does not increase the total weight. Only the empty-set weight must be strictly positive. -/
private theorem downset_insertion_le
    (h₀ : ∀ a, 0 ≤ w a) (he : 0 < w ∅)
    (hcomp : ∀ a, w (univ \ a) = w a)
    (hsuper : ∀ a b, w a * w b ≤ w (a ∩ b) * w (a ∪ b))
    (i : V) (𝒟 : Finset (Finset V)) (hD : 𝒟 ⊆ (univ.erase i).powerset)
    (hdown : ∀ a ∈ 𝒟, ∀ b ⊆ a, b ∈ 𝒟) (hE : ∅ ∈ 𝒟) :
    (∑ a ∈ 𝒟, w (insert i a)) ≤ ∑ a ∈ 𝒟, w a := by
  let u := (univ : Finset V).erase i
  have hmin : 𝒟 ⊼ u.powerset = 𝒟 := by
    apply Subset.antisymm
    · intro c hc
      obtain ⟨a,ha,b,_,rfl⟩ := mem_infs.mp hc
      exact hdown a ha (a ∩ b) inter_subset_left
    · intro a ha
      have hu : u ∈ u.powerset := mem_powerset.mpr Subset.rfl
      exact mem_infs.mpr ⟨a, ha, u, hu, inter_eq_left.mpr (mem_powerset.mp (hD ha))⟩
  have hmax : 𝒟 ⊻ u.powerset = u.powerset := by
    apply Subset.antisymm
    · intro c hc
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_sups.mp hc
      exact mem_powerset.mpr (union_subset (mem_powerset.mp (hD ha)) (mem_powerset.mp hb))
    · intro a ha
      exact mem_sups.mpr ⟨∅,hE,a,ha,empty_union a⟩
  have hh : ∀ ⦃a⦄, a ⊆ u → ∀ ⦃b⦄, b ⊆ u →
      w (insert i a) * w b ≤ w (a ∩ b) * w (insert i (a ∪ b)) := by
    intro a _ b hb
    have hn : i ∉ b := notMem_mono hb (notMem_erase i _)
    simpa only [insert_inter_of_notMem hn,insert_union] using hsuper (insert i a) b
  have H := u.four_functions_theorem (f₁ := fun a => w (insert i a)) (f₂ := w)
    (f₃ := w) (f₄ := fun a => w (insert i a))
    (fun a => h₀ _) h₀ h₀ (fun a => h₀ _) hh hD (Subset.rfl)
  rw [hmin,hmax,← full_fibers_equal w hcomp i] at H
  apply le_of_mul_le_mul_right H
  have hp : ∅ ∈ u.powerset := mem_powerset.mpr (empty_subset _)
  exact Finset.sum_pos' (fun a _ => h₀ a) ⟨∅,hp,he⟩
omit [Fintype V] in
private theorem insertion_bij {s : Finset V} {i : V} (hi : i ∉ s) :
    Set.InjOn (insert i) (s.powerset : Set (Finset V)) := by
  intro a ha b hb e
  have hn₁ := notMem_mono (mem_powerset.mp (show a ∈ s.powerset from ha)) hi
  have hn₂ := notMem_mono (mem_powerset.mp (show b ∈ s.powerset from hb)) hi
  have ee := congrArg (fun t : Finset V => t.erase i) e
  simpa only [erase_insert hn₁,erase_insert hn₂] using ee
omit [Fintype V] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem insertion_split {s : Finset V} {i : V} (hi : i ∉ s) :
    (∑ a ∈ (insert i s).powerset, w a) =
    (∑ a ∈ s.powerset, w a) + ∑ a ∈ s.powerset, w (insert i a) := by
  have hd : Disjoint s.powerset (s.powerset.image (insert i)) := by
    rw [disjoint_left]
    rintro _ ha hb
    obtain ⟨b,_,rfl⟩ := mem_image.mp hb
    exact (notMem_mono (mem_powerset.mp ha) hi) (mem_insert_self _ _)
  rw [powerset_insert,sum_union hd,sum_image (insertion_bij hi)]
/-- The powerset average weakly decreases on inserting a new site. -/
private theorem objective_insert_le (h₀ : ∀ a, 0 ≤ w a) (he : 0 < w ∅)
    (hcomp : ∀ a, w (univ \ a) = w a)
    (hsuper : ∀ a b, w a * w b ≤ w (a ∩ b) * w (a ∪ b))
    {i : V} {s : Finset V} (hi : i ∉ s) :
    Objective w (insert i s) ≤ Objective w s := by
  have hs : s ⊆ univ.erase i := by
    intro a ha
    exact mem_erase.mpr ⟨fun h => hi (h ▸ ha),mem_univ _⟩
  have H := downset_insertion_le w h₀ he hcomp hsuper i s.powerset
    (powerset_mono.mpr hs) (fun a ha b hb => mem_powerset.mpr (hb.trans (mem_powerset.mp ha)))
    (mem_powerset.mpr (empty_subset _))
  unfold Objective
  rw [insertion_split w hi,card_powerset,card_insert_of_notMem hi,card_powerset,pow_succ]
  push_cast
  calc
    _ ≤ ((∑ a ∈ s.powerset, w a) + ∑ a ∈ s.powerset, w a) /
        ((2 : K) ^ s.card * 2) := by
      exact div_le_div_of_nonneg_right (add_le_add_right H _) (by positivity)
    _ = _ := by rw [← mul_two,mul_div_mul_right _ _ (by positivity : (2 : K) ≠ 0)]
/-- Complement symmetry plus log-supermodularity make the Boolean average
antitone under subset inclusion. -/
private theorem objective_antitone (h₀ : ∀ a, 0 ≤ w a) (he : 0 < w ∅)
    (hcomp : ∀ a, w (univ \ a) = w a)
    (hsuper : ∀ a b, w a * w b ≤ w (a ∩ b) * w (a ∪ b)) :
    Antitone (Objective w) := by
  have h (d a : Finset V) : Objective w (d ∪ a) ≤ Objective w a := by
    induction d using Finset.induction_on with
    | empty => simp
    | insert i d _ ih =>
      rw [insert_union]
      by_cases hi : i ∈ d ∪ a
      · simpa [insert_eq_of_mem hi] using ih
      · exact (objective_insert_le w h₀ he hcomp hsuper hi).trans ih
  intro a b hab
  simpa only [union_eq_left.mpr hab] using h b a
end
section
private abbrev F := ZMod 2
variable {I : Type*} [Fintype I]
private def signBit (a : F) : ℤ := if a = 0 then 1 else -1
private theorem sign_add (a b : F) : signBit (a+b) = signBit a * signBit b := by
  revert a b
  decide +kernel
private def bilin (U : Matrix I I F) (x y : I → F) : F :=
  ∑ i : I, ∑ j : I, U i j * x i * y j
private def quadratic (U : Matrix I I F) (x : I → F) : F := bilin U x x
end
section
variable {I : Type*} [Fintype I]
/-- Exact graph-state amplitudes in the computational chart. The common
nonzero normalization is omitted, so amplitudes remain integer signs. -/
private def amp (U : Matrix I I F) (x : I → F) : ℤ := signBit (quadratic U x)
end
section
variable {I : Type*} [Fintype I]
variable [LinearOrder I]
/-- The upper triangle gives exactly the undirected graph phase without
an arbitrary square root or duplicate counting of edges. -/
private def graphUpper (A : Matrix I I F) : Matrix I I F := fun i j => if i < j then A i j else 0
omit [Fintype I] in
private theorem graph_matrix_recovered (A : Matrix I I F)
    (hs : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 0) (i j : I) :
    graphUpper A i j + graphUpper A j i = A i j := by
  rcases lt_trichotomy i j with h|rfl|h
  · simp [graphUpper,h,not_lt_of_gt h]
  · simp [graphUpper,hd]
  · simp [graphUpper,h,not_lt_of_gt h,hs j i]
end
section
open scoped Classical
variable {J : Type*} [Fintype J]
private theorem walsh_exact (v : J → 𝔽) :
    (∑ y : J → 𝔽, signBit (v ⬝ᵥ y)) = if v = 0 then Fintype.card (J → 𝔽) else 0 := by
  by_cases hv : v = 0
  · simp [hv,signBit]
  · obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    let z : J → 𝔽 := Pi.single j 1
    have hz : v ⬝ᵥ z = 1 := by
      have hbit : ∀ x : 𝔽, x ≠ 0 → x = 1 := by decide +kernel
      simpa [z, dotProduct_single] using hbit _ hj
    let e : (J → 𝔽) ≃ (J → 𝔽) := Equiv.addRight z
    have he (y : J → 𝔽) : signBit (v ⬝ᵥ e y) = - signBit (v ⬝ᵥ y) := by
      change signBit (v ⬝ᵥ (y+z)) = _
      rw [dotProduct_add,hz,sign_add]
      simp [signBit]
    have h := Equiv.sum_comp e (fun y : J → 𝔽 => signBit (v ⬝ᵥ y))
    simp only [he,Finset.sum_neg_distrib] at h
    simp only [hv,ite_false]
    change (∑ y : J → 𝔽, signBit (v ⬝ᵥ y)) = (0:ℤ)
    omega
omit [Fintype J] in
private theorem add_eq_zero_iff (x y : J → 𝔽) : x+y=0 ↔ x=y := by
  have hbit : ∀ a b : 𝔽, a+b=0 ↔ a=b := by decide +kernel
  constructor
  · intro h
    funext i
    exact (hbit _ _).mp (congrFun h i)
  · rintro rfl
    funext i
    exact (hbit _ _).mpr rfl
variable {I : Type*} [Fintype I]
/-- Before the common normalization, the actual cross-block signed amplitude
has Gram entries given exactly by equal images of the binary cut map. -/
private theorem cross_amplitude_gram (B : Matrix J I 𝔽) (x x' : I → 𝔽) :
    (∑ y : J → 𝔽, signBit ((B *ᵥ x) ⬝ᵥ y) * signBit ((B *ᵥ x') ⬝ᵥ y)) =
      if B *ᵥ x = B *ᵥ x' then Fintype.card (J → 𝔽) else 0 := by
  simp_rw [← sign_add,← add_dotProduct]
  simp only [walsh_exact,add_eq_zero_iff]
end
section
open scoped Classical
variable {I J : Type*} [Fintype I] [Fintype J]
private def gram (B : Matrix J I 𝔽) : Matrix (I → 𝔽) (I → 𝔽) ℂ :=
  fun x x' => if B *ᵥ x = B *ᵥ x' then 1 else 0
private def kernelFiber (B : Matrix J I 𝔽) (x : I → 𝔽) :
    B.mulVecLin.ker ≃ {y : I → 𝔽 // B *ᵥ x = B *ᵥ y} where
  toFun z := ⟨x+z.val,by
    have hz : B *ᵥ z.val = 0 := LinearMap.mem_ker.mp z.property
    rw [mulVec_add,hz,add_zero]⟩
  invFun y := ⟨y.val-x,LinearMap.mem_ker.mpr (by
    change B *ᵥ (y.val-x) = 0
    have h := y.property
    exact (mulVec_sub B _ _).trans (sub_eq_zero.mpr h.symm))⟩
  left_inv z := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
private theorem gram_mul_self (B : Matrix J I 𝔽) :
    gram B * gram B = (Nat.card B.mulVecLin.ker : ℂ) • gram B := by
  ext x z
  rw [Matrix.mul_apply]
  by_cases h : B *ᵥ x = B *ᵥ z
  · have f (y : I → 𝔽) : gram B x y * gram B y z =
      if B *ᵥ x = B *ᵥ y then 1 else 0 := by
      unfold gram
      by_cases hy : B *ᵥ x = B *ᵥ y
      · simp [hy,hy.symm.trans h]
      · simp [hy]
    simp_rw [f]
    have hh : (∑ y : I → 𝔽, if B *ᵥ x = B *ᵥ y then (1:ℂ) else 0) =
        (Nat.card {y : I → 𝔽 // B *ᵥ x = B *ᵥ y} : ℂ) := by
      rw [← Finset.sum_filter]
      simp [Nat.card_eq_fintype_card,Fintype.card_subtype]
    rw [hh,← Nat.card_congr (kernelFiber B x)]
    simp [gram,h]
  · have f (y : I → 𝔽) : gram B x y * gram B y z = 0 := by
      by_cases hy : B *ᵥ x = B *ᵥ y
      · have hn : B *ᵥ y ≠ B *ᵥ z := fun hz => h (hy.trans hz)
        simp [gram,hy,hn]
      · simp [gram,hy]
    simp only [f,Finset.sum_const_zero]
    simp [gram,h]
omit [Fintype J] in
private theorem kernel_card (B : Matrix J I 𝔽) :
    Nat.card B.mulVecLin.ker = 2 ^ Module.finrank 𝔽 B.mulVecLin.ker := by
  let _ : Fintype B.mulVecLin.ker := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=𝔽)]
  simp
private def crossReduced (B : Matrix J I 𝔽) : Matrix (I → 𝔽) (I → 𝔽) ℂ :=
  ((2 : ℂ) ^ Fintype.card I)⁻¹ • gram B
private theorem crossReduced_trace (B : Matrix J I 𝔽) : (crossReduced B).trace = 1 := by
  unfold crossReduced Matrix.trace
  simp [gram]
/-- A cut's normalized cross-phase density obeys an exact quadratic polynomial.
Its nonzero eigenvalue is determined by cut rank, not by the full state dimension. -/
private theorem crossReduced_square (B : Matrix J I 𝔽) :
    crossReduced B * crossReduced B = ((2 : ℂ) ^ B.rank)⁻¹ • crossReduced B := by
  have he := B.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at he
  change B.rank + Module.finrank 𝔽 B.mulVecLin.ker = _ at he
  have hh : (2 : ℂ) ^ Fintype.card I = 2 ^ B.rank * 2 ^ Module.finrank 𝔽 B.mulVecLin.ker := by
    rw [← pow_add,he]
  unfold crossReduced
  rw [Matrix.smul_mul,Matrix.mul_smul,gram_mul_self,smul_smul,smul_smul,smul_smul,kernel_card,
    Nat.cast_pow, Nat.cast_ofNat, hh]
  congr 1
  field_simp
end
section
open scoped Classical
variable {I J : Type*} [Fintype I] [Fintype J]
/-- The actual unnormalized computational amplitudes across a cut, with a
separate sign phase from each induced subgraph and the true bilinear cross phase. -/
private def cutCoeff (B : Matrix J I 𝔽) (u : (I → 𝔽) → 𝔽) (v : (J → 𝔽) → 𝔽) :
    Matrix (I → 𝔽) (J → 𝔽) ℂ :=
  fun x y => (signBit (u x + v y + ((B *ᵥ x) ⬝ᵥ y)) : ℂ)
private def signedDiagonal (u : (I → 𝔽) → 𝔽) : Matrix (I → 𝔽) (I → 𝔽) ℂ :=
  Matrix.diagonal (fun x => (signBit (u x) : ℂ))
private theorem complex_sign_sq (t : 𝔽) :
    (signBit t : ℂ) * (signBit t : ℂ) = 1 := by
  by_cases h : t = 0 <;> simp [signBit,h]
private theorem signedDiagonal_sq (u : (I → 𝔽) → 𝔽) :
    signedDiagonal u * signedDiagonal u = 1 := by
  rw [signedDiagonal, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  exact complex_sign_sq _
private def cutDensity (B : Matrix J I 𝔽) (u : (I → 𝔽) → 𝔽) (v : (J → 𝔽) → 𝔽) :
    Matrix (I → 𝔽) (I → 𝔽) ℂ :=
  ((2:ℂ) ^ (Fintype.card I + Fintype.card J))⁻¹ •
    (cutCoeff B u v * (cutCoeff B u v).conjTranspose)
private theorem cutDensity_is_cross_conj (B : Matrix J I 𝔽)
    (u : (I → 𝔽) → 𝔽) (v : (J → 𝔽) → 𝔽) :
    cutDensity B u v = signedDiagonal u * crossReduced B * signedDiagonal u := by
  ext x z
  have hf (y : J → 𝔽) : (cutCoeff B u v x y * star (cutCoeff B u v z y)) =
     ((signBit (u x) : ℂ) * (signBit (u z) : ℂ)) *
     ((signBit ((B *ᵥ x) ⬝ᵥ y) : ℂ) * (signBit ((B *ᵥ z) ⬝ᵥ y) : ℂ)) := by
    simp only [cutCoeff,star_intCast]
    simp only [sign_add,Int.cast_mul]
    calc
      _ = ((signBit (u x) : ℂ) * (signBit (u z) : ℂ)) *
        ((signBit ((B *ᵥ x) ⬝ᵥ y) : ℂ) * (signBit ((B *ᵥ z) ⬝ᵥ y) : ℂ)) *
        ((signBit (v y) : ℂ) * (signBit (v y) : ℂ)) := by ring
      _ = _ := by rw [complex_sign_sq,mul_one]
  have hgram := congrArg (fun r : ℤ => (r : ℂ)) (cross_amplitude_gram B x z)
  push_cast at hgram
  simp only [signedDiagonal,mul_diagonal,diagonal_mul]
  simp only [cutDensity,Matrix.smul_apply,smul_eq_mul,mul_apply,conjTranspose_apply,hf,
    ← Finset.mul_sum]
  rw [hgram]
  simp only [crossReduced,Matrix.smul_apply,smul_eq_mul]
  by_cases h : B *ᵥ x = B *ᵥ z
  · simp [gram,h,pow_add]
    field_simp
  · simp [gram,h]
private theorem cutDensity_trace (B : Matrix J I 𝔽)
    (u : (I → 𝔽) → 𝔽) (v : (J → 𝔽) → 𝔽) :
    (cutDensity B u v).trace = 1 := by
  rw [cutDensity_is_cross_conj,Matrix.trace_mul_comm,← Matrix.mul_assoc,signedDiagonal_sq,one_mul,
    crossReduced_trace]
private theorem cutDensity_square (B : Matrix J I 𝔽)
    (u : (I → 𝔽) → 𝔽) (v : (J → 𝔽) → 𝔽) :
    cutDensity B u v * cutDensity B u v = ((2:ℂ)^B.rank)⁻¹ • cutDensity B u v := by
  rw [cutDensity_is_cross_conj]
  let D := signedDiagonal u
  let R := crossReduced B
  have hd : D * D = 1 := signedDiagonal_sq _
  have hr : R * R = ((2:ℂ)^B.rank)⁻¹ • R := crossReduced_square _
  change (D*R*D)*(D*R*D) = _
  calc
    _ = D * R * (D * D) * R * D := by noncomm_ring
    _ = D * (R * R) * D := by rw [hd,mul_one,Matrix.mul_assoc D]
    _ = _ := by rw [hr,Matrix.mul_smul,Matrix.smul_mul]
end
section
open scoped Classical
variable {I J : Type*} [Fintype I] [Fintype J]
/-- Any upper phase representation of the full graph, in a bipartition chart. -/
private def assembled (L : Matrix I I 𝔽) (R : Matrix J J 𝔽) (B : Matrix J I 𝔽) :
    Matrix (I ⊕ J) (I ⊕ J) 𝔽
  | .inl i, .inl j => L i j
  | .inr i, .inr j => R i j
  | .inl i, .inr j => B j i
  | .inr _, .inl _ => 0
private theorem quadratic_cut (L : Matrix I I 𝔽) (R : Matrix J J 𝔽) (B : Matrix J I 𝔽)
    (x : I → 𝔽) (y : J → 𝔽) :
    quadratic (assembled L R B) (Sum.elim x y) =
      quadratic L x + quadratic R y + ((B *ᵥ x) ⬝ᵥ y) := by
  unfold quadratic bilin Matrix.mulVec dotProduct
  simp only [Fintype.sum_sum_type,assembled,Sum.elim_inl,Sum.elim_inr,
    zero_mul,Finset.sum_const_zero,Finset.sum_add_distrib,Finset.sum_mul]
  have h : (∑ i : I, ∑ j : J, B j i * x i * y j) =
      ∑ j : J, ∑ i : I, B j i * x i * y j := Finset.sum_comm
  rw [h]
  abel
private def leftBlock (W : Matrix (I ⊕ J) (I ⊕ J) 𝔽) : Matrix I I 𝔽 :=
  fun i j => W (.inl i) (.inl j)
private def rightBlock (W : Matrix (I ⊕ J) (I ⊕ J) 𝔽) : Matrix J J 𝔽 :=
  fun i j => W (.inr i) (.inr j)
private def crossBlock (W : Matrix (I ⊕ J) (I ⊕ J) 𝔽) : Matrix J I 𝔽 :=
  fun j i => W (.inl i) (.inr j) + W (.inr j) (.inl i)
/-- No assumption on the within-cut ordering used to encode the graph phase:
the two cross directions collapse to one physically exact cross block. -/
private theorem arbitrary_phase_cut (W : Matrix (I ⊕ J) (I ⊕ J) 𝔽) (x : I → 𝔽) (y : J → 𝔽) :
    quadratic W (Sum.elim x y) =
    quadratic (leftBlock W) x + quadratic (rightBlock W) y + ((crossBlock W *ᵥ x) ⬝ᵥ y) := by
  unfold quadratic bilin Matrix.mulVec dotProduct leftBlock rightBlock crossBlock
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_mul,
    add_mul,Finset.sum_add_distrib]
  have h : (∑ i : I, ∑ j : J, W (.inl i) (.inr j) * x i * y j) =
      ∑ j : J, ∑ i : I, W (.inl i) (.inr j) * x i * y j := Finset.sum_comm
  rw [h]
  have hq : (∑ j : J, ∑ i : I, W (.inr j) (.inl i) * y j * x i) =
      ∑ j : J, ∑ i : I, W (.inr j) (.inl i) * x i * y j := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hq]
  abel
/-- Same actual sign amplitudes as obtained from the full assembled graph. -/
private theorem graph_amp_cut (L : Matrix I I 𝔽) (R : Matrix J J 𝔽) (B : Matrix J I 𝔽)
    (x : I → 𝔽) (y : J → 𝔽) :
    (amp (assembled L R B) (Sum.elim x y) : ℂ) =
      cutCoeff B (quadratic L) (quadratic R) x y := by
  simp [amp,cutCoeff,quadratic_cut]
/-- The reduced matrix is defined by the actual sum of graph-amplitude
outer-product entries, with uniform graph-state normalization. -/
private def graphCutReduction (L : Matrix I I 𝔽) (R : Matrix J J 𝔽) (B : Matrix J I 𝔽) :
    Matrix (I → 𝔽) (I → 𝔽) ℂ :=
  fun x x' => ((2:ℂ)^(Fintype.card I + Fintype.card J))⁻¹ *
    ∑ y : J → 𝔽, (amp (assembled L R B) (Sum.elim x y) : ℂ) *
        star (amp (assembled L R B) (Sum.elim x' y) : ℂ)
private theorem graph_cut_density (L : Matrix I I 𝔽) (R : Matrix J J 𝔽) (B : Matrix J I 𝔽) :
    graphCutReduction L R B = cutDensity B (quadratic L) (quadratic R) := by
  ext x z
  simp only [graphCutReduction,graph_amp_cut,cutDensity,Matrix.smul_apply,smul_eq_mul,mul_apply,
    conjTranspose_apply]
private theorem graph_cut_trace_one_and_flat_polynomial
    (L : Matrix I I 𝔽) (R : Matrix J J 𝔽) (B : Matrix J I 𝔽) :
    (graphCutReduction L R B).trace = 1 ∧
    graphCutReduction L R B * graphCutReduction L R B =
      ((2:ℂ)^B.rank)⁻¹ • graphCutReduction L R B := by
  rw [graph_cut_density]
  exact ⟨cutDensity_trace _ _ _,cutDensity_square _ _ _⟩
end
section
variable {I : Type*} [Fintype I]
private abbrev Carrier (I : Type*) := I → 𝔽 × 𝔽
private def graph (A : Matrix I I 𝔽) (x : I → 𝔽) : Carrier I :=
  fun i => (x i,(A *ᵥ x) i)
private def eraseOn [DecidableEq I] (s : Finset I) : Carrier I →ₗ[𝔽] Carrier I where
  toFun v i := if i ∈ s then 0 else v i
  map_add' _ _ := by ext i <;> by_cases hi : i ∈ s <;> simp [hi]
  map_smul' _ _ := by ext i <;> by_cases hi : i ∈ s <;> simp [hi]
omit [Fintype I] in
@[simp] private theorem eraseOn_apply [DecidableEq I] (s : Finset I) (v : Carrier I) (i : I) :
    eraseOn s v i = if i ∈ s then 0 else v i := rfl
end
section
open scoped Classical
variable {I : Type*} [Fintype I]
private def support (W : Submodule 𝔽 (Carrier I)) (U : Finset I) : Submodule 𝔽 (Carrier I) :=
  W ⊓ (eraseOn U).ker
omit [Fintype I] in
private theorem mem_support (W : Submodule 𝔽 (Carrier I)) (U : Finset I) (v : Carrier I) :
    v ∈ support W U ↔ v ∈ W ∧ ∀ i ∉ U, v i = 0 := by
  constructor
  · rintro ⟨hw,hz⟩
    refine ⟨hw,fun i hi => ?_⟩
    exact (by simpa [hi] using congrFun (LinearMap.mem_ker.mp hz) i)
  · rintro ⟨hw,hz⟩
    refine ⟨hw,LinearMap.mem_ker.mpr ?_⟩
    funext i
    by_cases hi : i ∈ U <;> simp [hi,hz]
omit [Fintype I] in
private theorem support_inf (W : Submodule 𝔽 (Carrier I)) (A B : Finset I) :
    support W A ⊓ support W B = support W (A ∩ B) := by
  ext v
  simp only [Submodule.mem_inf,mem_support]
  constructor
  · rintro ⟨⟨hW,hA⟩,⟨_,hB⟩⟩
    refine ⟨hW,fun i hi => ?_⟩
    by_cases ia : i ∈ A
    · exact hB i (fun ib => hi (Finset.mem_inter.mpr ⟨ia,ib⟩))
    · exact hA i ia
  · rintro ⟨hW,h⟩
    exact ⟨⟨hW,fun i hi => h i (fun e => hi (Finset.mem_inter.mp e).1)⟩,
      ⟨hW,fun i hi => h i (fun e => hi (Finset.mem_inter.mp e).2)⟩⟩
omit [Fintype I] in
private theorem support_mono (W : Submodule 𝔽 (Carrier I)) {A B : Finset I} (h : A ⊆ B) :
    support W A ≤ support W B := by
  intro v hv
  obtain ⟨hw,hz⟩ := (mem_support W A v).mp hv
  exact (mem_support W B v).mpr ⟨hw,fun i hi => hz i (fun e => hi (h e))⟩
private theorem support_dim_supermod (W : Submodule 𝔽 (Carrier I)) (A B : Finset I) :
    Module.finrank 𝔽 (support W A) + Module.finrank 𝔽 (support W B) ≤
      Module.finrank 𝔽 (support W (A ∩ B)) + Module.finrank 𝔽 (support W (A ∪ B)) := by
  have hs : support W A ⊔ support W B ≤ support W (A ∪ B) :=
    sup_le (support_mono W Finset.subset_union_left) (support_mono W Finset.subset_union_right)
  have h := (support W A).finrank_sup_add_finrank_inf_eq (support W B)
  rw [support_inf] at h
  have hr := Submodule.finrank_mono hs
  omega
private def hcut (W : Submodule 𝔽 (Carrier I)) (U : Finset I) : ℝ :=
  (U.card : ℝ) - Module.finrank 𝔽 (support W U)
private theorem hcut_submod (W : Submodule 𝔽 (Carrier I)) (A B : Finset I) :
    hcut W (A ∩ B) + hcut W (A ∪ B) ≤ hcut W A + hcut W B := by
  have hr := support_dim_supermod W A B
  have hc := Finset.card_union_add_card_inter A B
  have r : (Module.finrank 𝔽 (support W A) : ℝ) + Module.finrank 𝔽 (support W B) ≤
    (Module.finrank 𝔽 (support W (A ∩ B)) : ℝ) +
      Module.finrank 𝔽 (support W (A ∪ B)) := by exact_mod_cast hr
  have c : ((A ∪ B).card : ℝ) + (A ∩ B).card = (A.card : ℝ) + B.card := by exact_mod_cast hc
  unfold hcut
  linarith
private def moment (W : Submodule 𝔽 (Carrier I)) (K : ℝ) (U : Finset I) : ℝ :=
  (2 : ℝ) ^ ((1-K)*hcut W U)
omit [Fintype I] in
private theorem moment_pos (W : Submodule 𝔽 (Carrier I)) (K : ℝ) (U : Finset I) :
    0 < moment W K U := Real.rpow_pos_of_pos (by norm_num) _
private theorem moment_supermod (W : Submodule 𝔽 (Carrier I)) (K : ℝ) (hK : 1 < K) (A B : Finset I) :
    moment W K A * moment W K B ≤ moment W K (A ∩ B) * moment W K (A ∪ B) := by
  unfold moment
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2), ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [← mul_add, ← mul_add]
  exact mul_le_mul_of_nonpos_left (hcut_submod W A B) (by linarith)
end
section
open scoped Classical
variable {I : Type*} [Fintype I]
def cutMatrix (A : Matrix I I 𝔽) (U V : Finset I) : Matrix V U 𝔽 :=
  fun v u => A v.val u.val
private def extend (U : Finset I) : (U → 𝔽) →ₗ[𝔽] (I → 𝔽) where
  toFun x i := if h : i ∈ U then x ⟨i,h⟩ else 0
  map_add' _ _ := by funext i; by_cases h : i ∈ U <;> simp [h]
  map_smul' _ _ := by funext i; by_cases h : i ∈ U <;> simp [h]
omit [Fintype I] in
@[simp] private theorem extend_mem (U : Finset I) (x : U → 𝔽) (i : U) :
    extend U x i.val = x i := by simp [extend,i.property]
omit [Fintype I] in
@[simp] private theorem extend_out (U : Finset I) (x : U → 𝔽) (i : I) (h : i ∉ U) :
    extend U x i = 0 := by simp [extend,h]
omit [Fintype I] in
private theorem restrict_extend (U : Finset I) (x : I → 𝔽) (h : ∀ i ∉ U, x i = 0) :
    extend U (fun i : U => x i.val) = x := by
  funext i
  by_cases hi : i ∈ U
  · exact extend_mem U _ ⟨i,hi⟩
  · rw [extend_out U _ i hi,h i hi]
private theorem cut_apply (A : Matrix I I 𝔽) (U V : Finset I) (x : U → 𝔽) (v : V) :
    (cutMatrix A U V *ᵥ x) v = (A *ᵥ extend U x) v.val := by
  change (∑ u : U, A v.val u.val * x u) = ∑ i : I, A v.val i * extend U x i
  let f (i : I) := A v.val i * extend U x i
  have hs : (∑ u : U, f u.val) = ∑ i ∈ U, f i := (Finset.sum_subtype U (fun _ => Iff.rfl) f).symm
  have ht : (∑ i ∈ U, f i) = ∑ i : I, f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ h
    simp [f,extend_out U _ _ h]
  simpa [f] using hs.trans ht
private def graphLin (A : Matrix I I 𝔽) : (I → 𝔽) →ₗ[𝔽] Carrier I :=
  LinearMap.pi (fun i => (LinearMap.proj i).prod ((LinearMap.proj i).comp A.mulVecLin))
private def firstRest (W : Submodule 𝔽 (Carrier I)) (U : Finset I) :
    support W U →ₗ[𝔽] (U → 𝔽) :=
  (LinearMap.pi fun i : U => (LinearMap.fst 𝔽 𝔽 𝔽).comp (LinearMap.proj i.val)).comp (support W U).subtype
private def supportEquiv (A : Matrix I I 𝔽) (W : Submodule 𝔽 (Carrier I))
    (hW : ∀ v, v ∈ W ↔ ∃ x, graph A x = v) (U : Finset I) :
    (cutMatrix A U (Finset.univ \ U)).mulVecLin.ker ≃ₗ[𝔽] support W U where
  toFun x := ⟨graphLin A (extend U x.val),(mem_support W U _).mpr ⟨(hW _).mpr ⟨_,rfl⟩,fun i hi => by
    let c : (Finset.univ \ U : Finset I) := ⟨i,by simp [hi]⟩
    have hz := congrFun (LinearMap.mem_ker.mp x.property) c
    change (cutMatrix A U (Finset.univ \ U) *ᵥ x.val) c = 0 at hz
    rw [cut_apply] at hz
    change (extend U x.val i,(A *ᵥ extend U x.val) i) = 0
    simp [extend_out U x.val i hi,show (A *ᵥ extend U x.val) i = 0 from hz]⟩⟩
  invFun v := ⟨firstRest W U v, LinearMap.mem_ker.mpr (by
    obtain ⟨h,hOut⟩ := (mem_support W U v.val).mp v.property
    obtain ⟨x,hx⟩ := (hW _).mp h
    have hre : extend U (firstRest W U v) = x := by
      change extend U (fun i : U => (v.val i.val).1) = x
      rw [← hx]
      apply restrict_extend
      intro i hi
      exact congrArg Prod.fst ((congrFun hx i).trans (hOut i hi))
    funext i
    change (cutMatrix A U _ *ᵥ firstRest W U v) i = 0
    rw [cut_apply,hre]
    exact congrArg Prod.snd ((congrFun hx i.val).trans
      (hOut i.val (Finset.mem_sdiff.mp i.property).2)))⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact extend_mem U x.val i
  right_inv v := by
    apply Subtype.ext
    obtain ⟨h,hOut⟩ := (mem_support W U v.val).mp v.property
    obtain ⟨x,hx⟩ := (hW _).mp h
    change graph A (extend U (fun i : U => (v.val i.val).1)) = v.val
    rw [← hx]
    congr 1
    apply restrict_extend
    intro i hi
    exact congrArg Prod.fst ((congrFun hx i).trans (hOut i hi))
  map_add' x y := by
    apply Subtype.ext
    change graphLin A (extend U (x.val+y.val)) = _
    rw [map_add,map_add]
    rfl
  map_smul' b x := by
    apply Subtype.ext
    change graphLin A (extend U (b • x.val)) = _
    rw [map_smul,map_smul]
    rfl
private theorem hcut_eq_rank (A : Matrix I I 𝔽) (W : Submodule 𝔽 (Carrier I))
    (hW : ∀ v, v ∈ W ↔ ∃ x, graph A x = v) (U : Finset I) :
    hcut W U = ((cutMatrix A U (Finset.univ \ U)).rank : ℝ) := by
  let B := cutMatrix A U (Finset.univ \ U)
  have d := B.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at d
  have hcard : Fintype.card U = U.card := Fintype.card_coe U
  have hdim := (supportEquiv A W hW U).finrank_eq
  change Module.finrank 𝔽 B.mulVecLin.ker = _ at hdim
  have hr : Module.finrank 𝔽 B.mulVecLin.range = B.rank := by
    rfl
  have dd : (B.rank : ℝ) + Module.finrank 𝔽 (support W U) = (U.card : ℝ) := by
    exact_mod_cast (by simpa only [hr,hdim,hcard] using d : B.rank + Module.finrank 𝔽 (support W U) = U.card)
  unfold hcut
  change _ = (B.rank : ℝ)
  linarith
private theorem hcut_symmetric_graph (A : Matrix I I 𝔽) (hs : A.transpose = A)
    (W : Submodule 𝔽 (Carrier I)) (hW : ∀ v, v ∈ W ↔ ∃ x, graph A x = v)
    (U : Finset I) : hcut W (Finset.univ \ U) = hcut W U := by
  rw [hcut_eq_rank A W hW, hcut_eq_rank A W hW, Finset.sdiff_sdiff_eq_self (Finset.subset_univ U)]
  have ht : (cutMatrix A U (Finset.univ \ U)).transpose = cutMatrix A (Finset.univ \ U) U := by
    ext i j
    exact congrFun (congrFun hs i.val) j.val
  rw [← ht, Matrix.rank_transpose]
end
section
variable {I : Type*} [Fintype I]
private theorem antitone_moment (W : Submodule 𝔽 (Carrier I)) (K : ℝ)
    (hK : 1 < K) (hSym : ∀ U, hcut W (Finset.univ \ U) = hcut W U) :
    Antitone (Objective (moment W K)) := by
  apply objective_antitone (moment W K)
  · intro s; exact (moment_pos W K s).le
  · exact moment_pos W K ∅
  · intro s; simp only [moment,hSym]
  · exact moment_supermod W K hK
end
section
open scoped Classical
variable {I : Type*} [Fintype I]
private theorem graphLabel_range (A : Matrix I I 𝔽) (v : Carrier I) :
    v ∈ (graphLin A).range ↔ ∃ x, graph A x = v := Iff.rfl
private def graphMoment (A : Matrix I I 𝔽) (K : ℝ) (U : Finset I) : ℝ :=
  (2:ℝ) ^ ((1-K) * (cutMatrix A U (Finset.univ \ U)).rank)
private theorem graphMoment_label (A : Matrix I I 𝔽) (K : ℝ) (U : Finset I) :
    graphMoment A K U = moment (graphLin A).range K U := by
  unfold graphMoment moment
  rw [hcut_eq_rank A _ (graphLabel_range A)]
private theorem graphMoment_average_antitone (A : Matrix I I 𝔽) (hA : A.transpose = A)
    (K : ℝ) (hK : 1 < K) : Antitone (Objective (graphMoment A K)) := by
  have h : graphMoment A K = moment (graphLin A).range K := funext (graphMoment_label A K)
  rw [h]
  apply antitone_moment _ K hK
  exact hcut_symmetric_graph A hA _ (graphLabel_range A)
end
section
open scoped Classical
variable {I : Type*} [Fintype I] [LinearOrder I]
private def partitionEquiv (U : Finset I) : (U ⊕ ↥(Finset.univ \ U)) ≃ I :=
  (Equiv.sumCongr (Equiv.refl ↥U)
    (Equiv.subtypeEquivRight (fun x => by simp [Finset.mem_sdiff]))).trans
    (Equiv.sumCompl (fun x => x ∈ U))
@[simp] private theorem partition_inl (U : Finset I) (u : U) :
    partitionEquiv U (.inl u) = u.val := by simp [partitionEquiv]
@[simp] private theorem partition_inr (U : Finset I) (v : (Finset.univ \ U : Finset I)) :
    partitionEquiv U (.inr v) = v.val := by simp [partitionEquiv]
private def together (U : Finset I) (x : U → 𝔽) (y : (Finset.univ \ U : Finset I) → 𝔽) :
    I → 𝔽 := Sum.elim x y ∘ (partitionEquiv U).symm
private def pullMatrix {T : Type*} (e : T ≃ I) (A : Matrix I I 𝔽) : Matrix T T 𝔽 :=
  fun i j => A (e i) (e j)
omit [LinearOrder I] in
private theorem quadratic_pull {T : Type*} [Fintype T] (e : T ≃ I)
    (A : Matrix I I 𝔽) (z : T → 𝔽) :
    quadratic A (z ∘ e.symm) = quadratic (pullMatrix e A) z := by
  unfold quadratic bilin pullMatrix
  have h (i : T) :
      (∑ j : T,A (e i) (e j) * z i * z j) =
        ∑ j : I, A (e i) j * z i * z (e.symm j) := by
    have ht := Equiv.sum_comp e (fun j : I => A (e i) j * z i * z (e.symm j))
    simpa using ht
  let f (i : I) := ∑ j : I,A i j * z (e.symm i) * z (e.symm j)
  have hf := Equiv.sum_comp e f
  simp only [h]
  simpa [f,Function.comp_apply] using hf.symm
private theorem cross_pulled_is_matrix (A : Matrix I I 𝔽) (hs : ∀ i j, A i j = A j i)
    (hd : ∀ i, A i i = 0) (U : Finset I) :
    crossBlock (pullMatrix (partitionEquiv U) (graphUpper A)) =
      cutMatrix A U (Finset.univ \ U) := by
  ext j i
  simp only [crossBlock,pullMatrix,partition_inl,partition_inr,cutMatrix]
  exact (graph_matrix_recovered A hs hd i.val j.val).trans (hs _ _)
def physicalGraphReduction (A : Matrix I I 𝔽) (U : Finset I) : Matrix (U → 𝔽) (U → 𝔽) ℂ :=
  fun x x' => ((2:ℂ)^Fintype.card I)⁻¹ *
    ∑ y : (Finset.univ \ U : Finset I) → 𝔽,
      (amp (graphUpper A) (together U x y) : ℂ) *
        star (amp (graphUpper A) (together U x' y) : ℂ)
/-- Actual normalized graph-state reduction rewritten into a single cross cut. -/
private theorem physicalGraphReduction_eq (A : Matrix I I 𝔽) (U : Finset I) :
    let W := pullMatrix (partitionEquiv U) (graphUpper A)
    physicalGraphReduction A U = graphCutReduction (leftBlock W) (rightBlock W) (crossBlock W) := by
  let W := pullMatrix (partitionEquiv U) (graphUpper A)
  change physicalGraphReduction A U = graphCutReduction (leftBlock W) (rightBlock W) (crossBlock W)
  have hcard := Fintype.card_congr (partitionEquiv U)
  rw [Fintype.card_sum] at hcard
  have h (x : U → 𝔽) (y : (Finset.univ \ U : Finset I) → 𝔽) :
      amp (graphUpper A) (together U x y) =
      amp (assembled (leftBlock W) (rightBlock W) (crossBlock W)) (Sum.elim x y) := by
    unfold amp together
    rw [quadratic_pull]
    change signBit (quadratic W (Sum.elim x y)) = _
    rw [arbitrary_phase_cut W,quadratic_cut]
  ext x z
  simp only [physicalGraphReduction,graphCutReduction,h,hcard]
  congr 2
  ext k
  simp
/-- A literal reduction from the actual signed graph-state amplitudes has unit
trace and the cut-rank flat-projector equation, for arbitrary subsystem. -/
private theorem physicalGraphReduction_flat (A : Matrix I I 𝔽) (hs : ∀ i j, A i j = A j i)
    (hd : ∀ i, A i i = 0) (U : Finset I) :
    (physicalGraphReduction A U).trace = 1 ∧
    physicalGraphReduction A U * physicalGraphReduction A U =
      ((2:ℂ)^(cutMatrix A U (Finset.univ \ U)).rank)⁻¹ • physicalGraphReduction A U := by
  let W := pullMatrix (partitionEquiv U) (graphUpper A)
  have eq : physicalGraphReduction A U = graphCutReduction (leftBlock W) (rightBlock W) (crossBlock W) :=
    physicalGraphReduction_eq A U
  have eqB : crossBlock W = cutMatrix A U (Finset.univ \ U) :=
    cross_pulled_is_matrix A hs hd U
  rw [eq,← eqB]
  convert graph_cut_trace_one_and_flat_polynomial (leftBlock W) (rightBlock W) (crossBlock W) using 2 <;> congr 2 <;> exact Subsingleton.elim _ _
end
section
open Matrix
open scoped ComplexOrder Classical
private theorem cutDensity_psd {I J : Type*} [Fintype I] [Fintype J] (B : Matrix J I 𝔽)
    (u : (I → 𝔽) → 𝔽) (v : (J → 𝔽) → 𝔽) :
    (cutDensity B u v).PosSemidef := by
  unfold cutDensity
  refine (Matrix.posSemidef_self_mul_conjTranspose _).smul ?_
  rw [← Complex.ofReal_ofNat 2,← Complex.ofReal_pow,← Complex.ofReal_inv]
  exact Complex.zero_le_real.mpr (by positivity)
end
section
private theorem scaled_rpow_pointwise {c x K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hx : x = 0 ∨ x = c) :
    x ^ K = c ^ (K - 1) * x := by
  rcases hx with rfl | hx
  · simp [Real.zero_rpow hK.ne']
  · subst x
    calc
      c ^ K = c ^ ((K - 1) + 1) := by rw [sub_add_cancel]
      _ = c ^ (K - 1) * c := by rw [Real.rpow_add hc,Real.rpow_one]
end
section
variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A]
  [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
private theorem spectrum_of_scaled_idempotent {a : A} (ha : IsSelfAdjoint a)
    {c : ℝ} (hp : a * a = c • a) :
    ∀ x ∈ spectrum ℝ a, x = 0 ∨ x = c := by
  have hcf : cfc (fun x : ℝ => x ^ 2) a = cfc (fun x : ℝ => c * x) a := by
    rw [cfc_pow_id a 2 ha, cfc_const_mul_id c a ha,pow_two,hp]
  have hpt := eqOn_of_cfc_eq_cfc hcf (by fun_prop) (by fun_prop) ha
  intro x hx
  have hh : x ^ 2 = c * x := hpt hx
  have hz : x * (x - c) = 0 := by
    rw [mul_sub,← pow_two,mul_comm x c,hh,sub_self]
  exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp
end
section
variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]
private theorem cfc_rpow_of_two_spectrum {a : A} (ha : 0 ≤ a)
    {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (he : ∀ x ∈ spectrum ℝ a, x = 0 ∨ x = c) :
    CFC.rpow a K = (c ^ (K - 1)) • a := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ha]
  calc
    _ = cfc (fun x : ℝ => c ^ (K - 1) * x) a :=
      cfc_congr (fun x hx => scaled_rpow_pointwise hc hK (he x hx))
    _ = _ := cfc_const_mul_id _ _ ha.isSelfAdjoint
private theorem cfc_rpow_of_scaled_idempotent {a : A} (ha : 0 ≤ a)
    {c K : ℝ} (hc : 0 < c) (hK : 0 < K) (hp : a * a = c • a) :
    CFC.rpow a K = (c ^ (K - 1)) • a :=
  cfc_rpow_of_two_spectrum ha hc hK (spectrum_of_scaled_idempotent ha.isSelfAdjoint hp)
end
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The same exact CFC moment directly from a scaled-idempotent identity;
neither a basis construction nor a separate eigenvalue enumeration is needed. -/
private theorem trace_rpow_of_scaled_projection {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hp : ρ * ρ = c • ρ) (ht : ρ.trace = 1) :
    (trace (ρ ^ K)).re = c ^ (K - 1) := by
  rw [show ρ ^ K = (c ^ (K - 1)) • ρ from
    cfc_rpow_of_scaled_idempotent hρ.nonneg hc hK hp,
    trace_smul, ht, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one]
end
section
open Matrix
open scoped ComplexOrder Classical MatrixOrder
variable {I : Type*} [Fintype I] [LinearOrder I]
private theorem graphReduction_psd (A : Matrix I I 𝔽) (U : Finset I) :
    (physicalGraphReduction A U).PosSemidef := by
  rw [physicalGraphReduction_eq,graph_cut_density]
  exact cutDensity_psd _ _ _
private theorem graphReduction_moment (A : Matrix I I 𝔽)
    (hs : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 0)
    (K : ℝ) (hK : 0 < K) (U : Finset I) :
    (trace (physicalGraphReduction A U ^ K)).re = graphMoment A K U := by
  obtain ⟨ht,hp⟩ := physicalGraphReduction_flat A hs hd U
  let r := (cutMatrix A U (Finset.univ \ U)).rank
  have hpos : 0 < ((2:ℝ)^r)⁻¹ := by positivity
  have hp' : physicalGraphReduction A U * physicalGraphReduction A U =
      (((2:ℝ)^r)⁻¹ : ℝ) • physicalGraphReduction A U := by
    convert hp using 1
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_pow, Complex.ofReal_ofNat, smul_eq_mul, r]
  rw [trace_rpow_of_scaled_projection (graphReduction_psd A U) hpos hK hp' ht]
  unfold graphMoment
  calc
    (((2:ℝ)^r)⁻¹ : ℝ) ^ (K-1) = (2:ℝ)^((1-K)*(r:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring
    _ = _ := by
      dsimp only [r]
      congr 6 <;> first | (congr 1; exact Subsingleton.elim _ _) | (funext x; simp [Finset.mem_sdiff])
/-- Site-set complement in the finite graph. -/
def complement {I : Type*} [Fintype I] (U : Finset I) : Finset I := Finset.univ \ U
/-- Binary cut rank of the original graph, separating U from its complement. -/
def cutRank {I : Type*} [Fintype I] (A : Matrix I I (ZMod 2))
    (U : Finset I) : ℕ :=
  (cutMatrix A U (complement U)).rank
/-- The exact real power trace of every actual graph-state reduction. -/
def graphTraceMoment {I : Type*} [Fintype I] [LinearOrder I] (A : Matrix I I (ZMod 2))
    (K : ℝ) (S : Finset I) : ℝ :=
  (trace (physicalGraphReduction A S ^ K)).re
/-- GCE of a graph state after its exact subsystem trace moment is read out. -/
def fromTraceMoments {I : Type*} [DecidableEq I] (K : ℝ)
    (w : Finset I → ℝ) (S : Finset I) : ℝ :=
  (1 - Objective w S) / (K - 1)
/-- The same actual reduced-matrix moments yield the exact cut-rank formula
and generalized concentratable entanglement monotone under inclusion. -/
theorem physical_graph_gce_monotone (N : ℕ) (K : ℝ) (A : Matrix (Fin N) (Fin N) 𝔽)
    (hs : ∀ i j, A i j = A j i) (hd : ∀ i, A i i = 0) (hK : 1 < K) :
    let observed := graphTraceMoment A K
    (∀ U, observed U = (2 : ℝ) ^ ((1 - K) * cutRank A U)) ∧
      Monotone (fromTraceMoments K observed) := by
  have h : graphTraceMoment A K = graphMoment A K :=
    funext (graphReduction_moment A hs hd K (by linarith))
  have hA : A.transpose = A := by ext i j; exact hs _ _
  constructor
  · intro U
    rw [h]
    rfl
  · rw [h]
    intro a b hab
    exact div_le_div_of_nonneg_right
      (sub_le_sub_left (graphMoment_average_antitone A hA K hK hab) 1)
      (sub_nonneg.mpr hK.le)
end
end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
