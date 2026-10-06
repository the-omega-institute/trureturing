/- GID: D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/BinaryStabilizerGraphNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pauli stabilizer eigenlines are local-unitary images of binary graph amplitudes. -/

/-
proof_shape: chi2, weyl, unique_weyl_line_lagrangian: bind-only, consumed helpers.
escape_witness: none.
admission_basis: open-problem-resolution (#13575, consumed helper of the settlement).
Direct frozen dependencies: BinaryLagrangianGraphForm.sp; declaration identities below.
-/

import D5.S3.Quantum.Information.BinaryLagrangianGraphForm
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

open scoped BigOperators
open D5.S3.Quantum.FiniteDimensional
open Matrix D5.S3.Quantum.Information.BinaryLagrangianGraphForm
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

noncomputable section

namespace D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm

local notation "V" N:max => (Fin N → ZMod 2)
local notation "E" N:max => ((V N) × (V N))

private def chi2 (t : ZMod 2) : ℂ :=
  AddChar.zmodChar 2 (by norm_num : (-1 : ℂ) ^ 2 = 1) t

private lemma chi2_eq (t : ZMod 2) : chi2 t = if t = 0 then 1 else -1 := by
  have ht : t = 0 ∨ t = 1 := (show ∀ t : ZMod 2, t = 0 ∨ t = 1 from by decide) t
  rcases ht with rfl | rfl
  · change (-1 : ℂ) ^ 0 = if (0 : ZMod 2) = 0 then 1 else -1
    norm_num
  · change (-1 : ℂ) ^ 1 = if (1 : ZMod 2) = 0 then 1 else -1
    norm_num

private lemma chi2_add (a b : ZMod 2) : chi2 (a + b) = chi2 a * chi2 b :=
  AddChar.map_add_eq_mul _ a b

private lemma chi2_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    chi2 (∑ i ∈ s, f i) = ∏ i ∈ s, chi2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi2_eq]
  | @insert i s hi ih => simp [Finset.sum_insert hi, Finset.prod_insert hi, chi2_add, ih]

/-- The Weyl operator `X^x Z^z` on functions on the binary configuration space. -/
private def weyl {N : ℕ} (v : E N) (f : V N → ℂ) : V N → ℂ :=
  fun t => chi2 (∑ i, v.2 i * (t i + v.1 i)) * f (t + v.1)

private lemma chi2_laws : chi2 0 = 1 ∧
    (∀ a b, chi2 (a + b) = chi2 a * chi2 b) ∧
    (∀ a, chi2 a * chi2 a = 1) ∧ (∀ a, chi2 a ≠ 0) ∧
    (∀ a, chi2 a = 1 ↔ a = 0) := by
  have cases₂ : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  refine ⟨by simp [chi2_eq], ?_, ?_, ?_, ?_⟩
  · exact chi2_add
  · intro a
    rcases cases₂ a with rfl | rfl <;> norm_num [chi2_eq]
  · intro a
    rcases cases₂ a with rfl | rfl <;> norm_num [chi2_eq]
  · intro a
    rcases cases₂ a with rfl | rfl <;> norm_num [chi2_eq]
private lemma sp_bilinear {N : ℕ} :
    (∀ u v w : E N, sp (u + v) w = sp u w + sp v w) ∧
    (∀ (a : ZMod 2) (u w : E N), sp (a • u) w = a • sp u w) ∧
    (∀ u v w : E N, sp u (v + w) = sp u v + sp u w) ∧
    (∀ (a : ZMod 2) (u w : E N), sp u (a • w) = a • sp u w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v w
    simp only [sp, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro a u w
    simp only [sp, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro u v w
    simp only [sp, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro a u w
    simp only [sp, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
private def spForm (N : ℕ) : LinearMap.BilinForm (ZMod 2) (E N) :=
  LinearMap.mk₂ (ZMod 2) sp sp_bilinear.1 sp_bilinear.2.1
    sp_bilinear.2.2.1 sp_bilinear.2.2.2
private lemma sp_alt (N : ℕ) : (spForm N).IsAlt := by
  intro u
  change sp u u = 0
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm (u.2 i) (u.1 i)]
  exact CharTwo.add_self_eq_zero _
private lemma sp_nondegenerate (N : ℕ) : (spForm N).Nondegenerate := by
  classical
  apply (sp_alt N).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro u hu
  apply Prod.ext
  · funext i
    have h := hu (0, Pi.single i 1)
    change sp u (0, Pi.single i 1) = 0 at h
    simpa [sp, Pi.single_apply, mul_ite] using h
  · funext i
    have h := hu (Pi.single i 1, 0)
    change sp u (Pi.single i 1, 0) = 0 at h
    simpa [sp, Pi.single_apply, mul_ite] using h
private lemma weyl_linear {N : ℕ} (u : E N) :
    (∀ f g, weyl u (f + g) = weyl u f + weyl u g) ∧
    (∀ (a : ℂ) f, weyl u (a • f) = a • weyl u f) ∧ weyl u 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g
    funext t
    simp [weyl, mul_add]
  · intro a f
    funext t
    simp [weyl, mul_left_comm]
  · funext t
    simp [weyl]
private lemma weyl_mul {N : ℕ} (u w : E N) (f : V N → ℂ) :
    weyl u (weyl w f) = chi2 (∑ i, u.2 i * w.1 i) • weyl (u + w) f := by
  funext t
  simp only [weyl, Pi.add_apply, Prod.fst_add, Prod.snd_add, Pi.smul_apply,
    smul_eq_mul, add_assoc]
  rw [← mul_assoc, ← mul_assoc, ← chi2_laws.2.1, ← chi2_laws.2.1]
  congr 1
  apply congrArg chi2
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = u.2 i * w.1 i + (u.2 i + w.2 i) * (t i + (u.1 i + w.1 i)) -
        (u.2 i * w.1 i + u.2 i * w.1 i) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, sub_zero]
private lemma weyl_square {N : ℕ} (u : E N) (f : V N → ℂ) :
    weyl u (weyl u f) = chi2 (∑ i, u.1 i * u.2 i) • f := by
  rw [weyl_mul]
  have hz : u + u = 0 := by
    apply Prod.ext <;> funext i <;> exact CharTwo.add_self_eq_zero _
  have hzero : weyl (0 : E N) f = f := by
    funext t
    simp [weyl, chi2_laws.1]
  rw [hz, hzero]
  congr 2
  exact Finset.sum_congr rfl (fun i _ => mul_comm (u.2 i) (u.1 i))
private lemma weyl_injective {N : ℕ} (u : E N) : Function.Injective (weyl u) := by
  intro f g hfg
  have h := congrArg (weyl u) hfg
  rw [weyl_square, weyl_square] at h
  exact smul_right_injective (V N → ℂ) (chi2_laws.2.2.2.1 _) h
private lemma weyl_commute {N : ℕ} (u w : E N) (f : V N → ℂ) :
    weyl u (weyl w f) = chi2 (sp u w) • weyl w (weyl u f) := by
  rw [weyl_mul, weyl_mul, add_comm w u, smul_smul]
  congr 1
  have h : (∑ i, w.2 i * u.1 i) = ∑ i, u.1 i * w.2 i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [sp, Finset.sum_add_distrib, h, chi2_laws.2.1]
  symm
  calc
    _ = (chi2 (∑ i, u.1 i * w.2 i) * chi2 (∑ i, u.1 i * w.2 i)) *
        chi2 (∑ i, u.2 i * w.1 i) := by ring
    _ = _ := by rw [chi2_laws.2.2.1, one_mul]
private lemma eigen_pair_orthogonal {N : ℕ} {ψ : V N → ℂ} (hne : ψ ≠ 0)
    {u w : E N} {a b : ℂ} (hu : weyl u ψ = a • ψ) (hw : weyl w ψ = b • ψ) :
    sp u w = 0 := by
  have hn : weyl w (weyl u ψ) ≠ 0 := by
    intro h
    have hz : weyl u ψ = 0 :=
      weyl_injective w (h.trans (weyl_linear w).2.2.symm)
    exact hne (weyl_injective u (hz.trans (weyl_linear u).2.2.symm))
  have hc : weyl u (weyl w ψ) = weyl w (weyl u ψ) := by
    rw [hw, (weyl_linear u).2.1, hu, (weyl_linear w).2.1, hw,
      smul_smul, smul_smul, mul_comm]
  have h := weyl_commute u w ψ
  rw [hc] at h
  have hχ : (1 : ℂ) = chi2 (sp u w) :=
    smul_left_injective ℂ hn (by simpa only [one_smul] using h)
  exact (chi2_laws.2.2.2.2 _).mp hχ.symm
private lemma generator_data {N : ℕ} {ψ : V N → ℂ} (hne : ψ ≠ 0)
    {u : E N} {c : ℂ} (h : c • weyl u ψ = ψ) :
    c ≠ 0 ∧ c ^ 2 = chi2 (∑ i, u.1 i * u.2 i) ∧ weyl u ψ = c⁻¹ • ψ := by
  have hc : c ≠ 0 := by
    intro hc
    exact hne (by simpa only [hc, zero_smul] using h.symm)
  have he : weyl u ψ = c⁻¹ • ψ := by
    have hh := congrArg (fun f : V N → ℂ => c⁻¹ • f) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh
  have hh := congrArg (fun f : V N → ℂ => c • weyl u f) h
  rw [(weyl_linear u).2.1, weyl_square] at hh
  simp only [smul_smul, h] at hh
  have hp : (c * c) * chi2 (∑ i, u.1 i * u.2 i) = 1 :=
    smul_left_injective ℂ hne (by simpa only [one_smul, mul_assoc] using hh)
  refine ⟨hc, ?_, he⟩
  calc
    c ^ 2 = ((c * c) * chi2 (∑ i, u.1 i * u.2 i)) *
        chi2 (∑ i, u.1 i * u.2 i) := by
      rw [mul_assoc, chi2_laws.2.2.1, mul_one, pow_two]
    _ = _ := by rw [hp, one_mul]
private lemma eigen_orthogonal_iff {N k : ℕ}
    (v : Fin k → E N) (c : Fin k → ℂ) (ψ : V N → ℂ) (hne : ψ ≠ 0)
    (hline : ∀ w : V N → ℂ,
      (∀ j, c j • weyl (v j) w = w) ↔ ∃ a : ℂ, w = a • ψ)
    (u : E N) :
    (∃ a : ℂ, weyl u ψ = a • ψ) ↔
      u ∈ (spForm N).orthogonal (Submodule.span (ZMod 2) (Set.range v)) := by
  have hψ : ∀ j, c j • weyl (v j) ψ = ψ :=
    (hline ψ).mpr ⟨1, (one_smul ℂ ψ).symm⟩
  constructor
  · rintro ⟨a, ha⟩
    intro w hw
    change sp w u = 0
    refine Submodule.span_induction (p := fun w _ => sp w u = 0) ?_ ?_ ?_ ?_ hw
    · rintro w ⟨j, rfl⟩
      exact eigen_pair_orthogonal hne (generator_data hne (hψ j)).2.2 ha
    · simp [sp]
    · intro w z _ _ hw hz
      rw [sp_bilinear.1, hw, hz, add_zero]
    · intro a w _ hw
      rw [sp_bilinear.2.1, hw, smul_zero]
  · intro hu
    apply (hline (weyl u ψ)).mp
    intro j
    have hju := hu (v j) (Submodule.subset_span ⟨j, rfl⟩)
    change sp (v j) u = 0 at hju
    rw [weyl_commute, hju, chi2_laws.1, one_smul,
      ← (weyl_linear u).2.1, hψ j]

private theorem unique_weyl_line_lagrangian {N k : ℕ}
    (v : Fin k → E N) (c : Fin k → ℂ) (ψ : V N → ℂ)
    (hne : ψ ≠ 0)
    (hline : ∀ w : V N → ℂ,
      (∀ j, c j • weyl (v j) w = w) ↔ ∃ a : ℂ, w = a • ψ) :
    let L := Submodule.span (ZMod 2) (Set.range v)
    (∀ j, c j ^ 2 = chi2 (∑ i, (v j).1 i * (v j).2 i)) ∧
    (∀ u ∈ L, ∀ w ∈ L, sp u w = 0) ∧
    Module.finrank (ZMod 2) L = N ∧
    (∀ u : E N, (∃ a : ℂ, weyl u ψ = a • ψ) ↔ u ∈ L) := by
  classical
  let L := Submodule.span (ZMod 2) (Set.range v)
  change (∀ j, c j ^ 2 = chi2 (∑ i, (v j).1 i * (v j).2 i)) ∧
    (∀ u ∈ L, ∀ w ∈ L, sp u w = 0) ∧ Module.finrank (ZMod 2) L = N ∧
    (∀ u : E N, (∃ a : ℂ, weyl u ψ = a • ψ) ↔ u ∈ L)
  have hψ : ∀ j, c j • weyl (v j) ψ = ψ :=
    (hline ψ).mpr ⟨1, (one_smul ℂ ψ).symm⟩
  have hg := fun j => generator_data hne (hψ j)
  have hLO : L ≤ (spForm N).orthogonal L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact (eigen_orthogonal_iff v c ψ hne hline (v j)).mp ⟨(c j)⁻¹, (hg j).2.2⟩
  have hOO : (spForm N).orthogonal L ≤
      (spForm N).orthogonal ((spForm N).orthogonal L) := by
    intro u hu w hw
    obtain ⟨a, ha⟩ := (eigen_orthogonal_iff v c ψ hne hline w).mpr hw
    obtain ⟨b, hb⟩ := (eigen_orthogonal_iff v c ψ hne hline u).mpr hu
    exact eigen_pair_orthogonal hne ha hb
  have heq : (spForm N).orthogonal L = L := by
    rw [LinearMap.BilinForm.orthogonal_orthogonal (B := spForm N)
      (sp_nondegenerate N) (sp_alt N).isRefl L] at hOO
    exact le_antisymm hOO hLO
  refine ⟨fun j => (hg j).2.1, ?_, ?_, ?_⟩
  · intro u hu w hw
    exact hLO hw u hu
  · have hd := LinearMap.BilinForm.finrank_add_finrank_orthogonal (B := spForm N)
      (sp_alt N).isRefl L
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot (sp_nondegenerate N), inf_bot_eq,
      finrank_bot, add_zero, heq] at hd
    have hdim : Module.finrank (ZMod 2) (E N) = N + N := by
      simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin]
    rw [hdim] at hd
    omega
  · intro u
    rw [← heq]
    exact eigen_orthogonal_iff v c ψ hne hline u

private def binary (t : Fin 2) : ZMod 2 := t

private lemma binary_zero : binary 0 = 0 := rfl
private lemma binary_one : binary 1 = 1 := rfl
private lemma binary_self (t : ZMod 2) : binary t = t := rfl

private def wmat (a b : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun t s =>
    if binary s = binary t + a then chi2 (b * binary s) else 0

private lemma tensor_mul {N : ℕ} (A B : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorOp A * tensorOp B = tensorOp (fun i => A i * B i) := by
  ext x z
  simp only [tensorOp, Matrix.mul_apply, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

private lemma tensor_one {N : ℕ} :
    tensorOp (fun _ : Fin N => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  classical
  ext x y
  simp only [tensorOp, Matrix.of_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst y; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private lemma tensor_adj {N : ℕ} (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorOp A)ᴴ = tensorOp (fun i => (A i)ᴴ) := by
  ext x y
  simp [tensorOp, Matrix.conjTranspose_apply]

private lemma tensor_unitary {N : ℕ} (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ i, A i ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    tensorOp A ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (tensorOp A)ᴴ * tensorOp A = 1
  rw [tensor_adj, tensor_mul]
  have he : (fun i => (A i)ᴴ * A i) = fun _ => 1 :=
    funext fun i => Matrix.mem_unitaryGroup_iff'.mp (hA i)
  rw [he]
  exact tensor_one

private lemma tensor_smul {N : ℕ} (r : Fin N → ℂ)
    (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorOp (fun i => r i • A i) = (∏ i, r i) • tensorOp A := by
  ext x y
  simp [tensorOp, Finset.prod_mul_distrib]

private lemma tensor_weyl {N : ℕ} (v : E N) (f : V N → ℂ) :
    tensorOp (fun i => wmat (v.1 i) (v.2 i)) *ᵥ f = weyl v f := by
  classical
  let T : Matrix (V N) (V N) ℂ := tensorOp (fun i => wmat (v.1 i) (v.2 i))
  have entries (x y : V N) : T x y =
      if y = x + v.1 then chi2 (∑ i, v.2 i * y i) else 0 := by
    change (∏ i, if binary (y i) = binary (x i) + v.1 i then
      chi2 (v.2 i * binary (y i)) else 0) = _
    simp only [binary_self]
    by_cases h : y = x + v.1
    · subst y
      simp only [Pi.add_apply, ite_true]
      exact (chi2_sum Finset.univ _).symm
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  change T *ᵥ f = weyl v f
  funext t
  simp only [Matrix.mulVec, dotProduct, entries, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (t + v.1)]
  · simp [weyl]
  · intro b _ hb; simp [hb]
  · simp

private lemma pauli_wmat (p : Pauli) :
    ∃ a b : ZMod 2, ∃ r : ℂ, r ≠ 0 ∧ pauliMatrix p = r • wmat a b := by
  cases p
  · refine ⟨0, 0, 1, one_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;> norm_num [pauliMatrix, wmat, binary_zero, binary_one,
      CharTwo.add_self_eq_zero, chi2_eq]
  · refine ⟨1, 0, 1, one_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat, binary_zero, binary_one,
        CharTwo.add_self_eq_zero, chi2_eq, D5.S3.Quantum.FiniteDimensional.qubitX]
  · refine ⟨1, 1, Complex.I, Complex.I_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat, binary_zero, binary_one,
        CharTwo.add_self_eq_zero, chi2_eq, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨0, 1, 1, one_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat, binary_zero, binary_one,
        CharTwo.add_self_eq_zero, chi2_eq, D5.S3.Quantum.FiniteDimensional.qubitZ]

private lemma stabilizer_weyl {N : ℕ} (ψ : V N → ℂ)
    (hψ : StabilizedBy pauliSet ψ) :
    ∃ k : ℕ, ∃ v : Fin k → E N, ∃ c : Fin k → ℂ,
      ∀ w : V N → ℂ, (∀ j, c j • weyl (v j) w = w) ↔ ∃ a : ℂ, w = a • ψ := by
  classical
  obtain ⟨_, k, O, hO, hline⟩ := hψ
  choose r hr p hp using hO
  choose a b s hs hps using fun j i => pauli_wmat (p j i)
  let v : Fin k → E N := fun j => (a j, b j)
  let c : Fin k → ℂ := fun j => ∏ i, r j i * s j i
  have hop (j : Fin k) (w : V N → ℂ) :
      (show Matrix (V N) (V N) ℂ from tensorOp (O j)) *ᵥ w = c j • weyl (v j) w := by
    have he : O j = fun i => (r j i * s j i) • wmat (a j i) (b j i) := by
      funext i
      rw [hp j i, hps j i, smul_smul]
    rw [he, tensor_smul]
    change ((∏ i, r j i * s j i) •
      (show Matrix (V N) (V N) ℂ from tensorOp (fun i => wmat (a j i) (b j i)))) *ᵥ w = _
    rw [Matrix.smul_mulVec]
    exact congrArg ((∏ i, r j i * s j i) • ·) (tensor_weyl (v j) w)
  refine ⟨k, v, c, ?_⟩
  intro w
  have hline' : (∀ j, (show Matrix (V N) (V N) ℂ from tensorOp (O j)) *ᵥ w = w) ↔
      ∃ a : ℂ, w = a • ψ := hline w
  simpa only [hop] using hline' 


private def gate (h : Bool) (d : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if d = 0 then 1 else !![1, 0; 0, Complex.I]) *
    (if h then BinaryStabilizerLocalInequivalence.hadamard else 1)

private lemma wmat_unitary (a b : ZMod 2) :
    wmat a b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have cases₂ : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rw [Matrix.mem_unitaryGroup_iff]
  rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [wmat, binary_zero, binary_one, CharTwo.add_self_eq_zero, chi2_eq,
      Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Fin.ext_iff]

private lemma gate_unitary (h : Bool) (d : ZMod 2) :
    gate h d ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hs : s2 ^ 2 = 1 / 2 := by
    simp only [s2]
    push_cast
    rw [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hr : (starRingEnd ℂ) s2 = s2 := by simp [s2, map_ofNat]
  have cases₂ : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rw [Matrix.mem_unitaryGroup_iff]
  cases h <;> rcases cases₂ d with rfl | rfl <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gate, BinaryStabilizerLocalInequivalence.hadamard,
      pauliMatrix, qubitX, qubitZ, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, hr]
  all_goals ring_nf; norm_num [hs, Complex.I_sq]

set_option maxHeartbeats 1000000 in
-- The sixteen binary parameter cases expand to sixty-four matrix entry equalities.
private lemma gate_wmat (h : Bool) (d a b : ZMod 2) :
    let a' := if h then b else a
    let b' := (if h then a else b) + d * a'
    ∃ r : ℂ, r ≠ 0 ∧ gate h d * wmat a b = r • (wmat a' b' * gate h d) := by
  have cases₂ : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  refine ⟨chi2 (if h then a * b else 0) *
    (if d * (if h then b else a) = 0 then 1 else Complex.I), ?_, ?_⟩
  · cases h <;> rcases cases₂ d with rfl | rfl <;>
      rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;>
      norm_num [chi2_eq]
  · cases h <;> rcases cases₂ d with rfl | rfl <;>
      rcases cases₂ a with rfl | rfl <;> rcases cases₂ b with rfl | rfl <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [gate, wmat, BinaryStabilizerLocalInequivalence.hadamard,
        pauliMatrix, qubitX, qubitZ, Matrix.mul_apply,
        Fin.sum_univ_two, chi2_eq, binary_zero, binary_one, CharTwo.add_self_eq_zero] <;>
        ring_nf <;> norm_num [Complex.I_sq]


private def graphExponent {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (x : V N) : ZMod 2 := ∑ i, ∑ j, if i < j then Γ i j * x i * x j else 0

/-- The graph-state amplitude `(-1)^{Σ_{i<j} Γ_ij x_i x_j}` (unnormalized). -/
def graphAmp {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (x : Fin N → Fin 2) : ℂ :=
  (-1 : ℂ) ^ (∑ i, ∑ j, if i < j then
    Γ i j * binary (x i) * binary (x j) else 0).val

private lemma graph_exponent_step {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (hs : Γ.IsSymm) (hd : ∀ i, Γ i i = 0) (t : V N) (i : Fin N) :
    graphExponent Γ (t + Pi.single i 1) = graphExponent Γ t + ∑ j, Γ i j * t j := by
  classical
  have term (a b : Fin N) :
      (if a < b then Γ a b * (t a + (Pi.single i (1 : ZMod 2) : V N) a) *
        (t b + (Pi.single i (1 : ZMod 2) : V N) b) else 0) =
      (if a < b then Γ a b * t a * t b else 0) +
      (if b = i ∧ a < b then Γ a b * t a else 0) +
      (if a = i ∧ a < b then Γ a b * t b else 0) := by
    by_cases hab : a < b
    · by_cases hai : a = i
      · subst a
        have hbi : b ≠ i := ne_of_gt hab
        simp [hbi, hab]
        ring
      · by_cases hbi : b = i
        · subst b
          simp [hai, hab]
          ring
        · simp [hai, hbi, hab]
    · simp [hab]
  unfold graphExponent
  simp only [Pi.add_apply]
  simp_rw [term, Finset.sum_add_distrib]
  have col : (∑ a, ∑ b, if b = i ∧ a < b then Γ a b * t a else 0) =
      ∑ a, if a < i then Γ a i * t a else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [hbi]
    · simp
  have row : (∑ a, ∑ b, if a = i ∧ a < b then Γ a b * t b else 0) =
      ∑ b, if i < b then Γ i b * t b else 0 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro a _ hai
      simp [hai]
    · simp
  rw [col, row, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy j i with h | rfl | h
  · simp [h, hs.apply i j, not_lt_of_ge h.le]
  · simp [hd]
  · simp [h, not_lt_of_ge h.le]

private theorem graph_fixed_line {N : ℕ} (Γ : Matrix (Fin N) (Fin N) (ZMod 2))
    (hs : Γ.IsSymm) (hd : ∀ i, Γ i i = 0) (f : V N → ℂ)
    (hf : ∀ i, weyl (Pi.single i 1, Γ *ᵥ Pi.single i 1) f = f) :
    f = f 0 • graphAmp Γ := by
  have cases₂ : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  classical
  let g : V N → ℂ := fun t => chi2 (graphExponent Γ t) * f t
  have step (t : V N) (i : Fin N) : g (t + Pi.single i 1) = g t := by
    have phase : (∑ j, (Γ *ᵥ Pi.single i 1) j *
        (t j + (Pi.single i (1 : ZMod 2) : V N) j)) = ∑ j, Γ i j * t j := by
      simp only [Matrix.mulVec_single_one, Matrix.col_apply, mul_add, Finset.sum_add_distrib]
      have hz : (∑ j, Γ j i * (Pi.single i (1 : ZMod 2) : V N) j) = 0 := by
        simp [Pi.single_apply, mul_ite, hd]
      rw [hz, add_zero]
      exact Finset.sum_congr rfl (fun j _ => by rw [hs.apply i j])
    have h := congrFun (hf i) t
    simp only [weyl, phase] at h
    dsimp only [g]
    rw [graph_exponent_step Γ hs hd, chi2_add, mul_assoc, h]
  have invariant (u : V N) : ∀ t : V N, g (t + u) = g t := by
    apply Pi.single_induction (fun u => ∀ t : V N, g (t + u) = g t) u
    · intro t
      simp
    · intro u v hu hv t
      rw [← add_assoc, hv, hu]
    · intro i a t
      have ha : a = 0 ∨ a = 1 := cases₂ a
      rcases ha with rfl | rfl
      · simp
      · exact step t i
  funext t
  change f t = f 0 * graphAmp Γ t
  have hconst : g t = f 0 := by
    simpa [g, graphExponent, chi2] using invariant t 0
  calc
    f t = chi2 (graphExponent Γ t) * g t := by
      dsimp only [g]
      rw [← mul_assoc, chi2_laws.2.2.1, one_mul]
    _ = f 0 * graphAmp Γ t := by
      rw [hconst]
      have hg : graphAmp Γ t = chi2 (graphExponent Γ t) := by
        simp [graphAmp, graphExponent, chi2, AddChar.zmodChar_apply, binary_self]
      rw [hg, mul_comm]

private def symbolTransform {N : ℕ} (H : Finset (Fin N)) (d : V N) (v : E N) : E N :=
  ((swapAt H v).1, (swapAt H v).2 + fun i => d i * (swapAt H v).1 i)

private lemma tensor_clifford {N : ℕ} (H : Finset (Fin N)) (d : V N)
    (v : E N) (f : V N → ℂ) :
    ∃ r : ℂ, r ≠ 0 ∧
      (show Matrix (V N) (V N) ℂ from tensorOp (fun i => gate (decide (i ∈ H)) (d i))) *ᵥ
        weyl v f = r • weyl (symbolTransform H d v)
          ((show Matrix (V N) (V N) ℂ from
            tensorOp (fun i => gate (decide (i ∈ H)) (d i))) *ᵥ f) := by
  classical
  let A := fun i => gate (decide (i ∈ H)) (d i)
  let v' := symbolTransform H d v
  have localLaw (i : Fin N) : ∃ r : ℂ, r ≠ 0 ∧
      A i * wmat (v.1 i) (v.2 i) = r • (wmat (v'.1 i) (v'.2 i) * A i) := by
    have h := gate_wmat (decide (i ∈ H)) (d i) (v.1 i) (v.2 i)
    by_cases hi : i ∈ H <;> simpa [A, v', symbolTransform, swapAt, hi] using h
  choose r hr he using localLaw
  have hm : tensorOp A * tensorOp (fun i => wmat (v.1 i) (v.2 i)) =
      (∏ i, r i) • (tensorOp (fun i => wmat (v'.1 i) (v'.2 i)) * tensorOp A) := by
    rw [tensor_mul, tensor_mul]
    rw [show (fun i => A i * wmat (v.1 i) (v.2 i)) =
      (fun i => r i • (wmat (v'.1 i) (v'.2 i) * A i)) from funext he, tensor_smul]
  let G : Matrix (V N) (V N) ℂ := tensorOp A
  let W : E N → Matrix (V N) (V N) ℂ :=
    fun u => tensorOp (fun i => wmat (u.1 i) (u.2 i))
  have hm' : G * W v = (∏ i, r i) • (W v' * G) := hm
  have hv := congrArg (fun M : Matrix (V N) (V N) ℂ => M *ᵥ f) hm'
  have hw (u : E N) (g : V N → ℂ) : W u *ᵥ g = weyl u g := tensor_weyl u g
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hw, hw] at hv
  exact ⟨∏ i, r i, Finset.prod_ne_zero_iff.mpr (fun i _ => hr i), hv⟩

private lemma stabilizer_graph_eigen {N : ℕ} (ψ : V N → ℂ)
    (hψ : StabilizedBy pauliSet ψ) :
    ∃ (A : Fin N → Matrix (Fin 2) (Fin 2) ℂ)
      (Γ : Matrix (Fin N) (Fin N) (ZMod 2)),
      (∀ i, A i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧ Γ.IsSymm ∧ (∀ i, Γ i i = 0) ∧
      ∀ i, ∃ a : ℂ, weyl (Pi.single i 1, Γ *ᵥ Pi.single i 1)
        ((show Matrix (V N) (V N) ℂ from tensorOp A) *ᵥ ψ) =
        a • ((show Matrix (V N) (V N) ℂ from tensorOp A) *ᵥ ψ) := by
  classical
  obtain ⟨k, v, c, hline⟩ := stabilizer_weyl ψ hψ
  obtain ⟨_, hiso, hdim, heigen⟩ := unique_weyl_line_lagrangian v c ψ hψ.1 hline
  let L := Submodule.span (ZMod 2) (Set.range v)
  obtain ⟨H, d, Γ, hs, hd, hgraph⟩ := lagrangian_graph_form L hiso hdim
  let A := fun i => gate (decide (i ∈ H)) (d i)
  refine ⟨A, Γ, fun i => gate_unitary _ _, hs, hd, ?_⟩
  intro i
  let q : E N := (Pi.single i 1, Γ *ᵥ Pi.single i 1)
  let w : E N := (q.1, q.2 + fun j => d j * q.1 j)
  let u := swapAt H w
  have hswap : swapAt H u = w := by
    ext j <;> by_cases hj : j ∈ H <;> simp [u, swapAt, hj]
  have htu : symbolTransform H d u = q := by
    unfold symbolTransform
    rw [hswap]
    apply Prod.ext
    · rfl
    · funext j
      change (q.2 j + d j * q.1 j) + d j * q.1 j = q.2 j
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have humem : u ∈ L := (hgraph u).mpr (by
    change (symbolTransform H d u).2 = Γ *ᵥ (symbolTransform H d u).1
    rw [htu])
  obtain ⟨a, ha⟩ := (heigen u).mpr humem
  obtain ⟨r, hr, hh⟩ := tensor_clifford H d u ψ
  rw [htu, ha, Matrix.mulVec_smul] at hh
  refine ⟨r⁻¹ * a, ?_⟩
  rw [← smul_smul, eq_inv_smul_iff₀ hr]
  exact hh.symm

private lemma graph_sign_correction {N : ℕ}
    (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (hs : Γ.IsSymm) (hd : ∀ i, Γ i i = 0)
    (φ : V N → ℂ) (hne : φ ≠ 0)
    (heigen : ∀ i, ∃ a : ℂ, weyl (Pi.single i 1, Γ *ᵥ Pi.single i 1) φ = a • φ) :
    ∃ (b : V N) (c : ℂ), weyl (0, b) φ = c • graphAmp Γ := by
  classical
  choose a ha using heigen
  have square (i : Fin N) : a i * a i = 1 := by
    have h := weyl_square (Pi.single i 1, Γ *ᵥ Pi.single i 1) φ
    have hz : (∑ j, (Pi.single i (1 : ZMod 2) : V N) j *
        (Γ *ᵥ Pi.single i 1) j) = 0 := by
      simp [Pi.single_apply, ite_mul, hd]
    rw [ha i, (weyl_linear _).2.1, ha i, smul_smul, hz, chi2_laws.1] at h
    exact smul_left_injective ℂ hne h
  let b : V N := fun i => if a i = 1 then 0 else 1
  have hb (i : Fin N) : chi2 (b i) = a i := by
    rcases mul_self_eq_one_iff.mp (square i) with h | h <;> norm_num [b, h, chi2_eq]
  refine ⟨b, (weyl (0, b) φ) 0, graph_fixed_line Γ hs hd _ ?_⟩
  intro i
  have hsp : sp (Pi.single i 1, Γ *ᵥ Pi.single i 1) (0, b) = b i := by
    simp [sp, Pi.single_apply, ite_mul]
  rw [weyl_commute, ha i, (weyl_linear (0, b)).2.1, smul_smul,
    hsp, hb, square, one_smul]

/-- Every nonzero Pauli stabilizer eigenline is a product of local unitaries applied to a
binary graph amplitude, up to an arbitrary complex scalar. -/
theorem stabilizer_graph_normal_form {N : ℕ} (ψ : (Fin N → Fin 2) → ℂ)
    (hψ : StabilizedBy pauliSet ψ) :
    ∃ (U : Fin N → Matrix (Fin 2) (Fin 2) ℂ) (Γ : Matrix (Fin N) (Fin N) (ZMod 2)) (c : ℂ),
      (∀ i, U i ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧ Γ.IsSymm ∧ (∀ i, Γ i i = 0) ∧
      ψ = c • (tensorOp U *ᵥ graphAmp Γ) := by
  classical
  obtain ⟨A, Γ, hA, hs, hd, heigen⟩ := stabilizer_graph_eigen ψ hψ
  let G := tensorOp A
  let φ : V N → ℂ := (show Matrix (V N) (V N) ℂ from G) *ᵥ ψ
  have hG : G ∈ Matrix.unitaryGroup (Fin N → Fin 2) ℂ := tensor_unitary A hA
  have hinv : Gᴴ * G = 1 := Matrix.mem_unitaryGroup_iff'.mp hG
  have hne : φ ≠ 0 := by
    intro hz
    have hh : Gᴴ *ᵥ (G *ᵥ ψ) = ψ := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    change (show Matrix (V N) (V N) ℂ from Gᴴ) *ᵥ φ = ψ at hh
    rw [hz, Matrix.mulVec_zero] at hh
    exact hψ.1 hh.symm
  obtain ⟨b, c, hfixed⟩ := graph_sign_correction Γ hs hd φ hne heigen
  let B := fun i => wmat 0 (b i)
  let U := fun i => (A i)ᴴ * B i
  have hU (i : Fin N) : U i ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    apply (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
    · exact Unitary.star_mem (hA i)
    · exact wmat_unitary 0 (b i)
  let T : Matrix (V N) (V N) ℂ := tensorOp B
  let g : V N → ℂ := graphAmp Γ
  have hwB : T *ᵥ g = weyl (0, b) g := tensor_weyl (0, b) g
  have hfixed' : weyl (0, b) φ = c • g := hfixed
  have hφ : φ = c • (T *ᵥ g) := by
    calc
      φ = weyl (0, b) (weyl (0, b) φ) := by
        rw [weyl_square]
        simp [chi2_laws.1]
      _ = weyl (0, b) (c • g) := congrArg (weyl (0, b)) hfixed'
      _ = c • weyl (0, b) g := (weyl_linear _).2.1 _ _
      _ = c • (T *ᵥ g) := congrArg (c • ·) hwB.symm
  have hφ' : G *ᵥ ψ = c • (tensorOp B *ᵥ graphAmp Γ) := hφ
  refine ⟨U, Γ, c, hU, hs, hd, ?_⟩
  calc
    ψ = Gᴴ *ᵥ (G *ᵥ ψ) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = c • (tensorOp U *ᵥ graphAmp Γ) := by
      rw [hφ', Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      change c • (((tensorOp A)ᴴ * tensorOp B) *ᵥ graphAmp Γ) = _
      rw [tensor_adj, tensor_mul]


end D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
