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

private def wmat (a b : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun t s =>
    let t' : ZMod 2 := t.val
    let s' : ZMod 2 := s.val
    if s' = t' + a then chi2 (b * s') else 0

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
    change (∏ i, if ((y i).val : ZMod 2) = (x i).val + v.1 i then
      chi2 (v.2 i * (y i).val) else 0) = _
    simp only [ZMod.natCast_zmod_val]
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
    ext t s; fin_cases t <;> fin_cases s <;> norm_num [pauliMatrix, wmat, chi2_eq]
  · refine ⟨1, 0, 1, one_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat, chi2_eq, D5.S3.Quantum.FiniteDimensional.qubitX] <;> decide
  · refine ⟨1, 1, Complex.I, Complex.I_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat, chi2_eq, D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ, Matrix.mul_apply, Fin.sum_univ_two] <;> decide
  · refine ⟨0, 1, 1, one_ne_zero, ?_⟩
    ext t s; fin_cases t <;> fin_cases s <;>
      norm_num [pauliMatrix, wmat, chi2_eq, D5.S3.Quantum.FiniteDimensional.qubitZ]

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


/- Open target: stabilizer_graph_normal_form, as stated in #13575. -/

end D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
