/- GID: D5/S3/ConceptDynamics/Coding/ResetHistoryKernel
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetHistoryKernel
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Faithful finite alternating actions in the original Reset representation kernel. -/

import D5.S3.ConceptDynamics.Coding.SeparatorGapAction
import D5.S3.ConceptDynamics.Coding.MarkerPermutationAction
import D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetHistoryKernel

open Polynomial
open ResetNumberedHistories ResetStandardBeamGeometry
open ResetFullStandardBeamRepresentation ResetNativeIntegerChart ResetSignIntegerCyclic
open StandardBeamHomeomorphisms

private local instance originalNativeIntModule (q : ℕ) : Module ℤ (Native q) :=
  AddCommGroup.toIntModule _

theorem rho_time (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (x : Native q) :
    rho q hq h (resetTheta q x) = resetTheta q (rho q hq h x) := by
  have hc : h * unitShift (ResetGraph q) = unitShift (ResetGraph q) * h := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro y
    exact h.property y
  have he := congrArg (rho q hq) hc
  rw [map_mul, map_mul] at he
  have hx := congrArg (fun f : Native q ≃ₗ[ℤ] Native q => f x) he
  have ht (y : Native q) : rho q hq (unitShift (ResetGraph q)) y = resetTheta q y :=
    LinearMap.congr_fun (rho_unitShift q hq) y
  simpa only [LinearEquiv.mul_apply, ht] using hx

/-- Transport any actual forward-time commuting integer-linear map into the cyclic chart. -/
def centralizingMap (q : ℕ) (hq : 0 < q) (A : Native q →ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) :
    QF q →ₗ[ℤ[X]] QF q :=
  (LinearMap.ofAEval (resetTheta q)
    ((nativeIntEquiv q hq).symm.toLinearMap.comp A) (by
      intro x
      change (nativeIntEquiv q hq).symm (A (resetTheta q x)) =
        (X : ℤ[X]) • (nativeIntEquiv q hq).symm (A x)
      rw [ht]
      apply (nativeIntEquiv q hq).injective
      rw [LinearEquiv.apply_symm_apply]
      change _ = nativeIntEquiv q hq (fp q X * _)
      rw [(native_presentation q hq).2.1, LinearEquiv.apply_symm_apply])).comp
    (nativePolynomialEquiv q hq).toLinearMap

/-- A commuting map is multiplication by its value at the actual cyclic generator. -/
theorem centralizingMap_scalar (q : ℕ) (hq : 0 < q) (A : Native q →ₗ[ℤ] Native q)
    (ht : ∀ x, A (resetTheta q x) = resetTheta q (A x)) (b : QF q) :
    centralizingMap q hq A ht b = b * centralizingMap q hq A ht 1 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hs := (centralizingMap q hq A ht).map_smul p 1
  change centralizingMap q hq A ht (fp q p * 1) = fp q p * centralizingMap q hq A ht 1 at hs
  simpa only [fp, mul_one] using hs

private def chartMap (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) :
    QF q →ₗ[ℤ[X]] QF q :=
  centralizingMap q hq (rho q hq h).toLinearMap (rho_time q hq h)

private theorem chartMap_apply (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (b : QF q) :
    chartMap q hq h b = (nativeIntEquiv q hq).symm
      (rho q hq h (nativeIntEquiv q hq b)) := rfl

private theorem chartMap_scalar (q : ℕ) (hq : 0 < q) (h : ResetFullAut q) (b : QF q) :
    chartMap q hq h b = b * chartMap q hq h 1 :=
  centralizingMap_scalar q hq (rho q hq h).toLinearMap (rho_time q hq h) b

private theorem rho_commute (q : ℕ) (hq : 0 < q) (h g : ResetFullAut q) :
    Commute (rho q hq h) (rho q hq g) := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨b, rfl⟩ := (nativeIntEquiv q hq).surjective x
  apply (nativeIntEquiv q hq).symm.injective
  change (nativeIntEquiv q hq).symm
      (rho q hq h (rho q hq g (nativeIntEquiv q hq b))) =
    (nativeIntEquiv q hq).symm
      (rho q hq g (rho q hq h (nativeIntEquiv q hq b)))
  have he (h g : ResetFullAut q) :
      (nativeIntEquiv q hq).symm
        (rho q hq h (rho q hq g (nativeIntEquiv q hq b))) =
        chartMap q hq h (chartMap q hq g b) := by
    simp only [chartMap_apply, LinearEquiv.apply_symm_apply]
  rw [he h g, he g h,
    chartMap_scalar q hq h (chartMap q hq g b),
    chartMap_scalar q hq g (chartMap q hq h b),
    chartMap_scalar q hq g b, chartMap_scalar q hq h b]
  ring

private theorem alternating_killed {I H : Type} [Fintype I] [DecidableEq I] [Group H]
    (f : Equiv.Perm I →* H) (hc : ∀ a b, Commute (f a) (f b)) :
    alternatingGroup I ≤ f.ker := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro g hg
  have hs : Equiv.Perm.IsThreeCycle (g ^ 2) := by
    simpa [pow_two] using hg.isThreeCycle_sq
  have hconj := Equiv.Perm.isConj_of_cycleType_eq (hg.cycleType.trans hs.cycleType.symm)
  obtain ⟨a, b, hab⟩ := mem_commutatorSet_iff.mp
    (mem_commutatorSet_of_isConj_sq (Equiv.Perm I) hconj)
  change f g = 1
  rw [← hab, map_commutatorElement]
  exact (hc a b).commutator_eq

private def dataIndex (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → Bool) :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin k → Bool) = 2 ^ k)).symm

/-- Reindex the actual faithful Boolean-word action by the prescribed finite cardinal. -/
def symmetricAction (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) :
    Equiv.Perm (Fin (2 ^ k)) →* ResetFullAut q :=
  (MarkerPermutationAction.resetAction (by omega : 1 < q) (by omega : 0 < k)).comp
    (dataIndex k).permCongrHom.toMonoidHom

private theorem symmetricAction_injective (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) :
    Function.Injective (symmetricAction q k hq hk) :=
  (MarkerPermutationAction.resetAction_injective (by omega : 1 < q) (by omega : 0 < k)).comp
    (dataIndex k).permCongrHom.injective

/-- A4 is included: three-cycles are commutators in Sym, without assuming Alt perfect. -/
def alternatingKernelEmbedding (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k) (hq0 : 0 < q) :
    alternatingGroup (Fin (2 ^ k)) →* (rho q hq0).ker := by
  let phi := symmetricAction q k hq hk
  let f := (rho q hq0).comp phi
  have ha : alternatingGroup (Fin (2 ^ k)) ≤ f.ker :=
    alternating_killed f (fun a b => rho_commute q hq0 (phi a) (phi b))
  exact (phi.comp (alternatingGroup (Fin (2 ^ k))).subtype).codRestrict
    (rho q hq0).ker (fun a => ha a.property)

/-- Uniform injectivity into the ORIGINAL representation kernel on the ORIGINAL histories. -/
theorem alternatingKernelEmbedding_injective (q k : ℕ) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hq0 : 0 < q) : Function.Injective (alternatingKernelEmbedding q k hq hk hq0) := by
  intro a b he
  apply Subtype.ext
  apply symmetricAction_injective q k hq hk
  exact congrArg Subtype.val he


open ResetNumberedHistories.Alternating
open CountedGroupOverlap (Edge)
open EssentialWordRealization

private theorem gapSignSquare : (Multiplicative.ofAdd true : Sign) * Multiplicative.ofAdd true = 1 := by decide
private theorem gapSignNe : (1 : Sign) ≠ Multiplicative.ofAdd true := by decide

private def gapZero {q : ℕ} (hq : 2 ≤ q) : Fin q := ⟨0, by omega⟩
private def gapOne {q : ℕ} (hq : 2 ≤ q) : Fin q := ⟨1, by omega⟩
private def gapA {q : ℕ} (hq : 2 ≤ q) : B q := .f (gapZero hq) 1
private def gapB {q : ℕ} (hq : 2 ≤ q) : B q := .f (gapZero hq) (Multiplicative.ofAdd true)
private def gapC {q : ℕ} (hq : 2 ≤ q) (h : Sign) : B q :=
  .a (gapZero hq) h (by dsimp [gapZero]; omega)
private def gapD {q : ℕ} (hq : 2 ≤ q) (h : Sign) : B q := .f (gapOne hq) h

/-- The two length-twelve blocks are U^4 and V^3 in the signed, numbered graph. -/
private def gapBlock {q : ℕ} (hq : 2 ≤ q) (bit : Bool) (j : Fin 12) : B q :=
  if bit then
    if j.val % 3 = 0 then gapA hq
    else if j.val % 3 = 1 then gapC hq (Multiplicative.ofAdd true)
    else gapD hq (Multiplicative.ofAdd true)
  else
    if j.val % 4 = 0 then gapC hq 1
    else if j.val % 4 = 1 then gapD hq 1
    else if j.val % 4 = 2 then gapC hq (Multiplicative.ofAdd true)
    else gapD hq (Multiplicative.ofAdd true)

private theorem gapBlock_legal {q : ℕ} (hq : 2 ≤ q) (bit : Bool)
    (j : Fin 12) (hj : j.val + 1 < 12) :
    targetB (by omega : 0 < q) (gapBlock hq bit j) =
      sourceB (gapBlock hq bit ⟨j.val + 1,hj⟩) := by
  fin_cases j <;> cases bit <;>
    simp_all [gapBlock, gapA, gapC, gapD, sourceB, targetB, flipSign, zero, next,
      gapZero, gapOne, gapSignSquare, gapSignNe]

private theorem gapBlock_source {q : ℕ} (hq : 2 ≤ q) (bit : Bool) :
    sourceB (gapBlock hq bit ⟨0, by omega⟩) = (gapZero hq, (1 : Sign)) := by
  cases bit <;> rfl

private theorem gapBlock_target {q : ℕ} (hq : 2 ≤ q) (bit : Bool) :
    targetB (by omega : 0 < q) (gapBlock hq bit ⟨11, by omega⟩) =
      (gapZero hq, (1 : Sign)) := by
  cases bit <;> simp [gapBlock, gapD, targetB, flipSign, zero, gapZero, gapSignSquare]

private theorem gapBlock_avoids {q : ℕ} (hq : 2 ≤ q) (bit : Bool) (j : Fin 12) :
    gapBlock hq bit j ≠ gapB hq := by
  fin_cases j <;> cases bit <;>
    simp [gapBlock, gapA, gapB, gapC, gapD, gapZero, gapOne, gapSignNe]

private def gapLength (n : ℕ) : ℕ := 12*(n + 2)+1
private def gapData {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (i : Fin (n + 2) → Bool)
    (j : Fin (gapLength n)) : B q :=
  if h : j.val < 12*(n + 2) then
    gapBlock hq (i ⟨j.val/12, by omega⟩) ⟨j.val%12, Nat.mod_lt _ (by omega)⟩
  else gapA hq

private theorem gapData_sample {q : ℕ} (hq : 2 ≤ q) (n : ℕ)
    (i : Fin (n + 2) → Bool) (j : Fin (n + 2)) :
    gapData hq n i ⟨12*j.val, by dsimp [gapLength]; omega⟩ =
      gapBlock hq (i j) ⟨0, by omega⟩ := by
  have hj := j.isLt
  simp only [gapData, dif_pos (by omega : 12*j.val < 12*(n + 2)),
    Nat.mul_div_cancel_left _ (by omega : 0 < 12), Nat.mul_mod_right]

private theorem gapData_injective {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    Function.Injective (gapData hq n) := by
  intro i l he
  funext j
  have hs := congrFun he ⟨12*j.val, by dsimp [gapLength]; have hj := j.isLt; omega⟩
  rw [gapData_sample, gapData_sample] at hs
  cases hi : i j <;> cases hl : l j <;> try rfl
  all_goals simp [hi, hl, gapBlock, gapA, gapC] at hs

private theorem gapData_avoids {q : ℕ} (hq : 2 ≤ q) (n : ℕ)
    (i : Fin (n + 2) → Bool) (j : Fin (gapLength n)) : gapData hq n i j ≠ gapB hq := by
  unfold gapData
  split_ifs
  · exact gapBlock_avoids hq _ _
  · simp [gapA, gapB, gapSignNe]

set_option backward.isDefEq.respectTransparency false in
private theorem gapData_source {q : ℕ} (hq : 2 ≤ q) (n : ℕ)
    (i : Fin (n + 2) → Bool) :
    sourceB (gapData hq n i ⟨0, by dsimp [gapLength]; omega⟩) =
      targetB (by omega : 0 < q) (gapB hq) := by
  rw [gapData, dif_pos (by omega : 0 < 12*(n + 2))]
  simp only [Fin.val_mk, Nat.zero_div, Nat.zero_mod]
  rw [gapBlock_source]
  simp [gapB, targetB, flipSign, zero, gapZero, gapSignSquare]

private theorem gapData_target {q : ℕ} (hq : 2 ≤ q) (n : ℕ)
    (i : Fin (n + 2) → Bool) :
    targetB (by omega : 0 < q)
        (gapData hq n i ⟨gapLength n-1, by dsimp [gapLength]; omega⟩) =
      sourceB (gapB hq) := by
  rw [gapData, dif_neg (by dsimp [gapLength]; omega)]
  simp [gapA, gapB, sourceB, targetB, flipSign, zero, gapZero]

private theorem gapData_legal {q : ℕ} (hq : 2 ≤ q) (n : ℕ)
    (i : Fin (n + 2) → Bool) (j : Fin (gapLength n)) (hj : j.val + 1 < gapLength n) :
    targetB (by omega : 0 < q) (gapData hq n i j) =
      sourceB (gapData hq n i ⟨j.val + 1,hj⟩) := by
  have hd : j.val < 12*(n + 2) := by dsimp [gapLength] at hj; omega
  rw [gapData, dif_pos hd]
  by_cases hn : j.val + 1 < 12*(n + 2)
  · rw [gapData, dif_pos hn]
    by_cases hc : j.val%12 = 11
    · have hc' : (j.val + 1)%12 = 0 := by omega
      have hj' : (⟨j.val%12, Nat.mod_lt _ (by omega)⟩ : Fin 12) = ⟨11, by omega⟩ :=
        Fin.ext hc
      have hk' : (⟨(j.val + 1)%12, Nat.mod_lt _ (by omega)⟩ : Fin 12) = ⟨0, by omega⟩ :=
        Fin.ext hc'
      rw [hj', hk', gapBlock_target, gapBlock_source]
    · have he : (j.val + 1)/12 = j.val/12 := by omega
      have hm : (j.val + 1)%12 = j.val%12+1 := by omega
      have hi : (⟨(j.val + 1)/12, by omega⟩ : Fin (n + 2)) = ⟨j.val/12, by omega⟩ := Fin.ext he
      rw [hi]
      convert gapBlock_legal hq (i ⟨j.val/12, by omega⟩)
        ⟨j.val%12, Nat.mod_lt _ (by omega)⟩ (by dsimp; omega) using 1
      congr 2
      apply Fin.ext
      exact hm
  · rw [gapData, dif_neg hn]
    have hc : j.val%12 = 11 := by omega
    have hj' : (⟨j.val%12, Nat.mod_lt _ (by omega)⟩ : Fin 12) = ⟨11, by omega⟩ := Fin.ext hc
    rw [hj', gapBlock_target]
    rfl

private def gapFamily {q : ℕ} (hq : 2 ≤ q) :
    SeparatorGapAction.Family (Edge (resetMatrix q) × Sign)
      (fun n => Fin (n + 2) → Bool) gapLength where
  separator := originalEdge (by omega) (gapB hq)
  positive n := by dsimp [gapLength]; omega
  length_injective := by intro n m h; dsimp [gapLength] at h; omega
  data n i j := originalEdge (by omega) (gapData hq n i j)
  data_injective n := by
    intro i j h
    apply gapData_injective hq n
    funext t
    exact (actualEdgeEquiv (by omega : 0 < q)).injective (congrFun h t)
  avoids n i j h := gapData_avoids hq n i j
    ((actualEdgeEquiv (by omega : 0 < q)).injective h)

private theorem gapPaths {q : ℕ} (hq : 2 ≤ q) :
    SeparatorGapAction.Paths (gapFamily hq) (ResetGraph q) where
  data_legal n i j hj := by
    change (ResetGraph q).target (originalEdge _ _) = (ResetGraph q).source (originalEdge _ _)
    rw [actual_target, actual_source]
    exact gapData_legal hq n i j hj
  data_source n i := by
    change (ResetGraph q).source (originalEdge _ _) = (ResetGraph q).target (originalEdge _ _)
    rw [actual_source, actual_target]
    exact gapData_source hq n i
  data_target n i := by
    change (ResetGraph q).target (originalEdge _ _) = (ResetGraph q).source (originalEdge _ _)
    rw [actual_target, actual_source]
    exact gapData_target hq n i

/-- The genuine noncommutative finite-support product, including A4 at coordinate zero. -/
abbrev FiniteGapAlternating :=
  RestrictedProduct (fun n : ℕ => alternatingGroup (Fin (2^(n + 2))))
    (fun n => (↑(⊥ : Subgroup (alternatingGroup (Fin (2^(n + 2))))) :
      Set (alternatingGroup (Fin (2^(n + 2)))))) Filter.cofinite

private def gapTupleMap : FiniteGapAlternating →*
    SeparatorGapAction.FinitePerm (fun n => Fin (n + 2) → Bool) where
  toFun g := ⟨fun n => (dataIndex (n + 2)).permCongrHom (g n).val, by
    filter_upwards [g.property] with n hn
    have he : g n = 1 := Subgroup.mem_bot.mp hn
    change (dataIndex (n + 2)).permCongrHom (g n).val = 1
    rw [he, OneMemClass.coe_one, map_one]⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro n
    change (dataIndex (n + 2)).permCongrHom 1 = 1
    exact map_one _
  map_mul' g h := by
    apply RestrictedProduct.ext
    intro n
    change (dataIndex (n + 2)).permCongrHom ((g n).val * (h n).val) =
      (dataIndex (n + 2)).permCongrHom (g n).val * (dataIndex (n + 2)).permCongrHom (h n).val
    exact map_mul _ _ _

private theorem gapTupleMap_injective : Function.Injective gapTupleMap := by
  intro g h he
  apply RestrictedProduct.ext
  intro n
  apply Subtype.ext
  apply (dataIndex (n + 2)).permCongrHom.injective
  exact congrArg (fun f : SeparatorGapAction.FinitePerm (fun n => Fin (n + 2) → Bool) => f n) he

private theorem gapTuple_kernel (q : ℕ) (hq : 2 ≤ q) (hq0 : 0 < q)
    (g : FiniteGapAlternating) :
    SeparatorGapAction.finiteAction (gapFamily hq) (ResetGraph q) (gapPaths hq)
      (gapTupleMap g) ∈ (rho q hq0).ker := by
  apply SeparatorGapAction.finiteAction_mem
  intro n
  let φ := (SeparatorGapAction.action (gapFamily hq) (ResetGraph q) (gapPaths hq) n).comp
    (dataIndex (n + 2)).permCongrHom.toMonoidHom
  have ha := alternating_killed ((rho q hq0).comp φ)
    (fun a b => rho_commute q hq0 (φ a) (φ b))
  exact ha (g n).property

/-- All length-separated alternating coordinates act simultaneously in the ORIGINAL rho kernel. -/
def gapProductKernelEmbedding (q : ℕ) (hq : 2 ≤ q) (hq0 : 0 < q) :
    FiniteGapAlternating →* (rho q hq0).ker :=
  ((SeparatorGapAction.finiteAction (gapFamily hq) (ResetGraph q) (gapPaths hq)).comp
    gapTupleMap).codRestrict (rho q hq0).ker (gapTuple_kernel q hq hq0)

/-- Joint original-history faithfulness, uniform for every q>=2 and including degree four. -/
theorem gapProductKernelEmbedding_injective (q : ℕ) (hq : 2 ≤ q) (hq0 : 0 < q) :
    Function.Injective (gapProductKernelEmbedding q hq hq0) := by
  intro g h he
  apply gapTupleMap_injective
  apply SeparatorGapAction.finiteAction_injective (gapFamily hq) (ResetGraph q) (gapPaths hq)
    (reset_expanded_essential q hq0)
  exact congrArg Subtype.val he

end D5.S3.ConceptDynamics.Coding.ResetHistoryKernel
