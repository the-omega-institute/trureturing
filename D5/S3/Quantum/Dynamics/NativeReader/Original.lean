/- GID: D5/S3/Quantum/Dynamics/NativeReader/Original
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/Original
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed exterior coordinates and original native preparation operators. -/

import D5.S3.Quantum.Dynamics.NativeReader.Global
import D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality

/-! Original finite-word preparation uses the same legal paths and fixed exterior bits. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Quantum.Dynamics.NativeReader
open Matrix
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open D5.S1.Words.AdmissibleWords.AdmissibleCount

/-- All thirteen old source paths, before attaching the original record bit. -/
abbrev OldSource := LegalPath adjacent 6 false false

/-- The literal original J: b1..b5 are the old word, b6=0,b7=1,b8=0,b9=i,b10=0. -/
def sourceJ (v : OldSource) (i : Bool) : Source :=
  ⟨fun k => if h : k.val < 7 then v.1 ⟨k.val, h⟩
      else if k.val = 7 then true else if k.val = 9 then i else false, by
    refine ⟨by simpa using v.2.1, by simp, ?_⟩
    intro k
    by_cases hk : k.val < 6
    · simpa [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ,
        show k.val < 7 by omega, show k.val + 1 < 7 by omega] using
        v.2.2.2 ⟨k.val, hk⟩
    · have hs : k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by
        rcases k with ⟨k, hk'⟩
        simp only [Fin.mk.injEq]
        omega
      have hv : v.1 6 = false := v.2.2.1
      rcases hs with rfl | rfl | rfl | rfl <;> simp [adjacent, hv]⟩

private theorem sourceJ_injective :
    Function.Injective (fun p : OldSource × Bool => sourceJ p.1 p.2) := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  have hi : i = j := by simpa [sourceJ] using congrArg (fun q : Source => q.1 9) h
  have hv : v = w := by
    apply Subtype.ext
    funext k
    have hh := congrArg (fun q : Source => q.1 ⟨k.val, by omega⟩) h
    simpa [sourceJ, show k.val < 7 by omega] using hh
  exact Prod.ext hv hi

def sourceCode : Set Source := Set.range (fun p : OldSource × Bool => sourceJ p.1 p.2)

instance : Fintype sourceCode := by classical; unfold sourceCode; infer_instance
instance : Fintype {q : Source // q ∉ sourceCode} := by classical; infer_instance

/-- The full 26-code and 63-complement remain subcarriers of the original 89-path space. -/
theorem source_code_counts : Fintype.card sourceCode = 26 ∧
    Fintype.card {q : Source // q ∉ sourceCode} = 63 := by
  classical
  have ho : Fintype.card OldSource = 13 := by
    rw [Fintype.card_congr (pathWordEquiv 5), admissibleWord_card_eq_fib]
    decide
  have hc : Fintype.card sourceCode = 26 := by
    rw [← Fintype.card_congr (Equiv.ofInjective _ sourceJ_injective), Fintype.card_prod, ho]
    decide
  refine ⟨hc, ?_⟩
  rw [Fintype.card_subtype_compl, source_card, hc]

def oldReady : OldSource :=
  ⟨![false, false, false, true, false, false, false], by
    refine ⟨by simp, by simp, ?_⟩
    intro k
    fin_cases k <;> decide⟩

theorem original_ready_is_J : sourceJ oldReady false = readySource := by
  apply Subtype.ext
  funext k
  fin_cases k <;> simp [sourceJ, oldReady, readySource]

/-- Reinsert the two original fixed exterior bits. -/
def padPath (n : ℕ) (q : LegalPath adjacent n false false) :
    LegalPath adjacent (n + 2) true true :=
  ⟨fun k => if h : 0 < k.val ∧ k.val < n + 2 then q.1 ⟨k.val - 1, by omega⟩ else true, by
    refine ⟨by simp, by simp, ?_⟩
    intro k
    by_cases h0 : k.val = 0
    · have hq : q.1 ⟨0, by omega⟩ = false := q.2.1
      simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, h0, hq, adjacent]
    · by_cases hn : k.val = n + 1
      · have he : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
        have hq : q.1 ⟨n, by omega⟩ = false := by simpa [he] using q.2.2.1
        simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, hn, hq, adjacent]
      · have hq := q.2.2.2 ⟨k.val - 1, by omega⟩
        simpa [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ,
          show 0 < k.val by omega, show k.val < n + 2 by omega,
          show k.val + 1 < n + 2 by omega,
          Nat.sub_add_cancel (by omega : 1 ≤ k.val)] using hq⟩

/-- Drop only the two declared fixed bits; the two adjacent zero bits follow from legality. -/
def unpadPath (n : ℕ) (p : LegalPath adjacent (n + 2) true true) :
    LegalPath adjacent n false false :=
  ⟨fun k => p.1 ⟨k.val + 1, by omega⟩, by
    refine ⟨?_, ?_, ?_⟩
    · have h := p.2.2.2 0
      have h0 := p.2.1
      cases hb : p.1 1 <;> simp_all [adjacent]
    · have h := p.2.2.2 ⟨n + 1, by omega⟩
      have he : p.1 ⟨n + 2, by omega⟩ = true := p.2.2.1
      cases hb : p.1 ⟨n + 1, by omega⟩ <;> simp_all [adjacent]
    · intro k
      simpa [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, Nat.add_assoc] using
        p.2.2.2 ⟨k.val + 1, by omega⟩⟩

/-- Exact coordinate equivalence, rather than a change of model or a reduced carrier. -/
def padEquiv (n : ℕ) :
    LegalPath adjacent n false false ≃ LegalPath adjacent (n + 2) true true where
  toFun := padPath n
  invFun := unpadPath n
  left_inv q := by
    apply Subtype.ext
    funext k
    simp [unpadPath, padPath]
  right_inv p := by
    apply Subtype.ext
    funext k
    dsimp [padPath, unpadPath]
    split_ifs with h
    · have he : (⟨k.val - 1 + 1, by omega⟩ : Fin (n + 3)) = k :=
        Fin.ext (by change k.val - 1 + 1 = k.val; omega)
      exact congrArg p.1 he
    · by_cases h0 : k.val = 0
      · have he : k = 0 := Fin.ext h0
        simpa [he] using p.2.1.symm
      · have he : k = Fin.last (n + 2) := Fin.ext (by simp; omega)
        simpa [he] using p.2.2.1.symm

/-- Every original native address, including the two endpoint singleton blocks. -/
def originalProjection (j : Fin 11) : Matrix Source Source ℂ :=
  (pathProjection adjacent weight Real.goldenRatio 12 true true (j.val + 1)
    ⟨by omega, by omega⟩).submatrix (padEquiv 10) (padEquiv 10)

/-- Every native address of the entire extended carrier. -/
def extendedProjection (j : Fin 15) : Matrix Extended Extended ℂ :=
  (pathProjection adjacent weight Real.goldenRatio 16 true true (j.val + 1)
    ⟨by omega, by omega⟩).submatrix (padEquiv 14) (padEquiv 14)

def originalPulse (j : Fin 11) (s : ℝ) : Matrix Source Source ℂ :=
  unitPhase (alpha * s) • (1 + (unitPhase (alpha * s) - 1) • originalProjection j)

def extendedOriginalPulse (j : Fin 11) (s : ℝ) : Matrix Extended Extended ℂ :=
  unitPhase (alpha * s) •
    (1 + (unitPhase (alpha * s) - 1) • extendedProjection ⟨j.val, by omega⟩)

/-- This is the original unique ready configuration, with the one fixed ready extension. -/
def extendReady (q : Source) : Extended :=
  joinPath (q.1 9) ⟨q, rfl⟩ (readyTail (q.1 9))

/-- Source amplitudes are inserted without renormalization or loss of complementary columns. -/
def readyExtension (chi : Source → ℂ) : Extended → ℂ := globalVector chi readyVector

private theorem padded_ready_old (q : Source) (k : Fin 13) :
    (padPath 14 (extendReady q)).1 ⟨k.val, by omega⟩ = (padPath 10 q).1 k := by
  have hq : q.1 10 = false := q.2.2.1
  fin_cases k <;> simp [padPath, extendReady, joinPath, readyTail, hq]

private theorem padded_ready_tail (q r : Source) (k : Fin 17) (hk : 13 ≤ k.val) :
    (padPath 14 (extendReady q)).1 k = (padPath 14 (extendReady r)).1 k := by
  fin_cases k <;> first | omega | simp [padPath, extendReady, joinPath, readyTail]

private theorem projection_ready_entry (j : Fin 11) (q r : Source) :
    extendedProjection ⟨j.val, by omega⟩ (extendReady q) (extendReady r) =
      originalProjection j q r := by
  have hc : (∀ k : Fin 17, k.val ≠ j.val + 1 →
      (padPath 14 (extendReady q)).1 k = (padPath 14 (extendReady r)).1 k) ↔
      ∀ k : Fin 13, k.val ≠ j.val + 1 → (padPath 10 q).1 k = (padPath 10 r).1 k := by
    constructor
    · intro h k hk
      simpa only [padded_ready_old] using h ⟨k.val, by omega⟩ hk
    · intro h k hk
      by_cases hb : k.val < 13
      · simpa only [padded_ready_old] using h ⟨k.val, hb⟩ hk
      · exact padded_ready_tail q r k (by omega)
  unfold extendedProjection originalProjection
  simp only [Matrix.submatrix_apply, padEquiv, Equiv.coe_fn_mk, pathProjection]
  rw [hc]
  simp only [padded_ready_old, Nat.add_sub_cancel]

private theorem ready_of_tail (e : Extended) (h11 : e.1 11 = true)
    (h12 : e.1 12 = false) (h13 : e.1 13 = false) :
    e = extendReady (originalPart e) := by
  have ht := e.2.2.2 10
  have h10 : e.1 10 = false := by
    cases hb : e.1 10 <;> simp_all [adjacent]
  have h14 : e.1 14 = false := e.2.2.1
  apply Subtype.ext
  funext k
  by_cases hk : k.val < 10
  · simp [extendReady, joinPath, originalPart, hk]
  · have hs : k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 := by
      rcases k with ⟨k, hk'⟩
      simp only [Fin.mk.injEq]
      omega
    rcases hs with rfl | rfl | rfl | rfl | rfl <;>
      simp [extendReady, joinPath, readyTail, h10, h11, h12, h13, h14]

private theorem projection_outside_ready (j : Fin 11) (e : Extended) (q : Source)
    (he : e ≠ extendReady (originalPart e)) :
    extendedProjection ⟨j.val, by omega⟩ e (extendReady q) = 0 := by
  unfold extendedProjection
  simp only [Matrix.submatrix_apply, padEquiv, Equiv.coe_fn_mk, pathProjection]
  apply if_neg
  intro h
  apply he
  apply ready_of_tail
  · have hb := h.1 ⟨12, by omega⟩ (by change 12 ≠ j.val + 1; omega)
    simpa [padPath, extendReady, joinPath, readyTail] using hb
  · have hb := h.1 ⟨13, by omega⟩ (by change 13 ≠ j.val + 1; omega)
    simpa [padPath, extendReady, joinPath, readyTail] using hb
  · have hb := h.1 ⟨14, by omega⟩ (by change 14 ≠ j.val + 1; omega)
    simpa [padPath, extendReady, joinPath, readyTail] using hb

private theorem readyExtension_outside (chi : Source → ℂ) (e : Extended)
    (he : e ≠ extendReady (originalPart e)) : readyExtension chi e = 0 := by
  have hz : auxiliaryPart e ≠ readyTail ((originalPart e).1 9) := by
    intro h
    apply he
    unfold extendReady
    rw [← h]
    exact (join_split e).symm
  simp [readyExtension, globalVector, readyVector, Pi.single_apply, Ne.symm hz]

private theorem projection_ready_action (j : Fin 11) (chi : Source → ℂ) :
    extendedProjection ⟨j.val, by omega⟩ *ᵥ readyExtension chi =
      readyExtension (originalProjection j *ᵥ chi) := by
  classical
  ext e
  have hsum : (extendedProjection ⟨j.val, by omega⟩ *ᵥ readyExtension chi) e =
      ∑ q : Source, extendedProjection ⟨j.val, by omega⟩ e (extendReady q) * chi q := by
    change (∑ f : Extended, extendedProjection ⟨j.val, by omega⟩ e f *
      globalVector chi readyVector f) = _
    rw [← fullCarrierEquiv.symm.sum_comp]
    change (∑ p : FiberCarrier,
      extendedProjection ⟨j.val, by omega⟩ e
        (joinPath (p.1.1 9) ⟨p.1, rfl⟩ p.2) *
      globalVector chi readyVector (joinPath (p.1.1 9) ⟨p.1, rfl⟩ p.2)) = _
    rw [Fintype.sum_sigma]
    simp [globalVector_join, readyVector, Pi.single_apply, mul_ite, extendReady]
  rw [hsum]
  by_cases he : e = extendReady (originalPart e)
  · conv_lhs => rw [he]
    conv_rhs => rw [he]
    simp only [projection_ready_entry, readyExtension, extendReady, globalVector_join,
      readyVector, Pi.single_eq_same, mul_one, Matrix.mulVec, dotProduct]
  · rw [readyExtension_outside _ _ he]
    exact Finset.sum_eq_zero (fun q _ => by rw [projection_outside_ready j e q he, zero_mul])

/-- Every original full forward pulse preserves the single ready extension and intertwines
    the literal full native matrices; no source column is prepared independently. -/
theorem original_pulse_bridge (j : Fin 11) (s : ℝ) (chi : Source → ℂ) :
    extendedOriginalPulse j s *ᵥ readyExtension chi =
      readyExtension (originalPulse j s *ᵥ chi) := by
  simp only [extendedOriginalPulse, originalPulse, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.one_mulVec, projection_ready_action]
  ext e
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, readyExtension, globalVector]
  ring

/-- An arbitrary original finite forward word, on the one original ready vector. -/
def originalPreparation (a : List (Fin 11)) : Source → ℂ :=
  a.foldl (fun v j => originalPulse j 1 *ᵥ v) (Pi.single readySource 1)

def extendedPreparation (a : List (Fin 11)) : Extended → ℂ :=
  a.foldl (fun v j => extendedOriginalPulse j 1 *ᵥ v)
    (readyExtension (Pi.single readySource 1))

/-- The complete preparation bridge holds for every allowed original word and all coordinates. -/
theorem original_preparation_bridge (a : List (Fin 11)) :
    extendedPreparation a = readyExtension (originalPreparation a) := by
  have h (a : List (Fin 11)) (chi : Source → ℂ) :
      a.foldl (fun v j => extendedOriginalPulse j 1 *ᵥ v) (readyExtension chi) =
        readyExtension (a.foldl (fun v j => originalPulse j 1 *ᵥ v) chi) := by
    induction a generalizing chi with
    | nil => rfl
    | cons j a ih => simpa only [List.foldl_cons, original_pulse_bridge] using
        ih (originalPulse j 1 *ᵥ chi)
  exact h a (Pi.single readySource 1)

end D5.S3.Quantum.Dynamics.NativeReader
