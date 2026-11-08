/- GID: D5/S1/Dynamics/Symbolic/PreinjectiveFibers
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PreinjectiveFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniformly finite complete-output fibers of preinjective integer block codes. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativePreinjectivity
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-! Two finite collars encode every finite family in a complete-output fiber. -/

set_option autoImplicit false

noncomputable section

namespace D5.S1.Dynamics.Symbolic.PreinjectiveFibers

open Set Function
open PermutativeLifts.BipermutativeLift
open PermutativeLifts.BipermutativePreinjectivity

variable {A : Type*} {k : ℕ} {h : (Fin (k + 2) → A) → A}

/-- The two outer collars of width `k+1` around the integer interval `[a,b]`. -/
def collarPair (k : ℕ) (a b : ℤ) (x : ℤ → A) :
    (Fin (k + 1) → A) × (Fin (k + 1) → A) :=
  (fun j => x (a - (k + 1 : ℕ) + (j : ℕ)),
   fun j => x (b + 1 + (j : ℕ)))

private theorem code_splice_of_outer_collar {x z : ℤ → A} {a b : ℤ}
    (hcode : code h x = code h z)
    (hcollar : ∀ i ∈ Icc (a - (k + 1 : ℕ)) (b + (k + 1 : ℕ)),
      i ∉ Icc a b → x i = z i) :
    code h ((Icc a b).piecewise x z) = code h z := by
  classical
  funext i
  by_cases htouch : ∃ j : Fin (k + 2), i + (j : ℕ) ∈ Icc a b
  · obtain ⟨j, hj⟩ := htouch
    have hjbound := j.isLt
    have hw : window (k := k) ((Icc a b).piecewise x z) i = window x i := by
      funext t
      change (Icc a b).piecewise x z (i + (t : ℕ)) = x (i + (t : ℕ))
      by_cases ht : i + (t : ℕ) ∈ Icc a b
      · exact piecewise_eq_of_mem _ _ _ ht
      · rw [piecewise_eq_of_notMem _ _ _ ht]
        apply (hcollar _ ?_ ht).symm
        have htbound := t.isLt
        simp only [mem_Icc] at hj ⊢
        omega
    change h (window ((Icc a b).piecewise x z) i) = h (window z i)
    rw [hw]
    exact congrFun hcode i
  · apply congrArg h
    funext t
    change (Icc a b).piecewise x z (i + (t : ℕ)) = z (i + (t : ℕ))
    exact piecewise_eq_of_notMem _ _ _ (fun ht => htouch ⟨t, ht⟩)

/-- Over an arbitrary alphabet, each finite family of complete preimages admits
an injective encoding by two outer collars of width `k+1`. -/
theorem finite_family_two_collar_encoding (hpre : Preinjective h) (y : ℤ → A)
    (F : Finset (ℤ → A)) (hF : ∀ x ∈ F, code h x = y) :
    ∃ a b : ℤ, a ≤ b ∧ (F : Set (ℤ → A)).InjOn (collarPair k a b) := by
  classical
  let d (x z : ℤ → A) : ℤ :=
    if he : x = z then 0 else Classical.choose (Function.ne_iff.mp he)
  have hd {x z : ℤ → A} (hne : x ≠ z) : x (d x z) ≠ z (d x z) := by
    simpa only [d, dite_eq_right hne] using Classical.choose_spec (Function.ne_iff.mp hne)
  let S : Finset ℤ := insert 0 ((F ×ˢ F).image (fun p => d p.1 p.2))
  obtain ⟨a, ha⟩ := S.finite_toSet.bddBelow
  obtain ⟨b, hb⟩ := S.finite_toSet.bddAbove
  have hzero : (0 : ℤ) ∈ S := Finset.mem_insert_self _ _
  refine ⟨a, b, (ha hzero).trans (hb hzero), ?_⟩
  intro x hx z hz hpair
  by_contra hne
  have hdS : d x z ∈ S := by
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(x, z),
      Finset.mem_product.mpr ⟨hx, hz⟩, rfl⟩)
  have hcore : d x z ∈ Icc a b := ⟨ha hdS, hb hdS⟩
  have hcollar : ∀ i ∈ Icc (a - (k + 1 : ℕ)) (b + (k + 1 : ℕ)),
      i ∉ Icc a b → x i = z i := by
    intro i hi hout
    simp only [mem_Icc] at hi hout
    by_cases hia : i < a
    · let j : Fin (k + 1) := ⟨(i - (a - (k + 1 : ℕ))).toNat, by omega⟩
      have he := congrFun (congrArg Prod.fst hpair) j
      change x (a - (k + 1 : ℕ) + (j : ℕ)) = z (a - (k + 1 : ℕ) + (j : ℕ)) at he
      have hj : a - (k + 1 : ℕ) + (j : ℕ) = i := by dsimp [j]; omega
      simpa only [hj] using he
    · let j : Fin (k + 1) := ⟨(i - (b + 1)).toNat, by omega⟩
      have he := congrFun (congrArg Prod.snd hpair) j
      change x (b + 1 + (j : ℕ)) = z (b + 1 + (j : ℕ)) at he
      have hj : b + 1 + (j : ℕ) = i := by dsimp [j]; omega
      simpa only [hj] using he
  have hfin : FiniteDifference ((Icc a b).piecewise x z) z := by
    apply (finite_Icc a b).subset
    intro i hi
    by_contra hout
    exact hi (piecewise_eq_of_notMem _ _ _ hout)
  have heq := hpre hfin (code_splice_of_outer_collar ((hF x hx).trans (hF z hz).symm) hcollar)
  have he := congrFun heq (d x z)
  rw [piecewise_eq_of_mem _ _ _ hcore] at he
  exact hd hne he

/-- Every complete-output fiber is finite, with a bound independent of the
output and requiring only native finite-difference preinjectivity. -/
theorem finite_fiber_ncard_le [Finite A] (hpre : Preinjective h) (y : ℤ → A) :
    Set.Finite {x : ℤ → A | code h x = y} ∧
      Set.ncard {x : ℤ → A | code h x = y} ≤ (Nat.card A) ^ (2 * (k + 1)) := by
  classical
  let _ := Fintype.ofFinite A
  let B := (Nat.card A) ^ (2 * (k + 1))
  have hbound (F : Finset (ℤ → A)) (hF : ∀ x ∈ F, code h x = y) : F.card ≤ B := by
    obtain ⟨a, b, _hab, hinj⟩ := finite_family_two_collar_encoding hpre y F hF
    have hc := Fintype.card_le_of_injective
      (fun x : {x // x ∈ F} => collarPair k a b x.1)
      (fun x z he => Subtype.ext (hinj x.property z.property he))
    simpa [B, Fintype.card_prod, Fintype.card_fun, Nat.card_eq_fintype_card,
      pow_add, two_mul] using hc
  have hfinite : Set.Finite {x : ℤ → A | code h x = y} := by
    by_contra hinf
    obtain ⟨T, hT, hTf, hTc⟩ := Set.Infinite.exists_subset_ncard_eq hinf (B + 1)
    have hc := hbound hTf.toFinset (by intro x hx; exact hT (hTf.mem_toFinset.mp hx))
    rw [← Set.ncard_eq_toFinset_card T hTf, hTc] at hc
    omega
  refine ⟨hfinite, ?_⟩
  have hc := hbound hfinite.toFinset (by simp)
  simpa only [← Set.ncard_eq_toFinset_card _ hfinite] using hc

end D5.S1.Dynamics.Symbolic.PreinjectiveFibers
