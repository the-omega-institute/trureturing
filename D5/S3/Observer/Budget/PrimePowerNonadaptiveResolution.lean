/- GID: D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/PrimePowerNonadaptiveResolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.Padics.RingHoms]
   utility: none
   digest: Final-fiber omissions characterize resolution and its attained call minimum. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy
open scoped BigOperators

/-- The largest congruence depth, including depth zero and the diagonal depth. -/
def depth (p e : ℕ) (c a : ZMod (p ^ e)) : ℕ :=
  ((Finset.range (e + 1)).filter fun d =>
    (ZMod.cast a : ZMod (p ^ d)) = ZMod.cast c).sup id

/-- A natural-center query caps the extended valuation; zero has capped value `e`. -/
noncomputable def query (p e : ℕ) [Fact p.Prime] (n : ℕ) (x : ℤ_[p]) : ℕ := by
  classical
  exact if x + n = 0 then e else min e (x + n).valuation

/-- Resolving geometry, the actual p-adic query bridge, and the attained minimum
of fixed query lengths. The length charges every coordinate, including repetitions. -/
theorem result (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    let π := primePowerProjection p (Nat.sub_le e 1)
    let K := (p - 1) * p ^ (e - 1)
    (∀ c a : ZMod (p ^ e), depth p e c a ≤ e ∧
      ∀ d ≤ e, d ≤ depth p e c a ↔
        (ZMod.cast a : ZMod (p ^ d)) = ZMod.cast c) ∧
    (∀ c a : ZMod (p ^ e), depth p e c a = e ↔ a = c) ∧
    (∀ (x : ℤ_[p]) (n : ℕ), query p e n x =
      depth p e (n : ZMod (p ^ e)) (-(PadicInt.toZModPow e x))) ∧
    Function.Surjective (fun x : ℤ_[p] => -(PadicInt.toZModPow e x)) ∧
    (∀ c : ZMod (p ^ e), ∃ n : ℕ, n < p ^ e ∧ (n : ZMod (p ^ e)) = c) ∧
    Fintype.card (ZMod (p ^ (e - 1))) = p ^ (e - 1) ∧
    (∀ r : ZMod (p ^ (e - 1)), (Finset.univ.filter fun a => π a = r).card = p) ∧
    (∀ S : Finset (ZMod (p ^ e)),
      Function.Injective (jointReadout (fun c : S => depth p e c.1)) ↔
        ∀ r, (Sᶜ.filter fun a => π a = r).card ≤ 1) ∧
    (∃ S : Finset (ZMod (p ^ e)), S.card = K ∧
      (∀ r, (Sᶜ.filter fun a => π a = r).card = 1) ∧
      Function.Injective (jointReadout (fun c : S => depth p e c.1))) ∧
    IsLeast {k : ℕ | ∃ n : Fin k → ℕ,
      Function.FactorsThrough (PadicInt.toZModPow e : ℤ_[p] → ZMod (p ^ e))
        (jointReadout (fun i => query p e (n i)))} K := by
  classical
  let X := ZMod (p ^ e)
  let Y := ZMod (p ^ (e - 1))
  let π := primePowerProjection p (Nat.sub_le e 1)
  have hp := (Fact.out : p.Prime)
  have hp2 := hp.two_le
  have hpow : p ^ e = p ^ (e - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel he]
  have hpos : 0 < p ^ (e - 1) := pow_pos hp.pos _
  have compose (d j : ℕ) (hdj : d ≤ j) (hje : j ≤ e) (a : X) :
      (ZMod.cast (ZMod.cast a : ZMod (p ^ j)) : ZMod (p ^ d)) = ZMod.cast a :=
    DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow p hdj) (pow_dvd_pow p hje)) a
  have bound (c a : X) : depth p e c a ≤ e := by
    exact Finset.sup_le fun d hd => Nat.le_of_lt_succ (Finset.mem_range.mp
      (Finset.mem_filter.mp hd).1)
  have threshold (c a : X) (d : ℕ) (hd : d ≤ e) : d ≤ depth p e c a ↔
      (ZMod.cast a : ZMod (p ^ d)) = ZMod.cast c := by
    constructor
    · intro h
      have hn : ((Finset.range (e + 1)).filter fun j =>
          (ZMod.cast a : ZMod (p ^ j)) = ZMod.cast c).Nonempty := by
        refine ⟨0, Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
        change (ZMod.cast a : ZMod 1) = ZMod.cast c
        exact Subsingleton.elim _ _
      obtain ⟨j, hj, hmax⟩ := Finset.sup_mem_of_nonempty (f := id) hn
      have hj' := Finset.mem_filter.mp hj
      have hje := Nat.le_of_lt_succ (Finset.mem_range.mp hj'.1)
      have hdj : d ≤ j := by simpa [depth, ← hmax] using h
      have hh := congrArg (fun z : ZMod (p ^ j) =>
        (ZMod.cast z : ZMod (p ^ d))) hj'.2
      simpa only [compose d j hdj hje] using hh
    · intro h
      exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hd), h⟩)
  have top (c a : X) : depth p e c a = e ↔ a = c := by
    constructor
    · intro h
      simpa only [ZMod.cast_id] using (threshold c a e le_rfl).mp h.ge
    · intro h
      exact (bound c a).antisymm ((threshold c a e le_rfl).mpr (by simp [h]))
  have fibers (r : Y) : (Finset.univ.filter fun a : X => π a = r).card = p := by
    have surj : Function.Surjective π := ZMod.castHom_surjective _
    have same (s : Y) : (Finset.univ.filter fun a : X => π a = s).card =
        (Finset.univ.filter fun a : X => π a = r).card :=
      AddMonoidHom.card_fiber_eq_of_mem_range π.toAddMonoidHom (surj s) (surj r)
    have count := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := π) (fun _ _ => Finset.mem_univ _)
    rw [Finset.sum_congr rfl (fun s _ => same s)] at count
    simp only [Finset.card_univ, Finset.sum_const, nsmul_eq_mul, X, Y, ZMod.card] at count
    exact Nat.eq_of_mul_eq_mul_left hpos (count.symm.trans hpow)
  have omitted (a b c : X) (ha : a ≠ c) (hb : b ≠ c) (hab : π a = π b) :
      depth p e c a = depth p e c b := by
    have transfer (a b : X) (ha : a ≠ c) (hab : π a = π b) :
        depth p e c a ≤ depth p e c b := by
      have hd : depth p e c a ≤ e - 1 := by
        have := bound c a
        have := (top c a).not.mpr ha
        omega
      have hr := congrArg (fun z : Y =>
        (ZMod.cast z : ZMod (p ^ depth p e c a))) hab
      have hr' : (ZMod.cast a : ZMod (p ^ depth p e c a)) = ZMod.cast b := by
        simpa only [π, primePowerProjection, ZMod.castHom_apply,
          compose _ _ hd (Nat.sub_le e 1)] using hr
      exact (threshold c b _ (bound c a)).mpr
        (hr'.symm.trans ((threshold c a _ (bound c a)).mp le_rfl))
    exact (transfer a b ha hab).antisymm (transfer b a hb hab.symm)
  have criterion (S : Finset X) :
      Function.Injective (jointReadout (fun c : S => depth p e c.1)) ↔
        ∀ r, (Sᶜ.filter fun a => π a = r).card ≤ 1 := by
    constructor
    · intro hinj r
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨haS, har⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbS, hbr⟩ := Finset.mem_filter.mp hb
      apply hinj
      funext c
      exact omitted a b c.1 (fun h => (Finset.mem_compl.mp haS) (h ▸ c.2))
        (fun h => (Finset.mem_compl.mp hbS) (h ▸ c.2)) (har.trans hbr.symm)
    · intro h a b hab
      have reply (c : X) (hc : c ∈ S) : depth p e c a = depth p e c b :=
        congrFun hab ⟨c, hc⟩
      by_cases ha : a ∈ S
      · exact ((top a b).mp ((reply a ha).symm.trans ((top a a).mpr rfl))).symm
      by_cases hb : b ∈ S
      · exact (top b a).mp ((reply b hb).trans ((top b b).mpr rfl))
      have same : π a = π b := by
        obtain ⟨c, hcS, hca⟩ : ∃ c ∈ S, π c = π a := by
          by_contra hnone
          have hsub : (Finset.univ.filter fun c : X => π c = π a) ⊆
              Sᶜ.filter fun c => π c = π a := by
            intro c hc
            have hcπ := (Finset.mem_filter.mp hc).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr
              (fun hcS => hnone ⟨c, hcS, hcπ⟩), hcπ⟩
          have := (Finset.card_le_card hsub).trans (h (π a))
          rw [fibers] at this
          omega
        have hca' : e - 1 ≤ depth p e c a :=
          (threshold c a _ (Nat.sub_le e 1)).mpr hca.symm
        have hcb := (threshold c b _ (Nat.sub_le e 1)).mp ((reply c hcS) ▸ hca')
        exact hca.symm.trans hcb.symm
      exact Finset.card_le_one.mp (h (π a)) a (by simp [ha]) b (by simp [hb, same])
  have lower (S : Finset X)
      (hS : Function.Injective (jointReadout (fun c : S => depth p e c.1))) :
      (p - 1) * p ^ (e - 1) ≤ S.card := by
    have inj : Set.InjOn π (Sᶜ : Finset X) := by
      intro a ha b hb hab
      exact Finset.card_le_one.mp ((criterion S).mp hS (π a)) a
        (Finset.mem_filter.mpr ⟨ha, rfl⟩) b (Finset.mem_filter.mpr ⟨hb, hab.symm⟩)
    have card := (Finset.card_image_of_injOn inj).symm.trans_le
      (Finset.card_le_univ (Sᶜ.image π))
    have total := S.card_add_card_compl
    rw [ZMod.card] at card total
    rw [Nat.sub_mul, one_mul, Nat.mul_comm]
    omega
  let sectionMap : Y → X := fun r => r.val
  have sectionRight (r : Y) : π (sectionMap r) = r := by
    simp [sectionMap, π, primePowerProjection]
  let S : Finset X := (Finset.univ.image sectionMap)ᶜ
  have single (r : Y) : Sᶜ.filter (fun a => π a = r) = {sectionMap r} := by
    ext a
    simp only [S, compl_compl, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨s, rfl⟩, hs⟩
      simpa only [sectionRight] using congrArg sectionMap hs
    · rintro rfl
      exact ⟨⟨r, rfl⟩, sectionRight r⟩
  have Sresolves : Function.Injective (jointReadout (fun c : S => depth p e c.1)) :=
    (criterion S).mpr (fun r => by rw [single]; simp)
  have Scard : S.card = (p - 1) * p ^ (e - 1) := by
    have inj : Function.Injective sectionMap := fun a b h =>
      (sectionRight a).symm.trans ((congrArg π h).trans (sectionRight b))
    simp only [S, Finset.card_compl, Finset.card_image_of_injective _ inj,
      Finset.card_univ, X, Y, ZMod.card]
    rw [hpow, Nat.sub_mul, one_mul, Nat.mul_comm]
  have bridge (x : ℤ_[p]) (n : ℕ) : query p e n x =
      depth p e (n : X) (-(PadicInt.toZModPow e x)) := by
    have qb : query p e n x ≤ e := by unfold query; split <;> simp_all
    have qt (d : ℕ) (hd : d ≤ e) : d ≤ query p e n x ↔
        PadicInt.toZModPow d (x + (n : ℤ_[p])) = 0 := by
      by_cases hz : x + (n : ℤ_[p]) = 0
      · simp [query, hz, hd]
      rw [query, if_neg hz, le_min_iff, and_iff_right hd]
      rw [← PadicInt.mem_span_pow_iff_le_valuation _ hz,
        ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have reduction (d : ℕ) (hd : d ≤ e) :
        (ZMod.cast (-(PadicInt.toZModPow e x)) : ZMod (p ^ d)) =
          ZMod.cast (n : X) ↔ PadicInt.toZModPow d (x + (n : ℤ_[p])) = 0 := by
      rw [ZMod.cast_neg (pow_dvd_pow p hd), PadicInt.cast_toZModPow _ _ hd,
        ZMod.cast_natCast (pow_dvd_pow p hd), map_add, map_natCast,
        neg_eq_iff_add_eq_zero]
    apply Nat.le_antisymm
    · exact (threshold _ _ _ qb).mpr ((reduction _ qb).mpr ((qt _ qb).mp le_rfl))
    · exact (qt _ (bound _ _)).mpr
        ((reduction _ (bound _ _)).mp ((threshold _ _ _ (bound _ _)).mp le_rfl))
  have realized : Function.Surjective (fun x : ℤ_[p] => -(PadicInt.toZModPow e x)) := by
    intro a
    refine ⟨-(a.val : ℤ_[p]), ?_⟩
    simp
  have support {k : ℕ} (cs : Fin k → X) :
      Function.Injective (jointReadout (fun i => depth p e (cs i))) ↔
      Function.Injective (jointReadout
        (fun c : (Finset.univ.image cs) => depth p e c.1)) := by
    constructor
    · intro h a b hab
      apply h
      funext i
      exact congrFun hab ⟨cs i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    · intro h a b hab
      apply h
      funext c
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp c.2
      simpa only [jointReadout, ← hi] using congrFun hab i
  have actual {k : ℕ} (ns : Fin k → ℕ) :
      Function.FactorsThrough (PadicInt.toZModPow e : ℤ_[p] → X)
        (jointReadout (fun i => query p e (ns i))) ↔
      Function.Injective (jointReadout (fun i => depth p e (ns i : X))) := by
    constructor
    · intro h a b hab
      obtain ⟨x, rfl⟩ := realized a
      obtain ⟨y, rfl⟩ := realized b
      apply congrArg Neg.neg
      apply h
      funext i
      simpa only [jointReadout, bridge] using congrFun hab i
    · intro h x y hab
      apply neg_injective
      apply h
      funext i
      simpa only [jointReadout, bridge] using congrFun hab i
  refine ⟨fun c a => ⟨bound c a, threshold c a⟩, top, bridge, realized,
    fun c => ⟨c.val, ZMod.val_lt c, ZMod.natCast_zmod_val c⟩, ZMod.card _, fibers,
    criterion, ⟨S, Scard, fun r => by rw [single]; simp, Sresolves⟩, ?_⟩
  constructor
  · let enum := S.equivFinOfCardEq Scard
    refine ⟨fun i => (enum.symm i).1.val, (actual _).mpr ?_⟩
    intro a b hab
    apply Sresolves
    funext c
    have hh := congrFun hab (enum c)
    simpa only [jointReadout, Equiv.symm_apply_apply, X, ZMod.natCast_zmod_val] using hh
  · rintro k ⟨ns, hns⟩
    have hh := lower (Finset.univ.image (fun i => (ns i : X)))
      ((support _).mp ((actual ns).mp hns))
    exact hh.trans (by simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := fun i => (ns i : X))))

#print axioms result

end D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution
