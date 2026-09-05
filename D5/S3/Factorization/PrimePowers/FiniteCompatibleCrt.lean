/- GID: D5/S3/Factorization/PrimePowers/FiniteCompatibleCrt
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/FiniteCompatibleCrt
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite congruences glue exactly under pairwise gcd compatibility, uniquely modulo lcm. -/

import D5.S3.Factorization.PrimePowers.CompatibleResidueJointImage
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.PrimePowers.FiniteCompatibleCrt

open CompatibleResidueJointImage

/- Search: the frozen CompatibleResidueJointImage supplies binary gluing, and
   Mathlib's ZMod.prodEquivPi supplies finite coprime gluing. Neither supplies the
   finite noncoprime overlap induction below. -/

private theorem gcd_lcm_distrib (u v n : ℕ) :
    Nat.gcd (Nat.lcm u v) n = Nat.lcm (Nat.gcd u n) (Nat.gcd v n) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp only [Nat.lcm_zero_left, Nat.gcd_zero_left]
    exact Nat.dvd_antisymm (Nat.dvd_lcm_left _ _)
      (Nat.lcm_dvd dvd_rfl (Nat.gcd_dvd_right _ _))
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [Nat.lcm_zero_right, Nat.gcd_zero_left]
    exact Nat.dvd_antisymm (Nat.dvd_lcm_right _ _)
      (Nat.lcm_dvd (Nat.gcd_dvd_right _ _) dvd_rfl)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  apply Nat.eq_of_factorization_eq'
    (Nat.gcd_ne_zero_right hn)
    (Nat.lcm_ne_zero (Nat.gcd_ne_zero_right hn) (Nat.gcd_ne_zero_right hn))
  rw [Nat.factorization_gcd (Nat.lcm_ne_zero hu hv) hn,
    Nat.factorization_lcm hu hv,
    Nat.factorization_lcm (Nat.gcd_ne_zero_right hn) (Nat.gcd_ne_zero_right hn),
    Nat.factorization_gcd hu hn, Nat.factorization_gcd hv hn]
  ext p
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  exact inf_sup_right (u.factorization p) (v.factorization p) (n.factorization p)

private theorem gcd_finset_lcm {ι : Type*} (s : Finset ι) (m : ι → ℕ) (n : ℕ) :
    Nat.gcd (s.lcm m) n = s.lcm (fun i => Nat.gcd (m i) n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.lcm_insert, lcm_eq_nat_lcm, gcd_lcm_distrib, ih]

private theorem modEq_finset_lcm {ι : Type*} (s : Finset ι) (m : ι → ℕ) (x y : ℤ) :
    Int.ModEq ((s.lcm m : ℕ) : ℤ) x y ↔ ∀ i ∈ s, Int.ModEq (m i : ℤ) x y := by
  simp only [Int.modEq_iff_dvd, Int.natCast_dvd, Finset.lcm_dvd_iff]

private theorem binary_gluing (m n : ℕ) (a b : ℤ)
    (h : Int.ModEq (Nat.gcd m n : ℤ) a b) :
    ∃ x : ℤ, Int.ModEq (m : ℤ) x a ∧ Int.ModEq (n : ℤ) x b := by
  have rep (k : ℕ) (hk : Nat.gcd m n ∣ k) (z : ℤ) :
      ((ZMod.cast (z : ZMod k) : ℤ) : ZMod (Nat.gcd m n)) =
        (z : ZMod (Nat.gcd m n)) := by
    have he := congrArg (ZMod.castHom hk (ZMod (Nat.gcd m n)))
      (ZMod.intCast_zmod_cast (z : ZMod k))
    simpa only [map_intCast] using he
  have hc : ((a : ZMod m), (b : ZMod n)) ∈ compatibleResiduePairs m n := by
    change ((ZMod.cast (a : ZMod m) : ℤ) : ZMod (Nat.gcd m n)) =
      ((ZMod.cast (b : ZMod n) : ℤ) : ZMod (Nat.gcd m n))
    rw [rep m (Nat.gcd_dvd_left m n), rep n (Nat.gcd_dvd_right m n)]
    exact (ZMod.intCast_eq_intCast_iff a b _).mpr h
  rw [← joint_residue_image_eq_compatible_pairs] at hc
  obtain ⟨x, hx⟩ := hc
  refine ⟨x, (ZMod.intCast_eq_intCast_iff x a m).mp ?_,
    (ZMod.intCast_eq_intCast_iff x b n).mp ?_⟩
  · exact congrArg Prod.fst hx
  · exact congrArg Prod.snd hx

/- The live construction step: previous local congruences and pairwise overlaps
   imply compatibility with the next modulus across the previous lcm. -/
private theorem merged_overlap {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (a : ι → ℤ) (j : ι) (x : ℤ)
    (hx : ∀ i ∈ s, Int.ModEq (m i : ℤ) x (a i))
    (ha : ∀ i ∈ s, Int.ModEq (Nat.gcd (m i) (m j) : ℤ) (a i) (a j)) :
    Int.ModEq (Nat.gcd (s.lcm m) (m j) : ℤ) x (a j) := by
  rw [gcd_finset_lcm, modEq_finset_lcm]
  intro i hi
  exact ((hx i hi).of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))).trans
    (ha i hi)

private theorem finite_gluing {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → ℤ)
    (ha : ∀ i ∈ s, ∀ j ∈ s, Int.ModEq (Nat.gcd (m i) (m j) : ℤ) (a i) (a j)) :
    ∃ x : ℤ, ∀ i ∈ s, Int.ModEq (m i : ℤ) x (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨x, hx⟩ := ih (fun i hi k hk => ha i (Finset.mem_insert_of_mem hi)
      k (Finset.mem_insert_of_mem hk))
    have hover := merged_overlap s m a j x hx
      (fun i hi => ha i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self j s))
    obtain ⟨y, hy, hyj⟩ := binary_gluing (s.lcm m) (m j) x (a j) hover
    refine ⟨y, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hyj
    · exact ((modEq_finset_lcm s m y x).mp hy i hi).trans (hx i hi)

/-- Finite CRT, including compatible noncoprime families and the distinction
between a unique residue class and a nonunique ordinary integer representative. -/
theorem finite_crt_gluing {ι : Type*} [Fintype ι] (m : ι → ℕ) (a : ι → ℤ) :
    ((Pairwise fun i j => Nat.Coprime (m i) (m j)) →
      ∃! z : ZMod (∏ i, m i), ∀ i,
        ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i)) z =
          (a i : ZMod (m i))) ∧
    ((∀ i j, Int.ModEq (Nat.gcd (m i) (m j) : ℤ) (a i) (a j)) ↔
      ∃ x : ℤ, ∀ y : ℤ, (∀ i, Int.ModEq (m i : ℤ) y (a i)) ↔
        Int.ModEq ((Finset.univ.lcm m : ℕ) : ℤ) y x) ∧
    ((∀ i, m i ≠ 0) → ∀ x : ℤ, ∃ y : ℤ, y ≠ x ∧
      ∀ i, Int.ModEq (m i : ℤ) y x) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro hcop
    let e := ZMod.prodEquivPi m hcop
    refine ⟨e.symm (fun i => (a i : ZMod (m i))), ?_, ?_⟩
    · intro i
      exact (ZMod.prodEquivPi_apply m hcop _ i).symm.trans
        (congrFun (e.apply_symm_apply (fun i => (a i : ZMod (m i)))) i)
    · intro z hz
      apply e.injective
      rw [e.apply_symm_apply]
      funext i
      exact (ZMod.prodEquivPi_apply m hcop z i).trans (hz i)
  · constructor
    · intro ha
      obtain ⟨x, hx⟩ := finite_gluing Finset.univ m a (fun i _ j _ => ha i j)
      refine ⟨x, fun y => ?_⟩
      rw [modEq_finset_lcm]
      constructor
      · intro hy i _
        exact (hy i).trans (hx i (Finset.mem_univ i)).symm
      · intro hy i
        exact (hy i (Finset.mem_univ i)).trans (hx i (Finset.mem_univ i))
    · rintro ⟨x, hx⟩
      have hs := (hx x).mpr (Int.ModEq.refl x)
      intro i j
      exact ((hs i).of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))).symm.trans
        ((hs j).of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)))
  · intro hm x
    refine ⟨x + (∏ i, m i : ℕ), ?_, ?_⟩
    · have hp : (∏ i, m i : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hm i)
      intro he
      apply hp
      exact_mod_cast (show ((∏ i, m i : ℕ) : ℤ) = 0 by omega)
    · intro i
      apply Int.modEq_iff_dvd.mpr
      have hd : (m i : ℤ) ∣ (∏ i, m i : ℕ) :=
        Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem m (Finset.mem_univ i))
      simpa only [sub_add_cancel_left] using dvd_neg.mpr hd

#print axioms finite_crt_gluing

/- Fidelity witnesses: genuinely noncoprime compatible data, a nonempty residue
carrier, and inhabited hypotheses for the coprime and positive-modulus legs. -/
example : ∀ i j : Fin 3,
    Int.ModEq (Nat.gcd (![6, 10, 15] i) (![6, 10, 15] j) : ℤ)
      (![1, 7, 7] i) (![1, 7, 7] j) := by decide

example : Nonempty (ZMod 6) := ⟨0⟩

example : Pairwise (fun _ _ : Fin 3 => Nat.Coprime 1 1) := by
  intro i j hij
  exact Nat.coprime_one_left 1

example : ∀ _ : Fin 3, (6 : ℕ) ≠ 0 := by decide

end D5.S3.Factorization.PrimePowers.FiniteCompatibleCrt
