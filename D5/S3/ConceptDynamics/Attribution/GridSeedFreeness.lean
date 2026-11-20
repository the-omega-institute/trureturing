/- GID: D5/S3/ConceptDynamics/Attribution/GridSeedFreeness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/GridSeedFreeness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Universal freeness on the complete probability grid is equivalent to prime divisibility. -/

import D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers
import D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.GridSeedFreeness

open Finset
open Equiv.Perm
open D5.S3.ConceptDynamics.Attribution.FiniteKernelStabilizers (stabilizer_possible_iff)
open D5.S3.ConceptDynamics.Attribution.PermutationGridSupport (CalibratingLaw)

private abbrev Profile (k m : ℕ) := {a : Fin k → ℕ // ∑ i, a i = m}

private abbrev relabel {k m : ℕ} (g : Equiv.Perm (Fin k)) (x : Profile k m) :
    Profile k m :=
  ⟨fun i => x.val (g⁻¹ i), (Equiv.sum_comp (g⁻¹ : Equiv.Perm (Fin k)) x.val).trans x.property⟩

private instance profileAction {k m : ℕ} : MulAction (Equiv.Perm (Fin k)) (Profile k m) where
  smul := relabel
  one_smul p := Subtype.ext (funext fun i => by simp)
  mul_smul g h p := Subtype.ext (funext fun i => by
    change p.val ((g * h)⁻¹ i) = p.val (h⁻¹ (g⁻¹ i))
    rw [mul_inv_rev, Equiv.Perm.mul_apply])

private theorem fixed_positive_of_cycle {k m p : ℕ} {g : Equiv.Perm (Fin k)}
    (cycle : g.IsCycle) (length : g.support.card = p) (missing : ¬ p ∣ m)
    (x : Profile k m) (fixed : g • x = x) :
    ∃ i : Fin k, 0 < x.val i ∧ g i = i := by
  classical
  obtain ⟨i, hi⟩ := cycle
  have constant (j : Fin k) : x.val (g j) = x.val j := by
    have eq := congrArg (fun a : Profile k m => a.val (g j)) fixed
    change x.val (g⁻¹ (g j)) = x.val (g j) at eq
    change x.val (g.symm (g j)) = x.val (g j) at eq
    rw [g.symm_apply_apply] at eq
    exact eq.symm
  have power (n : ℕ) : ∀ j : Fin k, x.val ((g ^ n) j) = x.val j := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro j
      rw [pow_succ', Equiv.Perm.mul_apply, constant, ih]
  by_contra! absent
  have masses (j : Fin k) : x.val j = if j ∈ g.support then x.val i else 0 := by
    by_cases hj : j ∈ g.support
    · obtain ⟨n, eq⟩ := IsCycle.exists_pow_eq ⟨i, hi⟩ hi.1 (mem_support.mp hj)
      exact (eq ▸ power n i).trans (ite_eq_left hj).symm
    · have eq : g j = j := not_ne_iff.mp (fun h => hj (mem_support.mpr h))
      have none : ¬ 0 < x.val j := fun h => absent j h eq
      simp [hj, Nat.eq_zero_of_not_pos none]
  apply missing
  use x.val i
  calc
    m = ∑ j, x.val j := x.property.symm
    _ = ∑ j, if j ∈ g.support then x.val i else 0 := Finset.sum_congr rfl fun j _ => masses j
    _ = p * x.val i := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
        nsmul_eq_mul, length, Nat.cast_id]

private theorem nonfree_of_missing_prime {k m p : ℕ} (positive : 0 < m)
    (prime : p.Prime) (leK : p ≤ k) (missing : ¬ p ∣ m) :
    ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin k)) S) (w : S → ℝ)
      (f : Profile k m → S → Fin k), CalibratingLaw S w f ∧
      ∃ s : S, MulAction.stabilizer (Equiv.Perm (Fin k)) s ≠ ⊥ := by
  classical
  let G := Equiv.Perm (Fin k)
  obtain ⟨g, shape⟩ := (Equiv.Perm.exists_with_cycleType_iff (α := Fin k)
    (m := ({p} : Multiset ℕ))).mpr (by simpa using And.intro leK prime.two_le)
  have cyc : g.IsCycle := card_cycleType_eq_one.mp (by simp [shape])
  have length : g.support.card = p := by simpa only [cyc.cycleType, Multiset.singleton_inj] using shape
  let H := Subgroup.zpowers g
  have Hcard : Nat.card H = p := (Nat.card_zpowers g).trans (cyc.orderOf.trans length)
  let _ : Fact p.Prime := ⟨prime⟩
  have generator (h : H) (ne : h ≠ 1) : ∃ j : ℤ, h ^ j = ⟨g, Subgroup.mem_zpowers g⟩ :=
    mem_zpowers_of_prime_card Hcard ne
  let P (x : Profile k m) (i : Fin k) : ℝ := (x.val i : ℝ) / m
  have mpos : (0 : ℝ) < m := by exact_mod_cast positive
  have normal (x : Profile k m) : ∑ i, P x i = 1 := by
    dsimp [P]
    rw [← Finset.sum_div, ← Nat.cast_sum, x.property, div_self mpos.ne']
  have equivariant (h : G) (x : Profile k m) (i : Fin k) :
      P (h • x) (h • i) = P x i := by
    change ((x.val (h⁻¹ (h i)) : ℕ) : ℝ) / m = _
    change ((x.val (h.symm (h i)) : ℕ) : ℝ) / m = _
    rw [h.symm_apply_apply]
  have support (x : Profile k m) :
      ∃ i : Fin k, 0 < P x i ∧ ∀ h : H, h • x = x → h • i = i := by
    by_cases fixed : g • x = x
    · obtain ⟨i, ipos, ifix⟩ := fixed_positive_of_cycle cyc length missing x fixed
      refine ⟨i, div_pos (by exact_mod_cast ipos) mpos, ?_⟩
      intro h _
      obtain ⟨j, eq⟩ := h.property
      change h.val • i = i
      rw [← eq]
      exact MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer G i).zpow_mem
        (MulAction.mem_stabilizer_iff.mpr (show g • i = i from ifix)) j)
    · have somePositive : ∃ i : Fin k, 0 < x.val i := by
        have sumPos : 0 < ∑ i, x.val i := x.property.symm ▸ positive
        simpa using (Finset.sum_pos_iff_of_nonneg fun i (_ : i ∈ Finset.univ) => Nat.zero_le (x.val i)).mp sumPos
      obtain ⟨i, ipos⟩ := somePositive
      refine ⟨i, div_pos (by exact_mod_cast ipos) mpos, ?_⟩
      intro h hx
      have eq : h = 1 := by
        by_contra ne
        obtain ⟨j, hj⟩ := generator h ne
        have fixes : (h ^ j) • x = x := MulAction.mem_stabilizer_iff.mp
          ((MulAction.stabilizer H x).zpow_mem (MulAction.mem_stabilizer_iff.mpr hx) j)
        rw [hj] at fixes
        exact fixed fixes
      rw [eq, one_smul]
  let encode (x : Profile k m) (i : Fin k) : Fin (m + 1) :=
    ⟨x.val i, Nat.lt_succ_of_le (by
      calc
        x.val i ≤ ∑ j, x.val j := Finset.single_le_sum
          (f := x.val) (fun j _ => Nat.zero_le (x.val j)) (Finset.mem_univ i)
        _ = m := x.property)⟩
  have encode_injective : Function.Injective encode := by
    intro a b same
    apply Subtype.ext
    funext i
    exact congrArg (fun data : Fin k → Fin (m + 1) => (data i).val) same
  let _ : Finite (Profile k m) := Finite.of_injective encode encode_injective
  let _ : Fintype (Profile k m) := Fintype.ofFinite _
  obtain ⟨S, fS, act, w, f, pos, total, wi, mass, equiv, s, stab⟩ :=
    (stabilizer_possible_iff P (fun x i => div_nonneg (Nat.cast_nonneg _) mpos.le)
      normal equivariant H).mpr support
  refine ⟨S, fS, act, w, f, ⟨pos, total, wi, mass, equiv⟩, s, ?_⟩
  intro eq
  have mem := stab (Subgroup.mem_zpowers g)
  rw [eq, Subgroup.mem_bot] at mem
  exact cyc.ne_one mem

/-- Prime divisibility characterizes when every calibrating seed action on the
complete probability grid of positive denominator is free. -/
theorem every_calibrating_law_free_iff {k m : ℕ} (positive : 0 < m) :
    (∀ (S : Type) [Fintype S] [MulAction (Equiv.Perm (Fin k)) S] (w : S → ℝ)
      (f : Profile k m → S → Fin k), CalibratingLaw S w f →
      ∀ s : S, MulAction.stabilizer (Equiv.Perm (Fin k)) s = ⊥) ↔
      (∀ p : ℕ, p.Prime → p ≤ k → p ∣ m) := by
  classical
  constructor
  · intro all p prime bound
    by_contra missing
    obtain ⟨S, _, _, w, f, law, s, nonfree⟩ :=
      nonfree_of_missing_prime positive prime bound missing
    exact nonfree (all S w f law s)
  · intro divisible S _ _ w f law
    obtain ⟨wpos, _, _, mass, covariant⟩ := law
    have mpos : 0 < (m : ℝ) := by exact_mod_cast positive
    let scaled (s : S) := (m : ℝ) * w s
    have calibrated (x : Profile k m) (i : Fin k) :
        (∑ s, if f x s = i then scaled s else 0) = (x.val i : ℝ) := by
      have term (s : S) : (if f x s = i then scaled s else 0) =
          (m : ℝ) * (if f x s = i then w s else 0) := by
        by_cases hit : f x s = i <;> simp [scaled, hit]
      rw [Finset.sum_congr rfl (fun s _ => term s), ← Finset.mul_sum, mass, mul_comm]
      exact div_mul_cancel₀ _ mpos.ne'
    exact D5.S3.ConceptDynamics.Attribution.PrimeCycleSeedFreeness.free_of_prime_divisibility
      (fun p prime le => divisible p prime (by simpa only [Fintype.card_fin] using le))
      scaled (fun s => mul_pos mpos (wpos s)) f calibrated covariant

end D5.S3.ConceptDynamics.Attribution.GridSeedFreeness
