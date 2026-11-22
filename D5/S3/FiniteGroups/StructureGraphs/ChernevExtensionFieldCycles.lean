/- GID: D5/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/StructureGraphs/ChernevExtensionFieldCycles
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Nontrivial directed cycles in finite extension fields outside order four. -/

/-
proof_shape: result: content
escape_witness: cycle_of_odd_degree, via the invariant complement of the prime field.
admission_basis: open-problem-resolution (#27776, Proved)
Direct frozen dependency: D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound.finite_orbit_and_readout_eventually_periodic
Frozen module statement_id: sha256:259d232d95c1ca485bdaeb0bf7eb8d9a839164d9e3964dab0743ddec9dc41953
-/

import D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound
import Mathlib.Combinatorics.Digraph.Basic

/-! Chernev–Chernev, arXiv:2611.07521v1, Definition 3.1 and Hypothesis 6.1. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Trureturing.StructureGraphCycles

open Function Polynomial

/-- The successor in the structure graph of a ring. -/
def phi {R : Type*} [Ring R] (v : R × R) : R × R :=
  (v.1 + v.2, v.1 * v.2)

/-- The directed graph of the sum-and-product map, including loops. -/
def structureGraph (R : Type*) [Ring R] : Digraph (R × R) where
  Adj v w := phi v = w

/-- A positive-length cyclic list of distinct vertices with all its directed edges. -/
def IsDirectedCycle {V : Type*} (G : Digraph V) (r : ℕ) (v : Fin r → V) : Prop :=
  0 < r ∧ Injective v ∧
    ∀ i j : Fin r, j.val = (i.val + 1) % r → G.Adj (v i) (v j)

/-- Chernev–Chernev Hypothesis 6.1. -/
def claim : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (p n : ℕ),
    Nat.Prime p → 1 < n → Fintype.card K = p ^ n → Fintype.card K ≠ 4 →
      ∃ (r : ℕ) (v : Fin r → K × K),
        1 < r ∧ IsDirectedCycle (structureGraph K) r v

private abbrev HasCycle (K : Type*) [Ring K] : Prop :=
  ∃ (r : ℕ) (v : Fin r → K × K), 1 < r ∧ IsDirectedCycle (structureGraph K) r v

private def g {K : Type*} [Ring K] (x : K) : K := x - x ^ 2

private theorem exists_cycle_of_periodic {K : Type*} [Ring K] {m : ℕ} {v : K × K}
    (hm : 0 < m) (hperiodic : IsPeriodicPt phi m v) (hmoves : phi v ≠ v) : HasCycle K := by
  let r := minimalPeriod phi v
  have hr : 0 < r := hperiodic.minimalPeriod_pos hm
  have hrone : r ≠ 1 := fun h => hmoves (minimalPeriod_eq_one_iff_isFixedPt.mp h)
  refine ⟨r, fun i => (phi^[i.val]) v, by omega, hr, ?_, ?_⟩
  · intro i j hij
    exact Fin.ext ((iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp hij)
  · intro i j hij
    change phi ((phi^[i.val]) v) = (phi^[j.val]) v
    rw [hij, (isPeriodicPt_minimalPeriod phi v).iterate_mod_apply, iterate_succ_apply']

private theorem phi_two {K : Type*} [CommRing K] (x : K) :
    (phi^[2]) (-1, x) = (-1, g x) := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, iterate_add_apply, iterate_one]
  apply Prod.ext <;> simp only [phi, g] <;> ring

private theorem cycle_of_g_periodic {K : Type*} [CommRing K] {m : ℕ} {x : K}
    (hm : 0 < m) (hx : x ≠ 0) (h : IsPeriodicPt g m x) : HasCycle K := by
  have hlift : Semiconj (fun y : K => ((-1 : K), y)) g (phi^[2]) := fun y => (phi_two y).symm
  refine exists_cycle_of_periodic (m := 2 * m) (v := (-1, x)) (Nat.mul_pos (by decide) hm) ?_ ?_
  · rw [IsPeriodicPt, IsFixedPt, iterate_mul]
    exact (hlift.iterate_right m x).symm.trans (congrArg (fun y : K => ((-1 : K), y)) h)
  · intro hfix
    apply hx
    have hfirst : (-1 : K) + x = -1 := congrArg Prod.fst hfix
    exact add_left_cancel (hfirst.trans (add_zero _).symm)

private theorem cycle_of_odd_degree {p n : ℕ} [Fact p.Prime]
    (hn : 1 < n) (hodd : Odd n) : HasCycle (GaloisField p n) := by
  classical
  let F := ZMod p
  let K := GaloisField p n
  let incl := algebraMap F K
  let : Fintype K := Fintype.ofFinite K
  have hn0 : n ≠ 0 := by omega
  have hcard : Fintype.card K = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p n hn0
  have hproper : ¬ Surjective incl := by
    intro hsurj
    have hle := Fintype.card_le_of_surjective incl hsurj
    rw [hcard, show Fintype.card F = p from ZMod.card p] at hle
    have hlt : p ^ 1 < p ^ n := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hn
    exact (not_lt_of_ge hle) (by simpa only [pow_one] using hlt)
  obtain ⟨x₀, hx₀⟩ : ∃ x : K, x ∉ Set.range incl := by
    simpa only [Surjective, Set.mem_range, not_forall] using hproper
  have hinvariant (x : K) (hx : x ∉ Set.range incl) : g x ∉ Set.range incl := by
    rintro ⟨c, hc⟩
    let q : F[X] := X ^ 2 - X + C c
    have hqdegree : q.degree = 2 := by
      rw [show q = X ^ 2 + (-X + C c) by unfold q; ring,
        degree_add_eq_left_of_degree_lt]
      · simp
      · refine (degree_add_le ..).trans_lt ?_
        apply max_lt
        · simp
        · exact degree_C_le.trans_lt (by rw [degree_X_pow]; decide)
    have hq0 : q ≠ 0 := by
      intro hzero
      simp [hzero] at hqdegree
    have hqroot : aeval x q = 0 := by
      simp [q, show algebraMap F K c = g x from hc, g]
    have hxmin := IsIntegral.of_finite F x
    have hpos := minpoly.natDegree_pos hxmin
    have hle : (minpoly F x).natDegree ≤ 2 := by
      have hqNat := (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 2)).mp hqdegree
      exact hqNat ▸ natDegree_le_natDegree (minpoly.degree_le_of_ne_zero F x hq0 hqroot)
    have hdvd : (minpoly F x).natDegree ∣ n := by
      simpa only [show Module.finrank F K = n from GaloisField.finrank p hn0]
        using minpoly.degree_dvd hxmin
    have hneq : (minpoly F x).natDegree ≠ 2 := by
      intro heq
      rw [heq] at hdvd
      exact hodd.not_two_dvd_nat hdvd
    exact hx (minpoly.natDegree_eq_one_iff.mp (by omega))
  let S := {x : K // x ∉ Set.range incl}
  let T : S → S := fun x => ⟨g x.val, hinvariant x.val x.property⟩
  let x₁ : S := ⟨x₀, hx₀⟩
  open D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound in
  obtain ⟨μ, m, hm, _, htail⟩ :=
    finite_orbit_and_readout_eventually_periodic T (fun x : S => x.val) x₁
  let y := (T^[μ]) x₁
  have hperiodic : IsPeriodicPt T m y := by
    exact (iterate_add_apply T m μ x₁).symm.trans (by simpa only [Nat.add_comm m μ] using
      (htail μ le_rfl).1)
  have hsemiconj : Semiconj (fun x : S => x.val) T g := fun _ => rfl
  have hne : y.val ≠ 0 := fun hy => y.property ⟨0, (map_zero incl).trans hy.symm⟩
  exact cycle_of_g_periodic hm hne (hperiodic.map hsemiconj)

private theorem map_cycle {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (h : HasCycle K) : HasCycle L := by
  obtain ⟨r, v, hr, hrpos, hinj, hedge⟩ := h
  let w : Fin r → L × L := fun i => (f (v i).1, f (v i).2)
  refine ⟨r, w, hr, hrpos, ?_, ?_⟩
  · intro i j hij
    exact hinj (Prod.ext (f.injective (congrArg Prod.fst hij))
      (f.injective (congrArg Prod.snd hij)))
  · intro i j hij
    have hstep : phi (v i) = v j := hedge i j hij
    change phi (w i) = w j
    simpa only [w, phi, Prod.map, map_add, map_mul] using congrArg (Prod.map f f) hstep

private theorem cycle_of_sq_neg_one {K : Type*} [Field K] {a : K}
    (htwo : (2 : K) ≠ 0) (ha : a ^ 2 = -1) :
    ∃ v : Fin 4 → K × K, IsDirectedCycle (structureGraph K) 4 v := by
  have hne : (1 : K) ≠ -1 := by
    intro h
    apply htwo
    linear_combination h
  have hne₁ : a ≠ 1 := fun h => hne (by simpa [h] using ha)
  have hne₂ : a ≠ -1 := fun h => hne (by simpa [h] using ha)
  have hne₃ : a ≠ -a := by
    intro h
    have haz : a = 0 := (mul_eq_zero.mp (show 2 * a = 0 by linear_combination h)).resolve_left htwo
    simp [haz] at ha
  have hne₄ : 1 + a ≠ 1 - a := by
    intro h
    exact hne₃ (by linear_combination h)
  let v : Fin 4 → K × K := ![(-1, 1 + a), (a, -1 - a), (-1, 1 - a), (-a, -1 + a)]
  refine ⟨v, by decide, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [v, Prod.mk.injEq, neg_eq_iff_eq_neg]
  · have hedge (i : Fin 4) : phi (v i) = v (i + 1) := by
      fin_cases i <;>
        apply Prod.ext <;>
        dsimp [v, phi] <;>
        ring_nf <;> rw [ha] <;> ring
    intro i j hij
    exact (hedge i).trans (congrArg v (Fin.ext (by
      change (i.val + 1) % 4 = j.val
      exact hij.symm)))

private theorem cycle_of_odd_char_even_degree {p n : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hn : n ≠ 0) (heven : Even n) : HasCycle (GaloisField p n) := by
  let E := GaloisField p 2
  let : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by decide)
  have hmod : p ^ 2 % 4 ≠ 3 := by
    rw [Nat.pow_mod]
    have hlt : p % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases h : p % 4 <;> decide
  obtain ⟨a, ha⟩ := (FiniteField.isSquare_neg_one_iff.mpr (hcard ▸ hmod) : IsSquare (-1 : E))
  have ha' : a ^ 2 = -1 := by simpa only [pow_two] using ha.symm
  have htwo : (2 : E) ≠ 0 := by
    rw [← Nat.cast_two, ne_eq, CharP.cast_eq_zero_iff E p 2]
    exact fun hdvd => hp ((Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left
      (Fact.out : p.Prime).ne_one)
  obtain ⟨v, hv⟩ := cycle_of_sq_neg_one htwo ha'
  have hdvd : 2 ∣ n := even_iff_two_dvd.mp heven
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := E) (L := GaloisField p n) (by
      change Module.finrank (ZMod p) (GaloisField p 2) ∣ _
      rw [GaloisField.finrank p (by decide : 2 ≠ 0), GaloisField.finrank p hn]
      exact hdvd)
  exact map_cycle f.toRingHom ⟨4, v, by decide, hv⟩

private theorem degree_seed_tail (E : Type*) [Field E] :
    (X + 1 : E[X]).degree < 4 := by
  have hlow : (X + 1 : E[X]).degree ≤ 1 :=
    (degree_add_le (X : E[X]) 1).trans (by simp)
  exact hlow.trans_lt (by decide)

private theorem degree_seed_polynomial (E : Type*) [Field E] :
    (X ^ 4 + X + 1 : E[X]).degree = 4 := by
  rw [add_assoc, degree_add_eq_left_of_degree_lt, degree_X_pow]
  · rfl
  · rw [degree_X_pow]
    change (X + 1 : E[X]).degree < 4
    exact degree_seed_tail E

/-- Every finite extension field in Hypothesis 6.1 has a nontrivial directed cycle. -/
theorem result : claim := by
  intro K _ _ p n hp hn hcard hfour
  let : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := by omega
  let L := GaloisField p n
  let : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card L = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p n hn0
  apply map_cycle (FiniteField.ringEquivOfCardEq (hcardL.trans hcard.symm)).toRingHom
  by_cases htwo : p = 2
  · subst p
    have hn2 : 2 < n := by
      by_contra! hle
      have heq : n = 2 := by omega
      exact hfour (hcard.trans (by rw [heq]; decide))
    rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn2 with h4 | ⟨d, hd, hdvd, hodd⟩
    · obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
        (F := ZMod 2) (K := GaloisField 2 4) (L := GaloisField 2 n) (by
          rw [GaloisField.finrank 2 (by decide : 4 ≠ 0), GaloisField.finrank 2 hn0]
          exact h4)
      have hseed : HasCycle (GaloisField 2 4) := by
        obtain ⟨t, ht₄, hminpoly⟩ : ∃ t : GaloisField 2 4,
            t ^ 4 = t + 1 ∧ minpoly (ZMod 2) t = X ^ 4 + X + 1 := by
          let E := GaloisField 2 4
          let q : E[X] := X ^ 4 + X + 1
          have hcard : Nat.card E = 16 := GaloisField.card 2 4 (by decide)
          have hsplit : (X ^ 16 - X : E[X]).Splits := by
            rw [← hcard]
            exact Polynomial.splits_X_pow_nat_card_sub_X
          have hdvd : q ∣ (X ^ 16 - X : E[X]) := by
            refine ⟨q ^ 3 + 1, ?_⟩
            have hfrob : q ^ 4 = X ^ 16 + X ^ 4 + 1 := by
              unfold q
              simp only [show (4 : ℕ) = 2 ^ 2 by decide, add_pow_char_pow, one_pow, ← pow_mul]
              norm_num
            calc
              X ^ 16 - X = q ^ 4 + q := by
                rw [hfrob, CharTwo.sub_eq_add]
                unfold q
                linear_combination -(X ^ 4 + 1) * (CharTwo.two_eq_zero (R := E[X]))
              _ = q * (q ^ 3 + 1) := by ring
          have hqsplits := hsplit.of_dvd (FiniteField.X_pow_card_sub_X_ne_zero E (by decide)) hdvd
          have hqdeg : q.degree = 4 := degree_seed_polynomial E
          obtain ⟨t, ht⟩ := hqsplits.exists_eval_eq_zero (by rw [hqdeg]; decide)
          have ht₄ : t ^ 4 = t + 1 := by
            have ht' : t ^ 4 + (t + 1) = 0 := by simpa [q, add_assoc] using ht
            exact CharTwo.add_eq_zero.mp ht'
          refine ⟨t, ht₄, ?_⟩
          have hint := IsIntegral.of_finite (ZMod 2) t
          let d := (minpoly (ZMod 2) t).natDegree
          have hd : d ∣ 4 := by
            have h := minpoly.degree_dvd hint
            change d ∣ Module.finrank (ZMod 2) (GaloisField 2 4) at h
            rwa [GaloisField.finrank 2 (by decide : 4 ≠ 0)] at h
          have hd₄ : d = 4 := by
            by_contra hdegree
            have hd₂ : d ∣ 2 := by
              obtain ⟨k, hk, hdk⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp hd
              change k ≤ 2 at hk
              have hkle : k ≤ 1 := by
                by_contra! h
                have heq : k = 2 := by omega
                exact hdegree (by simpa [heq] using hdk)
              rw [hdk]
              exact pow_dvd_pow 2 hkle
            let S := IntermediateField.adjoin (ZMod 2) ({t} : Set E)
            have hs : Module.finrank (ZMod 2) S = d := IntermediateField.adjoin.finrank hint
            obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
              (F := ZMod 2) (K := S) (L := GaloisField 2 2) (by
                rw [hs, GaloisField.finrank 2 (by decide : 2 ≠ 0)]
                exact hd₂)
            let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
            let tS : S := ⟨t, IntermediateField.mem_adjoin_simple_self _ _⟩
            have hcard₂ : Fintype.card (GaloisField 2 2) = 4 := by
              rw [← Nat.card_eq_fintype_card]
              exact GaloisField.card 2 2 (by decide)
            have htS : tS ^ 4 = tS := by
              apply e.injective
              change e (tS ^ 4) = e tS
              rw [map_pow]
              simpa only [hcard₂] using FiniteField.pow_card (e tS)
            have htfour : t ^ 4 = t := congrArg Subtype.val htS
            exact one_ne_zero (add_left_cancel ((ht₄.symm.trans htfour).trans (add_zero t).symm))
          have hmonic : (X ^ 4 + X + 1 : (ZMod 2)[X]).Monic := by
            rw [add_assoc]
            exact monic_X_pow_add (degree_seed_tail (ZMod 2))
          have hroot : aeval t (X ^ 4 + X + 1 : (ZMod 2)[X]) = 0 := by
            simp only [map_add, map_pow, aeval_X, map_one, ht₄]
            rw [add_assoc (t + 1)]
            exact CharTwo.add_self_eq_zero (t + 1)
          symm
          apply minpoly.unique_of_degree_le_degree_minpoly _ _ hmonic hroot
          rw [degree_seed_polynomial, degree_eq_natDegree (minpoly.ne_zero hint)]
          change (4 : WithBot ℕ) ≤ (d : WithBot ℕ)
          rw [hd₄]
          exact le_rfl
        -- Coefficients in increasing powers of the quartic root.
        let seedFirst : Fin 8 → Fin 4 → ZMod 2 :=
          ![![0, 1, 1, 1], ![1, 0, 1, 0], ![1, 0, 1, 1], ![1, 1, 0, 0],
            ![1, 0, 0, 1], ![0, 0, 1, 0], ![1, 1, 0, 1], ![0, 1, 0, 0]]

        let seedSecond : Fin 8 → Fin 4 → ZMod 2 :=
          ![![1, 1, 0, 1], ![0, 0, 0, 1], ![0, 1, 1, 1], ![0, 1, 0, 1],
            ![1, 0, 1, 1], ![1, 1, 1, 1], ![1, 0, 0, 1], ![0, 0, 1, 1]]
        have hdegree : (minpoly (ZMod 2) t).natDegree = 4 := by
          rw [hminpoly]
          exact (degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 4)).mp
            (degree_seed_polynomial (ZMod 2))
        let value (coeffs : Fin 4 → ZMod 2) : GaloisField 2 4 :=
          ∑ i : Fin 4, coeffs i • t ^ i.val
        have hvalue : Injective value := by
          have hlin := _root_.linearIndependent_pow (K := ZMod 2) t
          rw [hdegree] at hlin
          intro f g hfg
          exact funext (Fintype.linearIndependent_iffₛ.mp hlin f g hfg)
        let v : Fin 8 → GaloisField 2 4 × GaloisField 2 4 :=
          fun i => (value (seedFirst i), value (seedSecond i))
        refine ⟨8, v, by decide, by decide, ?_, ?_⟩
        · have hcodes : Injective seedFirst := of_decide_eq_true rfl
          intro i j hij
          exact hcodes (hvalue (congrArg Prod.fst hij))
        · have htwo : (2 : GaloisField 2 4) = 0 := CharTwo.two_eq_zero
          -- The edge differences are multiples of t⁴ − t − 1 and 2 over the integers.
          have hedge (i : Fin 8) : phi (v i) = v (i + 1) := by
            fin_cases i <;> apply Prod.ext <;>
              simp [v, phi, value, seedFirst, seedSecond, Fin.sum_univ_four]
            case «0».fst => linear_combination (t + t ^ 3) * htwo
            case «0».snd =>
              linear_combination (2 + t + t ^ 2) * ht₄ +
                (1 + 2 * t + 2 * t ^ 2 + t ^ 3) * htwo
            case «1».snd => linear_combination t * ht₄
            case «2».fst => linear_combination (t ^ 2 + t ^ 3) * htwo
            case «2».snd =>
              linear_combination (2 + 2 * t + t ^ 2) * ht₄ +
                (1 + 2 * t + 2 * t ^ 2 + t ^ 3) * htwo
            case «3».fst => linear_combination t * htwo
            case «3».snd => linear_combination ht₄ + t * htwo
            case «4».fst => linear_combination (1 + t ^ 3) * htwo
            case «4».snd => linear_combination (t + t ^ 2) * ht₄ + (t ^ 2 + t ^ 3) * htwo
            case «5».fst => linear_combination t ^ 2 * htwo
            case «5».snd => linear_combination (1 + t) * ht₄ + (t + t ^ 2) * htwo
            case «6».fst => linear_combination (1 + t ^ 3) * htwo
            case «6».snd => linear_combination (1 + t ^ 2) * ht₄ + (1 + t + t ^ 3) * htwo
            case «7».fst => ring
            case «7».snd => linear_combination ht₄
          intro i j hij
          exact (hedge i).trans (congrArg v (Fin.ext (by
            change (i.val + 1) % 8 = j.val
            exact hij.symm)))
      exact map_cycle f.toRingHom hseed
    · obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
        (F := ZMod 2) (K := GaloisField 2 d) (L := GaloisField 2 n) (by
          rw [GaloisField.finrank 2 hd.ne_zero, GaloisField.finrank 2 hn0]
          exact hdvd)
      exact map_cycle f.toRingHom (cycle_of_odd_degree hd.one_lt hodd)
  · rcases Nat.even_or_odd n with heven | hodd
    · exact cycle_of_odd_char_even_degree htwo hn0 heven
    · exact cycle_of_odd_degree hn hodd

end Trureturing.StructureGraphCycles
