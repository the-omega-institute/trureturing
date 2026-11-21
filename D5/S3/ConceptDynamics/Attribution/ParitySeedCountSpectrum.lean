/- GID: D5/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParitySeedCountSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact fixed-count restrictions for coloured parity seeds. -/

import D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card

/-! The attainable fixed counts inside the coordinatewise parity boundary. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum

open Finset CoordinateFlagCoupling ParitySeedBudget ParitySeedOptimization
open D5.S3.Combinatorics.Graph.Hypercube.ParityProfileMatching
open D5.S3.QuantumBounds.MerminMeasurementDependence (bit_cases)

open MulAction

private theorem orbit_two_or_four_dvd {G S : Type*} [Group G] [Fintype G] [Fintype S]
    [MulAction G S] {d : ℕ} (order : Fintype.card G = 2 ^ d) (s : S)
    (moves : ∃ g : G, g • s ≠ s) :
    let T := (orbit G s : Set S)
    letI : Fintype T := Fintype.ofFinite T
    Fintype.card T = 2 ∨ 4 ∣ Fintype.card T := by
  classical
  dsimp only
  letI : Fintype (orbit G s) := Fintype.ofFinite _
  letI : Fintype (stabilizer G s) := Fintype.ofFinite _
  have card_dvd : Fintype.card (orbit G s) ∣ 2 ^ d :=
    ⟨Fintype.card (stabilizer G s), order.symm.trans
      (card_orbit_mul_card_stabilizer_eq_card_group G s).symm⟩
  obtain ⟨r, _, orbit_size⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp card_dvd
  have two_le : 2 ≤ Fintype.card (orbit G s) := by
    obtain ⟨g, change⟩ := moves
    by_contra! small
    have small' : Fintype.card (orbit G s) ≤ 1 := Nat.le_of_lt_succ small
    have equal := (Fintype.card_le_one_iff.mp small')
      (⟨g • s, mem_orbit_iff.mpr ⟨g, rfl⟩⟩ : orbit G s) ⟨s, mem_orbit_self s⟩
    exact change (congrArg Subtype.val equal)
  cases r with
  | zero =>
    exact False.elim (Nat.not_succ_le_self 1 (by simpa only [orbit_size, pow_zero] using two_le))
  | succ r =>
    cases r with
    | zero => exact Or.inl orbit_size
    | succ r =>
      right
      rw [orbit_size, pow_succ, pow_succ]
      refine ⟨2 ^ r, ?_⟩
      exact (Nat.mul_assoc (2 ^ r) 2 2).trans (Nat.mul_comm (2 ^ r) 4)

private theorem fixes_of_fixes_image_of_two_point_orbit
    {G S T : Type*} [Group G] [Finite S] [MulAction G S] [MulAction G T]
    (f : S → T) (equiv : ∀ (g : G) s, f (g • s) = g • f s)
    (s : S) (orbit_size : (orbit G s).ncard = 2)
    (image_moves : ∃ h : G, h • f s ≠ f s)
    (g : G) (fixed : g • f s = f s) : g • s = s := by
  obtain ⟨h, moves⟩ := image_moves
  have hs : h • s ≠ s := by
    intro identity
    exact moves ((equiv h s).symm.trans (congrArg f identity))
  have contained : ({h • s, s} : Set S) ⊆ orbit G s := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact mem_orbit_iff.mpr ⟨h, rfl⟩
    · exact mem_orbit_self _
  have pair_eq : ({h • s, s} : Set S) = orbit G s := by
    apply Set.eq_of_subset_of_ncard_le contained
    rw [orbit_size, Set.ncard_pair hs]
  have hg : g • s ∈ ({h • s, s} : Set S) := by
    rw [pair_eq]
    exact mem_orbit_iff.mpr ⟨g, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  refine hg.resolve_left fun eq => moves ?_
  calc
    h • f s = f (h • s) := (equiv h s).symm
    _ = f (g • s) := congrArg f eq.symm
    _ = g • f s := equiv g s
    _ = f s := fixed

private theorem global_divisibility_from_orbits {G S : Type*}
    [Group G] [Fintype S] [MulAction G S] (m : ℕ)
    (h : ∀ s : S, m ∣ (orbit G s).ncard) : m ∣ Fintype.card S := by
  classical
  let Ω := Quotient (orbitRel G S)
  let _ : Fintype Ω := Fintype.ofFinite Ω
  let _ (o : Ω) : Fintype (orbit G o.out) := Fintype.ofFinite _
  rw [Fintype.card_congr (selfEquivSigmaOrbits G S), Fintype.card_sigma]
  apply Finset.dvd_sum
  intro o _
  simpa only [Set.fintypeCard_eq_ncard] using h o.out

private theorem four_dvd_of_fixed_images_but_moved_sources {G S T I : Type*}
    [Group G] [Fintype G] [Fintype S] [MulAction G S] [MulAction G T]
    {d : ℕ} (order : Fintype.card G = 2 ^ d) (gen : I → G)
    (f : S → T) (equiv : ∀ (g : G) s, f (g • s) = g • f s)
    (image_moves : ∀ s, ∃ g : G, g • f s ≠ f s)
    (image_fixes : ∀ s, ∃ i, gen i • f s = f s)
    (source_moves : ∀ (s : S) (i : I), gen i • s ≠ s) : 4 ∣ Fintype.card S := by
  apply global_divisibility_from_orbits (G := G)
  intro s
  have moves : ∃ g : G, g • s ≠ s := by
    obtain ⟨g, h⟩ := image_moves s
    exact ⟨g, fun eq => h ((equiv g s).symm.trans (congrArg f eq))⟩
  have alternatives := orbit_two_or_four_dvd order s moves
  have alternatives' : (orbit G s).ncard = 2 ∨ 4 ∣ (orbit G s).ncard := by
    dsimp only at alternatives
    rwa [Set.fintypeCard_eq_ncard] at alternatives
  rcases alternatives' with two | div
  · obtain ⟨i, fixed⟩ := image_fixes s
    exact False.elim (source_moves s i
      (fixes_of_fixes_image_of_two_point_orbit f equiv s two (image_moves s) (gen i) fixed))
  · exact div

open MulAction in
private theorem coordinate_fixed_iff_generator {n : ℕ} {S : Type}
    [MulAction (Acting (Fin (n + 2))) S] (i : Fin (n + 2)) (s : S) :
    (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • s = s) ↔ generator i • s = s := by
  have inclusion : (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • s = s) ↔
      coordinate i ≤ stabilizer (Acting (Fin (n + 2))) s :=
    ⟨fun fix g hg => fix ⟨g, hg⟩, fun sub g => sub g.property⟩
  rw [inclusion, coordinate, Subgroup.zpowers_le, mem_stabilizer_iff]

open MulAction in
private theorem pair_action_moves {n : ℕ} (a : Pair n) :
    ∃ g : Acting (Fin (n + 2)), g • a ≠ a := by
  by_contra! fixed
  have profileOne (t : ZMod 2) (x : slice (n + 2) t)
      (h : ∀ g : Acting (Fin (n + 2)), g • x = x) :
      bitProfile x.val.profile = 1 := by
    funext i
    have ones := (fixed_pair_iff x.val x.val i).1 (by
      intro g _
      exact ⟨congrArg Subtype.val (h g), congrArg Subtype.val (h g)⟩)
    have bit : x.val.profile i = true := by simpa using ones
    simp [bitProfile, bit]
  have left := profileOne _ a.1 (fun g => congrArg Prod.fst (fixed g))
  have right := profileOne _ a.2 (fun g => congrArg Prod.snd (fixed g))
  have equal := congrArg parity (left.trans right.symm)
  rw [a.1.property, a.2.property] at equal
  exact zero_ne_one equal

section
attribute [local instance 10000] Classical.propDecidable

/-- Uniform coloured marginals make each actual fixed count a multiple of four. -/
theorem coordinate_fixed_count_four_dvd {n : ℕ} {S : Type} [Fintype S]
    [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n)
    (equiv : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s)
    (c : ℕ)
    (rows : ∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c)
    (cols : ∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = c)
    (i : Fin (n + 2)) : 4 ∣ fixedSeedCount (n := n) S i := by
  classical
  let E (a : Pair n) := ∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a
  have eligible : 4 ∣ (∑ s : S, if E (f s) then (1 : ℕ) else 0) := by
    have counted : (∑ s : S, if E (f s) then (1 : ℕ) else 0) =
        ∑ a : Pair n, if (∀ h : coordinate i, (h : Acting (Fin (n + 2))) • a = a)
          then seedWeight (seedPushforward f) a else 0 := by
      convert seed_indicator_sum f E using 1 <;>
        apply sum_congr rfl <;> intro a _ <;> unfold E <;> split <;> simp_all
    rw [counted, matrix_fixed_total]
    have cells := (seeds_to_pushforward f rfl equiv c rows cols).four_dvd.2
    apply Finset.dvd_sum
    intro p _
    apply Finset.dvd_sum
    intro q _
    split
    · exact cells p q
    · exact dvd_zero _
  let M (s : S) := E (f s) ∧ generator i • s ≠ s
  have fixed_of_seed (s : S) (hs : generator i • s = s) : E (f s) := by
    exact (coordinate_fixed_iff_generator i (f s)).2 ((equiv (generator i) s).symm.trans
      (congrArg f hs))
  let moved : SubMulAction (Acting (Fin (n + 2))) S :=
    { carrier := {s | M s}
      smul_mem' := by
        intro g s hs
        change M s at hs
        change M (g • s)
        refine ⟨?_, ?_⟩
        · intro h
          rw [equiv, smul_comm (h : Acting (Fin (n + 2))) g, hs.1 h]
        · intro eq
          apply hs.2
          apply (MulAction.toPerm g).injective
          change g • (generator i • s) = g • s
          rw [smul_comm g (generator i)]
          exact eq }
  letI : Fintype moved := Fintype.ofFinite moved
  have order : Fintype.card (Acting (Fin (n + 2))) = 2 ^ (n + 2) := by
    rw [Fintype.card_congr Multiplicative.toAdd, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have divMoved : 4 ∣ Fintype.card moved := by
    apply four_dvd_of_fixed_images_but_moved_sources order
      (fun _ : Unit => generator i) (fun s : moved => f s.val)
    · intro g s
      exact equiv g s.val
    · exact fun s => pair_action_moves (f s.val)
    · intro s
      exact ⟨(), s.property.1 ⟨generator i, Subgroup.mem_zpowers _⟩⟩
    · intro s _ h
      exact s.property.2 (congrArg Subtype.val h)
  have movedCount : Fintype.card moved =
      ∑ s : S, if M s then (1 : ℕ) else 0 := by
    let sameFibre : moved ≃ {s : S // M s} := Equiv.refl _
    calc
      Fintype.card moved = Fintype.card {s : S // M s} := Fintype.card_congr sameFibre
      _ = _ := by
        rw [Fintype.card_subtype]
        simpa only [Nat.cast_id] using
          (Finset.sum_boole (R := ℕ) M (univ : Finset S)).symm
  have split : (∑ s : S, if E (f s) then (1 : ℕ) else 0) =
      fixedSeedCount (n := n) S i + Fintype.card moved := by
    rw [movedCount, fixedSeedCount, ← sum_add_distrib]
    apply sum_congr rfl
    intro s _
    by_cases hs : generator i • s = s
    · have fix := (coordinate_fixed_iff_generator i s).2 hs
      rw [ite_eq_left fix]
      simp [M, fixed_of_seed s hs, hs]
    · have moves := mt (coordinate_fixed_iff_generator i s).1 hs
      rw [ite_eq_right moves]
      simp [M, hs]
  rw [split] at eligible
  exact (Nat.dvd_add_iff_left divMoved).2 eligible

end

section

private theorem parity_ones_even {n : ℕ} (even : Even (n + 2)) :
    parity (1 : Profile (n + 2)) = 0 := by
  unfold parity
  simp only [Pi.one_apply, sum_const, card_univ, Fintype.card_fin, nsmul_one]
  obtain ⟨j, hj⟩ := even
  rw [show n + 2 = j + j from hj]
  push_cast
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem bits_on_right {n : ℕ} (even : Even (n + 2)) (y : slice (n + 2) 1) :
    (∃ i, y.val.profile i = true) ∧ (∃ i, y.val.profile i = false) := by
  have property : parity (bitProfile y.val.profile) = 1 := y.property
  constructor
  · by_contra! noTrue
    have zero : bitProfile y.val.profile = 0 := by
      funext i
      have eq := noTrue i
      cases h : y.val.profile i <;> simp_all [bitProfile]
    rw [zero, parity] at property
    simp at property
  · by_contra! noFalse
    have one : bitProfile y.val.profile = 1 := by
      funext i
      have eq := noFalse i
      cases h : y.val.profile i <;> simp_all [bitProfile]
    rw [one, parity_ones_even even] at property
    exact zero_ne_one property

private theorem fixed_one_output {n : ℕ} (even : Even (n + 2)) :
    ∃ x : slice (n + 2) 0, (∀ i, x.val.profile i = true) ∧
      ∀ g : Acting (Fin (n + 2)), g • x = x := by
  let x := sliceEquiv (n + 2) 0 (⟨1, parity_ones_even even⟩, 0)
  have ones (i : Fin (n + 2)) : x.val.profile i = true := by
    simp [x, sliceEquiv, booleanProfile]
  refine ⟨x, ones, fun g => Subtype.ext ?_⟩
  change Output.mk x.val.profile (shift x.val.profile g.toAdd + x.val.colour) = x.val
  have noShift : shift x.val.profile g.toAdd = 0 := by
    unfold shift
    exact sum_eq_zero fun i _ => by simp [ones i]
  rw [noShift, zero_add]

attribute [local instance 10000] Classical.propDecidable

private theorem uniform_coloured_fibre_four_dvd_of_no_coordinate_fixed {n : ℕ}
    (even : Even (n + 2)) (S : Type) [Fintype S] [MulAction (Acting (Fin (n + 2))) S]
    (f : S → Pair n) (equiv : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s)
    (source_moves : ∀ (s : S) (i : Fin (n + 2)), generator i • s ≠ s)
    (c : ℕ) (rows : ∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c) :
    4 ∣ c := by
  classical
  obtain ⟨x, leftOnes, leftFixed⟩ := fixed_one_output even
  let fibre : SubMulAction (Acting (Fin (n + 2))) S :=
    { carrier := {s | (f s).1 = x}
      smul_mem' := by
        intro g s hs
        change (f (g • s)).1 = x
        rw [equiv]
        change g • (f s).1 = x
        change (f s).1 = x at hs
        rw [hs, leftFixed] }
  let _ : Fintype fibre := Fintype.ofFinite fibre
  let readout : fibre → Pair n := fun s => f s.val
  have action_order : Fintype.card (Acting (Fin (n + 2))) = 2 ^ (n + 2) := by
    rw [Fintype.card_congr Multiplicative.toAdd, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have eq_card : Fintype.card fibre = c := by
    let sameFibre : fibre ≃ {s : S // (f s).1 = x} := Equiv.refl _
    rw [Fintype.card_congr sameFibre, Fintype.card_subtype]
    have filters := Finset.sum_boole (R := ℕ)
      (fun s : S => (f s).1 = x) (univ : Finset S)
    refine (Nat.cast_id _).symm.trans (filters.symm.trans ?_)
    convert rows x using 1
    apply sum_congr rfl
    intro s _
    by_cases hs : (f s).1 = x <;> simp [hs]
  rw [← eq_card]
  apply four_dvd_of_fixed_images_but_moved_sources action_order generator readout
  · intro g s
    exact equiv g s.val
  · intro s
    obtain ⟨_, j, rightZero⟩ := bits_on_right even (readout s).2
    by_contra! all
    have both := (fixed_pair_iff (readout s).1.val (readout s).2.val j).1 (by
      intro g _
      exact ⟨congrArg (fun a : Pair n => a.1.val) (all g),
        congrArg (fun a : Pair n => a.2.val) (all g)⟩)
    simp [rightZero] at both
  · intro s
    obtain ⟨⟨i, rightOne⟩, _⟩ := bits_on_right even (readout s).2
    have leftOne : (readout s).1.val.profile i = true := by
      change (f s.val).1.val.profile i = true
      rw [show (f s.val).1 = x from s.property]
      exact leftOnes i
    have both := (fixed_pair_iff (readout s).1.val (readout s).2.val i).2 (by
      simp [leftOne, rightOne])
    obtain ⟨left, right⟩ := both (generator i) (Subgroup.mem_zpowers (generator i))
    exact ⟨i, Prod.ext (Subtype.ext left) (Subtype.ext right)⟩
  · intro s i h
    exact source_moves s.val i (congrArg Subtype.val h)

private theorem left_colour_marginal {n k : ℕ} {S : Type} [Fintype S]
    (f : S → Pair n) (card : Fintype.card S = 2 ^ (n + 3) * k)
    (c : ℕ) (rows : ∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c) :
    c = 2 * k := by
  have fibre_sum :
      (∑ x : slice (n + 2) 0, ∑ s : S, if (f s).1 = x then 1 else (0 : ℕ)) = Fintype.card S := by
    rw [sum_comm]
    simp
  have card_slice : Fintype.card (slice (n + 2) 0) = 2 ^ (n + 2) := by
    rw [Fintype.card_congr (sliceEquiv (n + 2) 0).symm, Fintype.card_prod,
      ← Nat.card_eq_fintype_card, parityCard, ZMod.card]
    rw [pow_succ (2 : ℕ) (n + 1), pow_succ (2 : ℕ) n]
  simp only [rows, sum_const, card_univ, nsmul_eq_mul, card_slice, card, Nat.cast_id] at fibre_sum
  rw [show n + 3 = (n + 2) + 1 by rfl, pow_succ (2 : ℕ) (n + 2), Nat.mul_assoc] at fibre_sum
  exact Nat.eq_of_mul_eq_mul_left (by positivity) fibre_sum

set_option maxHeartbeats 600000 in
private theorem zero_coordinate_counts_force_odd_dimension_or_even_multiplier {n k : ℕ}
    (S : Type) [Fintype S] [MulAction (Acting (Fin (n + 2))) S] (f : S → Pair n)
    (card : Fintype.card S = 2 ^ (n + 3) * k)
    (equiv : ∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s)
    (c : ℕ) (rows : ∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c)
    (noneFixed : ∀ i, fixedSeedCount (n := n) S i = 0) :
    Odd (n + 2) ∨ Even k := by
  rcases Nat.even_or_odd (n + 2) with even | odd
  · refine Or.inr ?_
    have moves (s : S) (i : Fin (n + 2)) : generator i • s ≠ s := by
      intro fixed
      have e := (coordinate_fixed_iff_generator i s).2 fixed
      have hz := noneFixed i
      unfold fixedSeedCount at hz
      have atSeed := (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Nat.zero_le _)).mp hz s (mem_univ s)
      rw [ite_eq_left e] at atSeed
      exact Nat.one_ne_zero atSeed
    have div := uniform_coloured_fibre_four_dvd_of_no_coordinate_fixed even S f equiv moves c rows
    rw [left_colour_marginal f card c rows] at div
    obtain ⟨j, hj⟩ := div
    refine ⟨j, Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 1) (hj.trans ?_)⟩
    rw [Nat.mul_add, ← Nat.add_mul]

  · exact Or.inl odd

end

section

@[instance_reducible] private def flipOnEachCoordinate (d : ℕ) : MulAction (Acting (Fin d)) (ZMod 2) where
  smul g c := shift (fun _ => false) g.toAdd + c
  one_smul c := by
    change shift (fun _ => false) (0 : Fin d → ZMod 2) + c = c
    simp [shift]
  mul_smul g h c := by
    change shift (fun _ => false) (g.toAdd + h.toAdd) + c =
      shift (fun _ => false) g.toAdd + (shift (fun _ => false) h.toAdd + c)
    rw [shift_add, add_assoc]

private theorem generator_shifts {d : ℕ} (i : Fin d) :
    shift (fun _ => false) (generator i).toAdd = 1 := by
  simp [generator, shift]

section
attribute [local instance 10000] Classical.propDecidable

private theorem even_multiplier_all_zero (n k : ℕ) :
    ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Acting (Fin (n + 2))) S) (f : S → Pair n),
      Fintype.card S = 2 ^ (n + 3) * (2 * k) ∧
      (∀ (g : Acting (Fin (n + 2))) s, f (g • s) = g • f s) ∧
      (∃ c : ℕ,
        (∀ x : slice (n + 2) 0, (∑ s, if (f s).1 = x then 1 else (0 : ℕ)) = c) ∧
        (∀ y : slice (n + 2) 1, (∑ s, if (f s).2 = y then 1 else (0 : ℕ)) = c)) ∧
      ∀ i, fixedSeedCount (n := n) S i = 0 := by
  classical
  obtain ⟨S, _, _, f, card, equiv, c, rows, cols⟩ :=
    (exact_seed_budget n (2 ^ (n + 3) * k)).2 ⟨k, rfl⟩
  letI := flipOnEachCoordinate (n + 2)
  let readout : S × ZMod 2 → Pair n := fun a => f a.1
  have double (P : S → Prop) :
      (∑ a : S × ZMod 2, if P a.1 then (1 : ℕ) else 0) =
        2 * ∑ s : S, if P s then (1 : ℕ) else 0 := by
    rw [Fintype.sum_prod_type]
    rw [mul_sum]
    apply sum_congr rfl
    intro s _
    by_cases h : P s <;> simp [h, ZMod.card]
  refine ⟨S × ZMod 2, inferInstance, inferInstance, readout, ?_, ?_, ⟨2 * c, ?_, ?_⟩, ?_⟩
  · rw [Fintype.card_prod, card, ZMod.card]
    ac_rfl
  · intro g a
    exact equiv g a.1
  · intro x
    rw [double (fun s => (f s).1 = x), rows x]
  · intro y
    rw [double (fun s => (f s).2 = y), cols y]
  · intro i
    unfold fixedSeedCount
    apply sum_eq_zero
    intro a _
    apply if_neg
    intro fixed
    have mem : generator i ∈ coordinate i := Subgroup.mem_zpowers (generator i)
    have h := congrArg Prod.snd (fixed ⟨generator i, mem⟩)
    change shift (fun _ => false) (generator i).toAdd + a.2 = a.2 at h
    rw [generator_shifts] at h
    exact one_ne_zero (add_right_cancel (h.trans (zero_add _).symm))

end

end

section

namespace TwoCoordinateMixedSeedWitness

private abbrev G := Acting (Fin 2)
private abbrev Bit := ZMod 2
private abbrev Seeds := Bit × Bit × Bit × Bit

private def motion (g : G) (s : Seeds) : Seeds :=
  let (a, b, c, d) := s
  if a = 0 then
    (a, b, g.toAdd 0 + g.toAdd 1 + c, g.toAdd 0 + d)
  else
    (a, (if c = 0 then 0 else g.toAdd 0) + b, c, g.toAdd 1 + d)

private instance : MulAction G Seeds where
  smul := motion
  one_smul := by
    rintro ⟨a, b, c, d⟩
    change motion 1 (a,b,c,d) = (a,b,c,d)
    by_cases ha : a = 0 <;> simp [motion, ha]
  mul_smul := by
    rintro g h ⟨a,b,c,d⟩
    change motion (g * h) (a,b,c,d) = motion g (motion h (a,b,c,d))
    by_cases ha : a = 0
    · simp only [motion, ha, ite_true, Prod.mk.injEq, true_and]
      change
        (g.toAdd 0 + h.toAdd 0 + (g.toAdd 1 + h.toAdd 1) + c =
          g.toAdd 0 + g.toAdd 1 + (h.toAdd 0 + h.toAdd 1 + c)) ∧
        (g.toAdd 0 + h.toAdd 0 + d = g.toAdd 0 + (h.toAdd 0 + d))
      exact ⟨by ac_rfl, by ac_rfl⟩
    · by_cases hc : c = 0
      · simp only [motion, ha, hc, ite_false, ite_true, zero_add, Prod.mk.injEq, true_and]
        change g.toAdd 1 + h.toAdd 1 + d = g.toAdd 1 + (h.toAdd 1 + d)
        exact add_assoc _ _ _
      · simp only [motion, ha, hc, ite_false, Prod.mk.injEq, true_and]
        exact ⟨add_assoc _ _ _, add_assoc _ _ _⟩

private def leftProfile (a : Bit) : Profile 2 := fun _ => a
private def rightProfile (a : Bit) : Profile 2 := ![a, 1 - a]

private theorem zmod2_double (a : Bit) : a + a = 0 := by
  have double : (2 : Bit) = 0 := by decide
  rw [← two_mul, double, zero_mul]

private def leftParity (a : Bit) : ParityClass 2 0 :=
  ⟨leftProfile a, by simpa only [parity, leftProfile, Fin.sum_univ_two] using zmod2_double a⟩

private def rightParity (a : Bit) : ParityClass 2 1 :=
  ⟨rightProfile a, by simp [parity, rightProfile, Fin.sum_univ_two]⟩

private def f (s : Seeds) : Pair 0 :=
  (sliceEquiv 2 0 (leftParity s.1, s.2.2.1), sliceEquiv 2 1 (rightParity s.1, s.2.2.2))

private theorem leftParity_bijective : Function.Bijective leftParity := by
  have inj : Function.Injective leftParity := by
    intro a b eq
    exact congrArg (fun x : ParityClass 2 0 => x.val 0) eq
  refine ⟨inj, (Finite.injective_iff_surjective_of_equiv ?_).1 inj⟩
  apply Fintype.equivOfCardEq
  rw [ZMod.card, ← Nat.card_eq_fintype_card, parityCard]
  decide

private theorem rightParity_bijective : Function.Bijective rightParity := by
  have inj : Function.Injective rightParity := by
    intro a b eq
    exact congrArg (fun x : ParityClass 2 1 => x.val 0) eq
  refine ⟨inj, (Finite.injective_iff_surjective_of_equiv ?_).1 inj⟩
  apply Fintype.equivOfCardEq
  rw [ZMod.card, ← Nat.card_eq_fintype_card, parityCard]
  decide

private theorem equivariant (g : G) (s : Seeds) : f (g • s) = g • f s := by
  rcases s with ⟨a,b,c,d⟩
  change f (motion g (a,b,c,d)) = g • f (a,b,c,d)
  apply Prod.ext
  · apply Subtype.ext
    change Output.mk (booleanProfile (leftProfile (motion g (a,b,c,d)).1))
        (motion g (a,b,c,d)).2.2.1 =
      Output.mk (booleanProfile (leftProfile a))
        (shift (booleanProfile (leftProfile a)) g.toAdd + c)
    rcases bit_cases a with rfl | rfl <;>
      simp [motion, leftProfile, booleanProfile, shift, Fin.sum_univ_two]
  · apply Subtype.ext
    change Output.mk (booleanProfile (rightProfile (motion g (a,b,c,d)).1))
        (motion g (a,b,c,d)).2.2.2 =
      Output.mk (booleanProfile (rightProfile a))
        (shift (booleanProfile (rightProfile a)) g.toAdd + d)
    rcases bit_cases a with rfl | rfl <;>
      simp [motion, rightProfile, booleanProfile, shift, Fin.sum_univ_two]

attribute [local instance 10000] Classical.propDecidable

private theorem readout_count (target x : Bit) :
    (∑ s : Seeds, if s.1 = target ∧ s.2.2.1 = x then (1 : ℕ) else 0) = 4 := by
  simp_rw [Fintype.sum_prod_type]
  have balance (a : Bit) :
      (∑ b : Bit, ∑ c : Bit, ∑ _ : Bit,
        if a = target ∧ c = x then (1 : ℕ) else 0) =
          if a = target then 4 else 0 := by
    by_cases h : a = target <;> simp [h, ZMod.card]
  simp only [balance]
  simp

private theorem left_marginal (x : slice 2 0) :
    (∑ s : Seeds, if (f s).1 = x then (1 : ℕ) else 0) = 4 := by
  obtain ⟨⟨p,c⟩,rfl⟩ := (sliceEquiv 2 0).surjective x
  obtain ⟨a,rfl⟩ := leftParity_bijective.2 p
  simp only [f, (sliceEquiv 2 0).injective.eq_iff, Prod.mk.injEq,
    leftParity_bijective.1.eq_iff]
  exact readout_count a c

private theorem right_marginal (y : slice 2 1) :
    (∑ s : Seeds, if (f s).2 = y then (1 : ℕ) else 0) = 4 := by
  obtain ⟨⟨p,d⟩,rfl⟩ := (sliceEquiv 2 1).surjective y
  obtain ⟨a,rfl⟩ := rightParity_bijective.2 p
  simp only [f, (sliceEquiv 2 1).injective.eq_iff, Prod.mk.injEq,
    rightParity_bijective.1.eq_iff]
  simp_rw [Fintype.sum_prod_type]
  change (∑ z : Bit, ∑ _ : Bit, ∑ _ : Bit, ∑ v : Bit,
    if z = a ∧ v = d then (1 : ℕ) else 0) = 4
  have balance (z : Bit) :
      (∑ _ : Bit, ∑ _ : Bit, ∑ v : Bit,
        if z = a ∧ v = d then (1 : ℕ) else 0) = if z = a then 4 else 0 := by
    by_cases h : z = a <;> simp [h, ZMod.card]
  simp only [balance]
  simp

private theorem generator_fixed (s : Seeds) (i : Fin 2) :
    generator i • s = s ↔ i = 0 ∧ s.1 = 1 ∧ s.2.2.1 = 0 := by
  rcases s with ⟨a,b,c,d⟩
  rcases bit_cases a with rfl | rfl <;> fin_cases i <;>
    change motion (generator _) (_,_,_,_) = (_,_,_,_) ↔ _ <;>
    simp [motion, generator, Prod.mk.injEq]

section
attribute [local instance 10000] Classical.propDecidable

set_option maxHeartbeats 1000000 in
private theorem mixed_seed_witness : RealizableSeedCounts 0 2 ![4,0] := by
  refine ⟨Seeds, inferInstance, (inferInstance : MulAction G Seeds), f, ?_, equivariant,
    ⟨4,left_marginal,right_marginal⟩, ?_⟩
  · simp [Fintype.card_prod, ZMod.card]
  · intro i
    let : MulAction (Acting (Fin (0 + 2))) Seeds := (inferInstance : MulAction G Seeds)
    have reduced : fixedSeedCount (n := 0) Seeds i =
        ∑ s : Seeds, if i = 0 ∧ s.1 = 1 ∧ s.2.2.1 = 0 then (1 : ℕ) else 0 := by
      unfold fixedSeedCount
      apply sum_congr rfl
      intro s _
      have condition := (coordinate_fixed_iff_generator (n := 0) i s).trans (generator_fixed s i)
      by_cases h : i = 0 ∧ s.1 = 1 ∧ s.2.2.1 = 0
      · rw [ite_eq_left (condition.mpr h), ite_eq_left h]
      · rw [ite_eq_right (mt condition.mp h), ite_eq_right h]
    rw [reduced]
    fin_cases i
    · simp_rw [Fintype.sum_prod_type]
      change (∑ a : Bit, ∑ _ : Bit, ∑ c : Bit, ∑ _ : Bit,
        if (0 : Fin 2) = 0 ∧ a = 1 ∧ c = 0 then (1 : ℕ) else 0) = 4
      have balance (a : Bit) :
          (∑ _ : Bit, ∑ c : Bit, ∑ _ : Bit,
            if (0 : Fin 2) = 0 ∧ a = 1 ∧ c = 0 then (1 : ℕ) else 0) =
            if a = 1 then 4 else 0 := by
        by_cases h : a = 1 <;> simp [h, ZMod.card]
      calc
        _ = ∑ a : Bit, if a = 1 then 4 else 0 := sum_congr rfl fun a _ => balance a
        _ = _ := by simp
    · have ne : (1 : Fin 2) ≠ 0 := by
        intro eq
        have bad := congrArg Fin.val eq
        change 1 = 0 at bad
        exact Nat.one_ne_zero bad
      simp [ne]

end

end TwoCoordinateMixedSeedWitness

end

section

attribute [local instance 10000] Classical.propDecidable

private theorem add_realizable_seed_counts {n k l : ℕ} {x y : Fin (n + 2) → ℕ}
    (left : RealizableSeedCounts n k x) (right : RealizableSeedCounts n l y) :
    RealizableSeedCounts n (k + l) (fun i => x i + y i) := by
  obtain ⟨A, _, _, fa, aCard, aEquiv, ⟨a, aRows, aCols⟩, aFixed⟩ := left
  obtain ⟨B, _, _, fb, bCard, bEquiv, ⟨b, bRows, bCols⟩, bFixed⟩ := right
  refine ⟨A ⊕ B, inferInstance, inferInstance, Sum.elim fa fb, ?_, ?_,
    ⟨a + b, ?_, ?_⟩, ?_⟩
  · rw [Fintype.card_sum, aCard, bCard, Nat.mul_add]
  · intro g s
    cases s
    · exact aEquiv g _
    · exact bEquiv g _
  · intro z
    rw [Fintype.sum_sum_type]
    exact congrArg₂ (· + ·) (aRows z) (bRows z)
  · intro z
    rw [Fintype.sum_sum_type]
    exact congrArg₂ (· + ·) (aCols z) (bCols z)
  · intro i
    change fixedSeedCount (n := n) (A ⊕ B) i = x i + y i
    rw [← aFixed i, ← bFixed i]
    simp only [fixedSeedCount, Fintype.sum_sum_type,
      Sum.smul_inl, Sum.smul_inr, Sum.inl.injEq, Sum.inr.injEq]
    apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intro s _ <;>
      split <;> simp_all

private theorem two_coordinate_boundary (t u : ℕ) :
    RealizableSeedCounts 0 (t + u) ![4 * t, 4 * u] := by
  apply ((maximal_coordinate_fixed_vectors 0 (t + u) ![4 * t, 4 * u]).2 ?_).1
  refine ⟨![t, u], ?_, ?_⟩
  · constructor
    · intro i
      fin_cases i <;> simp
    · rw [Fin.sum_univ_two]
      simp [Nat.add_comm]
  · intro i
    fin_cases i <;> rfl

end

section

namespace ParitySeedCoordinateRelabel

variable {n : ℕ}

private abbrev Index (n : ℕ) := Fin (n + 2)

private def precompose (p : Equiv.Perm (Index n)) : Acting (Index n) →* Acting (Index n) where
  toFun g := Multiplicative.ofAdd (g.toAdd ∘ p)
  map_one' := rfl
  map_mul' _ _ := rfl

private def renameOutput (p : Equiv.Perm (Index n)) (x : Output (Index n)) : Output (Index n) :=
  ⟨x.profile ∘ p, x.colour⟩

private theorem parity_rename (p : Equiv.Perm (Index n)) (x : Output (Index n)) :
    parity (bitProfile (renameOutput p x).profile) = parity (bitProfile x.profile) := by
  exact Equiv.sum_comp p (bitProfile x.profile)

private def renameSlice (p : Equiv.Perm (Index n)) (a : ZMod 2) :
    slice (n + 2) a ≃ slice (n + 2) a where
  toFun x := ⟨renameOutput p x.val, (parity_rename p x.val).trans x.property⟩
  invFun x := ⟨renameOutput p.symm x.val, (parity_rename p.symm x.val).trans x.property⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨bits,c⟩, _⟩
    · change Output.mk ((bits ∘ p) ∘ p.symm) c = Output.mk bits c
      simp [Function.comp_def]
  right_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨bits,c⟩, _⟩
    · change Output.mk ((bits ∘ p.symm) ∘ p) c = Output.mk bits c
      simp [Function.comp_def]

private theorem rename_smul (p : Equiv.Perm (Index n)) (g : Acting (Index n))
    {a : ZMod 2} (x : slice (n + 2) a) :
    renameSlice p a (precompose p.symm g • x) = g • renameSlice p a x := by
  apply Subtype.ext
  change Output.mk (x.val.profile ∘ p)
      (shift x.val.profile (g.toAdd ∘ p.symm) + x.val.colour) =
    Output.mk (x.val.profile ∘ p)
      (shift (x.val.profile ∘ p) g.toAdd + x.val.colour)
  have h : shift (x.val.profile ∘ p) g.toAdd = shift x.val.profile (g.toAdd ∘ p.symm) := by
    change (∑ i, if x.val.profile (p i) then (0 : ZMod 2) else g.toAdd i) = _
    simpa only [shift, Function.comp_apply, p.symm_apply_apply] using
      Equiv.sum_comp p (fun j => if x.val.profile j then (0 : ZMod 2) else g.toAdd (p.symm j))
  rw [h]

private theorem rename_generator (p : Equiv.Perm (Index n)) (i : Index n) :
    precompose p.symm (generator i) = generator (p i) := by
  apply Multiplicative.toAdd.injective
  funext j
  have eq_iff : p.symm j = i ↔ j = p i := p.symm_apply_eq
  simp [precompose, generator, Pi.single_apply, eq_iff]

attribute [local instance 10000] Classical.propDecidable

private theorem realizable_relabel {k : ℕ} (p : Equiv.Perm (Index n))
    {v : Index n → ℕ} (h : RealizableSeedCounts n k v) :
    RealizableSeedCounts n k (v ∘ p) := by
  obtain ⟨S, ftype, act, f, card, equiv, ⟨c, row, col⟩, eq⟩ := h
  let renamedAct : MulAction (Acting (Index n)) S := MulAction.compHom S (precompose p.symm)
  let readout (s : S) : Pair n := (renameSlice p 0 (f s).1, renameSlice p 1 (f s).2)
  refine ⟨S, ftype, renamedAct, readout, card, ?_, ⟨c, ?_, ?_⟩, ?_⟩
  · intro g s
    change readout (act.smul (precompose p.symm g) s) = g • readout s
    unfold readout
    have moved : f (act.smul (precompose p.symm g) s) = precompose p.symm g • f s :=
      equiv (precompose p.symm g) s
    rw [moved]
    exact Prod.ext (rename_smul p g (f s).1) (rename_smul p g (f s).2)
  · intro x
    obtain ⟨z, rfl⟩ := (renameSlice p 0).surjective x
    simpa [readout, (renameSlice p 0).injective.eq_iff] using row z
  · intro y
    obtain ⟨z, rfl⟩ := (renameSlice p 1).surjective y
    simpa [readout, (renameSlice p 1).injective.eq_iff] using col z
  · intro i
    change @fixedSeedCount n S ftype renamedAct i = v (p i)
    rw [← eq (p i)]
    unfold fixedSeedCount
    apply sum_congr rfl
    intro s _
    have condition :
        (∀ g : coordinate i, renamedAct.smul g.val s = s) ↔
        (∀ g : coordinate (p i), act.smul g.val s = s) := by
      have left := @coordinate_fixed_iff_generator n S renamedAct i s
      have right := @coordinate_fixed_iff_generator n S act (p i) s
      have gens : renamedAct.smul (generator i) s = act.smul (generator (p i)) s := by
        change act.smul (precompose p.symm (generator i)) s = _
        rw [rename_generator]
      have mid : (renamedAct.smul (generator i) s = s) ↔
          (act.smul (generator (p i)) s = s) := by rw [gens]
      exact left.trans (mid.trans right.symm)
    split <;> split
    · rfl
    · rename_i left right
      exact False.elim (right (condition.mp left))
    · rename_i left right
      exact False.elim (left (condition.mpr right))
    · rfl

end ParitySeedCoordinateRelabel

end

private def complementEquiv {n : ℕ} (odd : Odd (n + 2)) :
    ParityClass (n + 2) 0 ≃ ParityClass (n + 2) 1 := by
  have ones : parity (1 : Profile (n + 2)) = 1 := by
    unfold parity
    simp only [Pi.one_apply, sum_const, card_univ, Fintype.card_fin, nsmul_one]
    obtain ⟨j, hj⟩ := odd
    rw [show n + 2 = 2 * j + 1 from hj]
    push_cast
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
  have add_one (x : Profile (n + 2)) : parity (x + 1) = parity x + 1 := by
    change (∑ i : Fin (n + 2), (x i + (1 : Profile (n + 2)) i)) = parity x + 1
    rw [sum_add_distrib]
    change parity x + parity 1 = parity x + 1
    rw [ones]
  have complement_twice (x : Profile (n + 2)) : x + 1 + 1 = x := by
    funext i
    change x i + 1 + 1 = x i
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]
  refine
    { toFun := fun p => ⟨p.val + 1, by rw [add_one, p.property, zero_add]⟩
      invFun := fun q => ⟨q.val + 1, by rw [add_one, q.property]; decide⟩
      left_inv := fun p => Subtype.ext (complement_twice p.val)
      right_inv := fun q => Subtype.ext (complement_twice q.val) }

private def complementW {n : ℕ} (odd : Odd (n + 2)) (k : ℕ)
    (p : ParityClass (n + 2) 0) (q : ParityClass (n + 2) 1) : ℕ :=
  if complementEquiv odd p = q then k else 0

private theorem complement_margins {n : ℕ} (odd : Odd (n + 2)) (k : ℕ) :
    (∀ p, ∑ q, complementW odd k p q = k) ∧
    (∀ q, ∑ p, complementW odd k p q = k) := by
  constructor
  · intro p
    simp [complementW]
  · intro q
    rw [← Equiv.sum_comp (complementEquiv odd).symm]
    simp [complementW]

private theorem complement_common_one_zero {n : ℕ} (odd : Odd (n + 2)) (k : ℕ)
    (i : Fin (n + 2)) :
    commonOneCount (complementW odd k) i = 0 := by
  unfold commonOneCount
  apply sum_eq_zero
  intro p _
  apply sum_eq_zero
  intro q _
  by_cases edge : complementEquiv odd p = q
  · subst q
    by_cases hp : p.val i = 1
    · have hzero : (complementEquiv odd p).val i = 0 := by
        change p.val i + 1 = 0
        rw [hp]
        decide
      simp [hzero]
    · simp [hp]
  · simp [complementW, edge]

private theorem odd_dimension_all_zero (n k : ℕ) (odd : Odd (n + 2)) :
    RealizableSeedCounts n k (fun _ => 0) := by
  obtain ⟨rows, cols⟩ := complement_margins odd k
  have counts := realize_scaled_profile_counts (complementW odd k) rows cols
  simpa [complement_common_one_zero odd k] using counts

/-- The zero vector is attained in odd dimension or at even multiplicity. -/
theorem zero_coordinate_counts_iff (n k : ℕ) :
    RealizableSeedCounts n k (fun _ => 0) ↔ Odd (n + 2) ∨ Even k := by
  constructor
  · rintro ⟨S, _, _, f, card, equiv, ⟨c, rows, _⟩, fixed⟩
    exact zero_coordinate_counts_force_odd_dimension_or_even_multiplier S f card equiv c rows fixed
  · rintro (odd | ⟨j, hj⟩)
    · exact odd_dimension_all_zero n k odd
    · rw [hj, ← two_mul]
      exact even_multiplier_all_zero n j

private theorem rescale_even_zero (j : ℕ) : RealizableSeedCounts 0 (j + j) (fun _ => 0) := by
  have h : RealizableSeedCounts 0 (2 * j) (fun _ => 0) := even_multiplier_all_zero 0 j
  simpa [two_mul] using h

private theorem mixed_reversed : RealizableSeedCounts 0 2 ![0,4] := by
  let p : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have h := ParitySeedCoordinateRelabel.realizable_relabel (n := 0) p
    TwoCoordinateMixedSeedWitness.mixed_seed_witness
  have eq : (![4,0] : Fin 2 → ℕ) ∘ p = ![0,4] := by
    funext i
    fin_cases i <;> simp [p]
  rwa [eq] at h

private theorem two_coordinate_attainment (k t u : ℕ)
    (fits : t + u ≤ k) (allowed : Even k ∨ 0 < t + u) :
    RealizableSeedCounts 0 k ![4 * t, 4 * u] := by
  rcases Nat.even_or_odd (k - (t + u)) with ⟨j, hj⟩ | ⟨j, hj⟩
  · have h := add_realizable_seed_counts (two_coordinate_boundary t u) (rescale_even_zero j)
    have hBudget : t + u + (j + j) = k := by omega
    rw [hBudget] at h
    simpa using h
  · have positive : 0 < t + u := by
      rcases allowed with ⟨m, hm⟩ | pos
      · omega
      · exact pos
    by_cases ht : 0 < t
    · have h := add_realizable_seed_counts
        (add_realizable_seed_counts (two_coordinate_boundary (t - 1) u)
          TwoCoordinateMixedSeedWitness.mixed_seed_witness) (rescale_even_zero j)
      have hBudget : (t - 1 + u + 2) + (j + j) = k := by omega
      rw [hBudget] at h
      convert h using 1
      funext i
      fin_cases i
      · simp <;> omega
      · simp <;> omega
    · have h := add_realizable_seed_counts
        (add_realizable_seed_counts (two_coordinate_boundary t (u - 1)) mixed_reversed)
          (rescale_even_zero j)
      have hBudget : (t + (u - 1) + 2) + (j + j) = k := by omega
      rw [hBudget] at h
      convert h using 1
      funext i
      fin_cases i
      · simp <;> omega
      · simp <;> omega

/-- Exact realizability of the coordinate fixed-count vector in dimension two. -/
theorem exact_two_coordinate_counts (k : ℕ) (z : Fin 2 → ℕ) :
    RealizableSeedCounts 0 k z ↔
      ∃ t u : ℕ, z = ![4 * t, 4 * u] ∧ t + u ≤ k ∧ (Even k ∨ 0 < t + u) := by
  constructor
  · intro h
    obtain ⟨v, ⟨caps, sum⟩, dom⟩ := seed_vector_dominated h
    obtain ⟨S, _, _, f, card, equiv, ⟨c, rows, cols⟩, fixed⟩ := h
    obtain ⟨t, tEq⟩ := coordinate_fixed_count_four_dvd f equiv c rows cols 0
    obtain ⟨u, uEq⟩ := coordinate_fixed_count_four_dvd f equiv c rows cols 1
    have countVector : z = ![4 * t, 4 * u] := by
      funext i
      fin_cases i
      · exact (fixed 0).symm.trans tEq
      · exact (fixed 1).symm.trans uEq
    have c0 := caps 0
    have c1 := caps 1
    have d0 := dom 0
    have d1 := dom 1
    rw [Fin.sum_univ_two] at sum
    have capSum : v 0 + v 1 = k := by simp at sum c0 c1; omega
    have bound : t + u ≤ k := by
      rw [countVector] at d0 d1
      simp at d0 d1
      omega
    refine ⟨t,u,countVector,bound,?_⟩
    by_cases pos : 0 < t + u
    · exact Or.inr pos
    · have noneFixed (i : Fin 2) : fixedSeedCount (n := 0) S i = 0 := by
        rw [fixed i, countVector]
        have tZero : t = 0 := by omega
        have uZero : u = 0 := by omega
        fin_cases i <;> simp [tZero, uZero]
      rcases zero_coordinate_counts_force_odd_dimension_or_even_multiplier
          S f card equiv c rows noneFixed with h | h
      · norm_num at h
      · exact Or.inl h
  · rintro ⟨t,u,rfl,fits,allowed⟩
    exact two_coordinate_attainment k t u fits allowed

end D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
