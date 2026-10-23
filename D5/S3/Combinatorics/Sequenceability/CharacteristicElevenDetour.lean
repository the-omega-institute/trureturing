/- GID: D5/S3/Combinatorics/Sequenceability/CharacteristicElevenDetour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/CharacteristicElevenDetour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Translated ten-column dynamics and four-cut paths in characteristic eleven. -/

import D5.S1.Words.Sequenceability.RowOrbitLift
import D5.S3.Combinatorics.PerfectMatchings.WeightedReattachment

/-! The translated ten-column construction. The original arbitrary-subset
sequenceability problem is outside the scope of this construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.CharacteristicElevenDetour

open Equiv
open D5.S1.Words.Sequenceability
open D5.S3.Combinatorics.PerfectMatchings
open FiniteEndpointPairing FiniteReturnTowers WeightedReattachment
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K]

/-- The ten nonzero columns, in doubling order. -/
def column : Fin 10 → ZMod 11 := ![1, 2, 4, 8, 5, 10, 9, 7, 3, 6]

/-- The column translations used in the actual affine action. -/
def shift (r : Kˣ) (u : K) : Fin 10 → K :=
  ![0, u, u, 0, 0, 0, -2 * u, 2 * u, 0, (1 + 2 / (r : K)) * u]

private def sign : Fin 10 → K := ![1, -1, 1, -1, 1, -1, 1, -1, 1, -1]

/-- Coordinates in which a round multiplies the row by r. -/
def rowCoordinates (r : Kˣ) (u : K) : (Fin 10 × K) ≃ (Fin 10 × K) where
  toFun v := (v.1, sign v.1 * v.2 + shift r u v.1)
  invFun v := (v.1, sign v.1 * (v.2 - shift r u v.1))
  left_inv := by rintro ⟨i, x⟩; fin_cases i <;> simp [sign]
  right_inv := by rintro ⟨i, x⟩; fin_cases i <;> simp [sign]

/-- The skew product of a ten-cycle with multiplication on the last step. -/
def roundStep (r : Kˣ) : Perm (Fin 10 × K) where
  toFun v := if v.1 = 9 then (0, (r : K) * v.2) else (v.1 + 1, v.2)
  invFun v := if v.1 = 0 then (9, (↑r⁻¹ : K) * v.2) else (v.1 - 1, v.2)
  left_inv := by rintro ⟨i, x⟩; fin_cases i <;> simp
  right_inv := by rintro ⟨i, x⟩; fin_cases i <;> simp

/-- The actual translated lift, with row h at each physical column. -/
def lift (r : Kˣ) (u : K) : Perm (Fin 10 × K) :=
  (rowCoordinates r u).permCongr (roundStep r)

/-- The actual ambient vertex. -/
def vertex (v : Fin 10 × K) : ZMod 11 × K := (column v.1, v.2)

def edgeLabel (r : Kˣ) (u : K) (v : Fin 10 × K) : ZMod 11 × K :=
  vertex (lift r u v) - vertex v

set_option maxHeartbeats 2000000 in
-- Expanding the ten affine coordinate cases includes symbolic field division.
private theorem lift_apply (r : Kˣ) (u h : K) (i : Fin 10) :
    lift r u (i, h) =
      if i = 9 then (0, -(r : K) * h + ((r : K) + 2) * u)
      else (i + 1, -h + shift r u i + shift r u (i + 1)) := by
  fin_cases i <;>
    simp [lift, rowCoordinates, roundStep, sign, shift]
  all_goals ring_nf
  all_goals simp [r.ne_zero]
  all_goals ring

private theorem round_phase (r : Kˣ) (x : K) (i : Fin 10) :
    (roundStep r ^ i.val) (0, x) = (i, x) := by
  fin_cases i <;> norm_num [pow_succ, Perm.mul_apply, roundStep]

private theorem round_ten (r : Kˣ) (x : K) :
    (roundStep r ^ 10) (0, x) = (0, (r : K) * x) := by
  norm_num [pow_succ, Perm.mul_apply, roundStep]

private theorem round_rounds (r : Kˣ) (x : K) (n : ℕ) :
    (roundStep r ^ (10 * n)) (0, x) = (0, (r : K) ^ n * x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, Perm.mul_apply, round_ten, ih, pow_succ]
    congr 1
    ring

private theorem round_position (r : Kˣ) (x : K) (n : ℕ) :
    (roundStep r ^ n) (0, x) =
      (⟨n % 10, Nat.mod_lt _ (by decide)⟩, (r : K) ^ (n / 10) * x) := by
  conv_lhs => rw [← Nat.div_add_mod n 10]
  rw [Nat.add_comm (10 * (n / 10)), pow_add, Perm.mul_apply]
  rw [round_rounds]
  exact round_phase r _ ⟨n % 10, Nat.mod_lt _ (by decide)⟩

private theorem round_same_cycle [Finite K] (r : Kˣ)
    (hr : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (v w : Fin 10 × K) :
    (roundStep r).SameCycle v w ↔ (v.2 = 0 ↔ w.2 = 0) := by
  have invariant (v : Fin 10 × K) :
      (roundStep r v).2 = 0 ↔ v.2 = 0 := by
    change (if v.1 = 9 then (0, (r : K) * v.2) else (v.1 + 1, v.2) : Fin 10 × K).2 = 0 ↔ v.2 = 0
    split_ifs <;> simp [r.ne_zero]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ', Perm.mul_apply, invariant] using ih
  · intro h
    have hrow := (RowOrbitLift.row_same_cycle_iff r hr 0 v.2 w.2).mpr h
    obtain ⟨n, hn⟩ := hrow.exists_nat_pow_eq
    have rowpow (n : ℕ) (x : K) :
        (RowOrbitLift.rowReturn r 0 ^ n) x = (r : K) ^ n * x := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Perm.mul_apply, ih, pow_succ']
        simp [RowOrbitLift.rowReturn, mul_assoc]
    have hm : (roundStep r).SameCycle (0, v.2) (0, w.2) := by
      refine ⟨(10 * n : ℕ), ?_⟩
      rw [zpow_natCast, round_rounds, ← rowpow, hn]
    have hv : (roundStep r).SameCycle (0, v.2) v :=
      ⟨(v.1.val : ℕ), by rw [zpow_natCast, round_phase]⟩
    have hw : (roundStep r).SameCycle (0, w.2) w :=
      ⟨(w.1.val : ℕ), by rw [zpow_natCast, round_phase]⟩
    exact hv.symm.trans (hm.trans hw)

omit [Field K] in
private theorem vertices_bijective :
    Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0} := by
  have hc : Function.Injective column := by decide
  have hn : ∀ i, column i ≠ 0 := by decide
  have hs : ∀ d : ZMod 11, d ≠ 0 → ∃ i, column i = d := by decide
  refine ⟨fun v _ => hn v.1, ?_, ?_⟩
  · intro v _ w _ h
    exact Prod.ext (hc (congrArg (fun z : ZMod 11 × K => z.1) h))
      (congrArg (fun z : ZMod 11 × K => z.2) h)
  · rintro ⟨d, h⟩ hd
    obtain ⟨i, hi⟩ := hs d hd
    exact ⟨(i, h), trivial, Prod.ext hi rfl⟩

private theorem labels_bijective [CharP K 11] (r : Kˣ)
    (hr : (r : K) + 1 ≠ 0) (u : K) :
    Set.BijOn (edgeLabel r u) Set.univ {v | v.1 ≠ 0} := by
  have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 11 2).not.mpr (by decide)
  have hc : Function.Injective column := by decide
  have hn : ∀ i, column i ≠ 0 := by decide
  have hs : ∀ d : ZMod 11, d ≠ 0 → ∃ i, column i = d := by decide
  have hcform (i : Fin 10) (h : K) :
      (edgeLabel r u (i, h)).1 = column i := by
    rw [edgeLabel, lift_apply]
    fin_cases i <;> norm_num [vertex, column] <;> decide
  have hrow (i : Fin 10) (h : K) :
      (edgeLabel r u (i, h)).2 =
        if i = 9 then -((r : K) + 1) * h + ((r : K) + 2) * u
        else -2 * h + shift r u i + shift r u (i + 1) := by
    rw [edgeLabel, lift_apply]
    split_ifs <;> simp [vertex] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, h⟩ _
    change (edgeLabel r u (i, h)).1 ≠ 0
    rw [hcform]
    exact hn i
  · rintro ⟨i, h⟩ _ ⟨j, k⟩ _ he
    have hi : i = j := hc (by simpa only [hcform] using congrArg Prod.fst he)
    subst j
    have hh := congrArg Prod.snd he
    rw [hrow, hrow] at hh
    have heq : h = k := by
      split_ifs at hh
      · have hz : ((r : K) + 1) * (h - k) = 0 := by linear_combination -hh
        exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hr)
      · have hz : (2 : K) * (h - k) = 0 := by linear_combination -hh
        exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left htwo)
    exact Prod.ext rfl heq
  · rintro ⟨d, h⟩ hd
    obtain ⟨i, hi⟩ := hs d hd
    by_cases h9 : i = 9
    · refine ⟨(i, (((r : K) + 2) * u - h) / ((r : K) + 1)), trivial, ?_⟩
      apply Prod.ext
      · simpa only [hcform] using hi
      · rw [hrow, ite_eq_left h9]
        field_simp
        ring
    · refine ⟨(i, (shift r u i + shift r u (i + 1) - h) / 2), trivial, ?_⟩
      apply Prod.ext
      · simpa only [hcform] using hi
      · rw [hrow, ite_eq_right h9]
        field_simp
        ring


private abbrev Carrier (K : Type*) := (Fin 10 × K) ⊕ Fin 2

private def basePerm (r : Kˣ) : Perm (Carrier K) := (roundStep r).sumCongr 1

private def coordinate (r : Kˣ) (u : K) : Carrier K → ZMod 11 × K
  | .inl v => vertex (rowCoordinates r u v)
  | .inr i => if i = 0 then (0, 0) else (0, u)

private def mark (u : K) : Fin 6 → Carrier K :=
  ![.inl (1, u), .inl (0, 2 * u), .inl (7, 2 * u), .inl (2, 0), .inr 0, .inr 1]

private theorem mark_injective (u : K) : Function.Injective (mark u) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [mark]

private def markEquiv (u : K) : Fin 6 ≃ Set.range (mark u) :=
  Equiv.ofBijective (fun i => ⟨mark u i, ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => mark_injective u (congrArg Subtype.val h),
      fun ⟨_, i, hi⟩ => ⟨i, Subtype.ext hi⟩⟩

private def rho : Perm (Fin 6) := swap 0 2 * swap 0 1

private def sigma : Perm (Fin 6) := swap 0 3 * swap 0 2 * swap 0 1

private def endpointInsertion : Perm (Fin 6) := swap 0 4 * swap 0 5

private def cutShuffle : Perm (Fin 6) := endpointInsertion * sigma

private def rewire (u : K) : Perm (Carrier K) :=
  swap (mark u 0) (mark u 4) * swap (mark u 0) (mark u 5) *
    swap (mark u 0) (mark u 3) * swap (mark u 0) (mark u 2) *
      swap (mark u 0) (mark u 1)

private def surgery (r : Kˣ) (u : K) : Perm (Carrier K) := rewire u * basePerm r

private theorem base_power (r : Kˣ) (n : ℕ) (v : Fin 10 × K) :
    (basePerm r ^ n) (.inl v) = .inl ((roundStep r ^ n) v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]; rfl

private theorem base_same_cycle [Finite K] (r : Kˣ)
    (hr : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) (v w : Fin 10 × K) :
    (basePerm r).SameCycle (.inl v) (.inl w) ↔ (v.2 = 0 ↔ w.2 = 0) := by
  rw [← round_same_cycle r hr]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [base_power] at hn
    exact ⟨(n : ℤ), by simpa only [zpow_natCast] using Sum.inl.inj hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast, base_power, hn]⟩

private theorem round_orbit_injective (r : Kˣ) (u : K) (hu : u ≠ 0) :
    Set.InjOn (fun n : ℕ => (roundStep r ^ n) (0, u))
      (Set.Iio (10 * orderOf r)) := by
  intro m hm n hn h
  dsimp only at h
  rw [round_position, round_position] at h
  have hphase : m % 10 = n % 10 := congrArg (fun v : Fin 10 × K => v.1.val) h
  have hrow : (r : K) ^ (m / 10) = (r : K) ^ (n / 10) :=
    mul_right_cancel₀ hu (congrArg Prod.snd h)
  have hunit : r ^ (m / 10) = r ^ (n / 10) := Units.ext (by simpa using hrow)
  have hm' : m / 10 < orderOf r := by change m < 10 * orderOf r at hm; omega
  have hn' : n / 10 < orderOf r := by change n < 10 * orderOf r at hn; omega
  have hdiv : m / 10 = n / 10 := pow_injOn_Iio_orderOf hm' hn' hunit
  omega

private theorem base_orbit_mod (r : Kˣ) (u : K) (n : ℕ) :
    (basePerm r ^ (n % (10 * orderOf r))) (.inl (0, u)) =
      (basePerm r ^ n) (.inl (0, u)) := by
  have hper : Function.IsPeriodicPt (basePerm r : Carrier K → Carrier K)
      (10 * orderOf r) (.inl (0, u)) := by
    change (basePerm r ^ (10 * orderOf r)) (.inl (0, u)) = .inl (0, u)
    rw [base_power, round_rounds]
    have he : (r : K) ^ orderOf r = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun z : Kˣ => (z : K)) (pow_orderOf_eq_one r)
    simp [he]
  exact hper.iterate_mod_apply n

private theorem first_visit_along {X : Type*} (f : Perm X) (S : Set X) (x : X)
    (a b : ℕ) (hab : a < b) (hb : (f ^ b) x ∈ S)
    (hgap : ∀ n, a < n → n < b → (f ^ n) x ∉ S) :
    FirstVisit f S ((f ^ a) x) (b - a) := by
  refine ⟨by omega, ?_, ?_⟩
  · rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hab.le]
    exact hb
  · intro k hk hkb
    rw [← Perm.mul_apply, ← pow_add]
    apply hgap (k + a) <;> omega

private theorem cut_return_data [Finite K] [CharP K 11]
    (r : Kˣ) (u : K) (hu : u ≠ 0) (k : ℕ)
    (hk0 : 0 < k) (hkL : k < orderOf r) (hpow : (r : K) ^ k = 2) :
    ∀ i : Fin 6, ∃ n : ℕ,
      FirstVisit (basePerm r) (Set.range (mark u)) (mark u i) n ∧
        (basePerm r ^ n) (mark u i) = mark u (rho i) := by
  let P := basePerm r
  let N := 10 * orderOf r
  let x : Carrier K := .inl (0, u)
  have hN : 0 < N := by dsimp [N]; exact Nat.mul_pos (by decide) (orderOf_pos r)
  have hbound : 10 * k + 7 < N := by dsimp [N]; omega
  have hpos₀ : (P ^ 1) x = mark u 0 := by simp [P, x, basePerm, roundStep, mark]
  have hpos₁ : (P ^ (10 * k)) x = mark u 1 := by
    rw [base_power, round_rounds]
    simp [mark, hpow]
  have hpos₂ : (P ^ (10 * k + 7)) x = mark u 2 := by
    rw [Nat.add_comm, pow_add, Perm.mul_apply, base_power, round_rounds]
    rw [base_power]
    simpa [mark, hpow] using
      congrArg (Sum.inl : Fin 10 × K → Carrier K) (round_phase r (2 * u) (7 : Fin 10))
  have hinj : Set.InjOn (fun n : ℕ => (P ^ n) x) (Set.Iio N) := by
    intro m hm n hn he
    apply round_orbit_injective r u hu hm hn
    exact Sum.inl.inj (by simpa only [P, x, base_power] using he)
  have hmod (n : ℕ) : (P ^ (n % N)) x = (P ^ n) x := base_orbit_mod r u n
  have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 11 2).not.mpr (by decide)
  have hlong (n : ℕ) : (P ^ n) x ∈ Set.range (mark u) ↔
      n % N = 1 ∨ n % N = 10 * k ∨ n % N = 10 * k + 7 := by
    have heq (a : ℕ) (ha : a < N) : (P ^ n) x = (P ^ a) x ↔ n % N = a := by
      rw [← hmod n]
      exact ⟨hinj (Nat.mod_lt _ hN) ha, fun h => congrArg (fun j => (P ^ j) x) h⟩
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl ((heq 1 (by omega)).mp (hi.symm.trans hpos₀.symm))
      · exact Or.inr (Or.inl ((heq _ (by omega)).mp (hi.symm.trans hpos₁.symm)))
      · exact Or.inr (Or.inr ((heq _ hbound).mp (hi.symm.trans hpos₂.symm)))
      · have hnz : (r : K) ^ (n / 10) * u ≠ 0 := mul_ne_zero (pow_ne_zero _ r.ne_zero) hu
        have he := congrArg (fun z : Carrier K => z) hi
        rw [show (P ^ n) x = .inl ((roundStep r ^ n) (0, u)) from base_power r n _,
          round_position] at he
        exact (hnz (congrArg Prod.snd (Sum.inl.inj he.symm))).elim
      · have he : mark u 4 = .inl ((roundStep r ^ n) (0, u)) := by simpa [P, x, base_power] using hi
        simp [mark] at he
      · have he : mark u 5 = .inl ((roundStep r ^ n) (0, u)) := by simpa [P, x, base_power] using hi
        simp [mark] at he
    · rintro (hn | hn | hn)
      · exact ⟨0, hpos₀.symm.trans ((heq 1 (by omega)).mpr hn).symm⟩
      · exact ⟨1, hpos₁.symm.trans ((heq _ (by omega)).mpr hn).symm⟩
      · exact ⟨2, hpos₂.symm.trans ((heq _ hbound).mpr hn).symm⟩
  have hb₀ : (P ^ 1) x ∈ Set.range (mark u) := ⟨0, hpos₀.symm⟩
  have hb₁ : (P ^ (10 * k)) x ∈ Set.range (mark u) := ⟨1, hpos₁.symm⟩
  have hb₂ : (P ^ (10 * k + 7)) x ∈ Set.range (mark u) := ⟨2, hpos₂.symm⟩
  have hwrap : (P ^ (N + 1)) x = mark u 0 := by
    rw [← hmod]
    have he : (N + 1) % N = 1 := by simp [Nat.mod_eq_of_lt (show 1 < N by omega)]
    rw [he, hpos₀]
  intro i
  fin_cases i
  · refine ⟨10 * k - 1, ?_, ?_⟩
    · change FirstVisit P _ (mark u 0) (10 * k - 1)
      rw [← hpos₀]
      apply first_visit_along P _ x 1 (10 * k) (by omega) hb₁
      intro n ha hb hn
      have hn' := hlong n |>.mp hn
      rw [Nat.mod_eq_of_lt (by omega : n < N)] at hn'
      omega
    · change (P ^ (10 * k - 1)) (mark u 0) = mark u (rho 0)
      rw [← hpos₀, ← Perm.mul_apply, ← pow_add]
      have he : 10 * k - 1 + 1 = 10 * k := by omega
      simpa [he, rho, swap_apply_def] using hpos₁
  · refine ⟨7, ?_, ?_⟩
    · change FirstVisit P _ (mark u 1) 7
      rw [← hpos₁, show 7 = (10 * k + 7) - 10 * k by omega]
      apply first_visit_along P _ x (10 * k) (10 * k + 7) (by omega) hb₂
      intro n ha hb hn
      have hn' := (hlong n).mp hn
      rw [Nat.mod_eq_of_lt (by omega : n < N)] at hn'
      omega
    · change (P ^ 7) (mark u 1) = mark u (rho 1)
      rw [← hpos₁, ← Perm.mul_apply, ← pow_add]
      simpa [Nat.add_comm, rho, swap_apply_def] using hpos₂
  · refine ⟨N + 1 - (10 * k + 7), ?_, ?_⟩
    · change FirstVisit P _ (mark u 2) (N + 1 - (10 * k + 7))
      rw [← hpos₂]
      apply first_visit_along P (Set.range (mark u)) x (10 * k + 7) (N + 1)
        (by omega) (show (P ^ (N + 1)) x ∈ Set.range (mark u) from ⟨0, hwrap.symm⟩)
      intro n ha hb hn
      have hn' := (hlong n).mp hn
      by_cases hnN : n < N
      · rw [Nat.mod_eq_of_lt hnN] at hn'; omega
      · have he : n = N := by omega
        simp [he] at hn'
        omega
    · change (P ^ (N + 1 - (10 * k + 7))) (mark u 2) = mark u (rho 2)
      rw [← hpos₂, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega)]
      simpa [rho, swap_apply_def] using hwrap
  · refine ⟨10, ?_, ?_⟩
    · refine ⟨by decide, ?_, ?_⟩
      · refine ⟨3, ?_⟩
        norm_num [P, mark, basePerm, roundStep, pow_succ, Perm.mul_apply]
      · intro n hn hn10
        interval_cases n <;>
          simp [mark, basePerm, roundStep, pow_succ, hu, htwo]
        all_goals aesop
    · norm_num [P, mark, basePerm, roundStep, rho, swap_apply_def, pow_succ, Perm.mul_apply]
  · refine ⟨1, ⟨by decide, ⟨4, rfl⟩, by intro n hn hn1; omega⟩, ?_⟩
    simp [mark, basePerm, rho, swap_apply_def]
  · refine ⟨1, ⟨by decide, ⟨5, rfl⟩, by intro n hn hn1; omega⟩, ?_⟩
    simp [mark, basePerm, rho, swap_apply_def]


set_option maxHeartbeats 1000000 in
-- The six marked return maps expand into composed subtype permutations.
private theorem surgery_cycle [Finite K] [CharP K 11]
    (r : Kˣ) (hr : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z)
    (u : K) (hu : u ≠ 0) (k : ℕ)
    (hk0 : 0 < k) (hkL : k < orderOf r) (hpow : (r : K) ^ k = 2) :
    (surgery r u).IsCycleOn Set.univ := by
  let P := basePerm r
  let S := Set.range (mark u)
  let e := markEquiv u
  let : DecidablePred (· ∈ S) := fun _ => Classical.propDecidable _
  let J : Perm S := e.permCongr cutShuffle
  let H : Perm S := e.permCongr rho
  let g := P * J.ofSubtype
  have he (i : Fin 6) : (e i : Carrier K) = mark u i := rfl
  have hfirst (x : S) : ∃ n : ℕ, FirstVisit P S x n ∧ (P ^ n) x = H x := by
    obtain ⟨i, rfl⟩ := e.surjective x
    obtain ⟨n, hn, hp⟩ := cut_return_data r u hu k hk0 hkL hpow i
    refine ⟨n, hn, ?_⟩
    simpa only [H, Equiv.permCongr_apply, Equiv.symm_apply_apply, he] using hp
  have hjump (x : S) : ∃ n : ℕ,
      FirstVisit g S x n ∧ (g ^ n) x = (H * J) x := by
    obtain ⟨n, hn, hp⟩ := hfirst (J x)
    obtain ⟨hn', hp'⟩ := first_visit_reattach P S J x n hn
    exact ⟨n, hn', hp'.trans hp⟩
  have hfour : sigma * rho = swap 0 3 * swap 0 1 * swap 0 2 := by
    ext i
    fin_cases i <;> decide
  have hshuffle : rho * cutShuffle =
      rho * endpointInsertion * (swap 0 3 * swap 0 1 * swap 0 2) * rho⁻¹ := by
    rw [← hfour]
    simp [cutShuffle, mul_assoc]
  have hind : (rho * cutShuffle).IsCycleOn Set.univ := by
    have hreach (i : Fin 6) : (rho * cutShuffle).SameCycle 0 i := by
      rw [hshuffle]
      fin_cases i
      · exact .refl _ _
      · exact ⟨(5 : ℕ), by norm_num [rho, endpointInsertion,
          pow_succ, Perm.mul_apply, swap_apply_def]⟩
      · exact ⟨(1 : ℕ), by norm_num [rho, endpointInsertion,
          pow_succ, Perm.mul_apply, swap_apply_def]⟩
      · exact ⟨(2 : ℕ), by norm_num [rho, endpointInsertion,
          pow_succ, Perm.mul_apply, swap_apply_def]⟩
      · exact ⟨(4 : ℕ), by norm_num [rho, endpointInsertion,
          pow_succ, Perm.mul_apply, swap_apply_def]⟩
      · exact ⟨(3 : ℕ), by norm_num [rho, endpointInsertion,
          pow_succ, Perm.mul_apply, swap_apply_def]⟩
    exact ⟨(rho * cutShuffle).bijective.bijOn_univ,
      fun i _ j _ => (hreach i).symm.trans (hreach j)⟩
  have hmarks (x y : S) : g.SameCycle x y := by
    apply (same_cycle_of_first_visit g S (H * J) hjump x y).mpr
    obtain ⟨i, rfl⟩ := e.surjective x
    obtain ⟨j, rfl⟩ := e.surjective y
    have hm : H * J = e.permCongr (rho * cutShuffle) :=
      (map_mul e.permCongrHom rho cutShuffle).symm
    rw [hm]
    exact (FiniteBandSwitch.same_cycle_perm_congr e _ i j).mpr (hind.2 trivial trivial)
  have hold (z : Carrier K) : ∃ x : S, P.SameCycle x z := by
    cases z with
    | inl v =>
      by_cases hv : v.2 = 0
      · refine ⟨e 3, ?_⟩
        apply (base_same_cycle r hr _ _).mpr
        simpa [he, mark] using hv
      · refine ⟨e 0, ?_⟩
        apply (base_same_cycle r hr _ _).mpr
        simpa [he, mark, hu] using hv
    | inr i =>
      fin_cases i
      · exact ⟨e 4, Perm.SameCycle.refl P _⟩
      · exact ⟨e 5, Perm.SameCycle.refl P _⟩
  have hnew (z : Carrier K) : ∃ x : S, g.SameCycle x z := by
    by_contra hn
    have hn' : ∀ x : S, ¬ g.SameCycle x z := by simpa using hn
    have horig := (untouched_reattach_iff P S J z).mp (by simpa only [g] using hn')
    obtain ⟨x, hx⟩ := hold z
    exact horig x hx
  have hg : g.IsCycleOn Set.univ := by
    refine ⟨g.bijective.bijOn_univ, ?_⟩
    intro x _ y _
    obtain ⟨a, ha⟩ := hnew x
    obtain ⟨b, hb⟩ := hnew y
    exact ha.symm.trans ((hmarks a b).trans hb)
  have hJ : J.ofSubtype = rewire u := by
    have hswap (i j : Fin 6) :
        (e.permCongr (swap i j)).ofSubtype = swap (mark u i) (mark u j) := by
      have hcongr : e.permCongr (swap i j) = swap (e i) (e j) :=
        Equiv.symm_trans_swap_trans i j e
      rw [hcongr, Perm.ofSubtype_swap_eq]
      rfl
    have hmul (a b : Perm (Fin 6)) :
        (e.permCongr (a * b)).ofSubtype =
          (e.permCongr a).ofSubtype * (e.permCongr b).ofSubtype := by
      exact (congrArg (fun f : Perm S => f.ofSubtype)
        (map_mul e.permCongrHom a b)).trans (map_mul Perm.ofSubtype _ _)
    simp only [J, cutShuffle, endpointInsertion, sigma, hmul, hswap, rewire, mul_assoc]
  have hconj := hg.conj (g := P⁻¹)
  have hfull : (P⁻¹ : Perm (Carrier K)) '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective P⁻¹.surjective
  rw [hfull] at hconj
  have heq : P⁻¹ * g * (P⁻¹)⁻¹ = surgery r u := by
    simp only [g, inv_mul_cancel_left, inv_inv, hJ, surgery, P]
  rw [heq] at hconj
  exact hconj


private theorem coordinate_injective (r : Kˣ) (u : K) (hu : u ≠ 0) :
    Function.Injective (coordinate r u) := by
  have hv := vertices_bijective (K := K)
  rintro (v | i) (w | j) he
  · exact congrArg Sum.inl ((rowCoordinates r u).injective (hv.2.1 trivial trivial he))
  · have hn := hv.1 (Set.mem_univ (rowCoordinates r u v))
    have hz := congrArg Prod.fst he
    fin_cases j <;> exact (hn hz).elim
  · have hn := hv.1 (Set.mem_univ (rowCoordinates r u w))
    have hz := congrArg Prod.fst he
    fin_cases i <;> exact (hn hz.symm).elim
  · fin_cases i <;> fin_cases j <;> simp_all [coordinate]


set_option maxHeartbeats 2000000 in
-- The full vector comparison expands five exceptional tails and the untouched complement.
private theorem surgery_labels [CharP K 11] (r : Kˣ)
    (hr : (r : K) + 1 ≠ 0) (u : K) :
    Set.BijOn (fun z => coordinate r u (surgery r u z) - coordinate r u z)
      {z | z ≠ Sum.inr 1} ({v | v.1 ≠ 0} ∪ {(0, u)}) := by
  let s : Carrier K := .inr 0
  let t : Carrier K := .inr 1
  let a : Carrier K := .inl (0, u)
  let b : Carrier K := .inl (9, (2 / (r : K)) * u)
  let c : Carrier K := .inl (6, 2 * u)
  let d : Carrier K := .inl (1, 0)
  let ψ : Perm (Carrier K) := swap s a * swap s b * swap s c * swap s d
  let L : Carrier K → ZMod 11 × K := fun z =>
    match z with
    | .inl v => edgeLabel r u (rowCoordinates r u v)
    | .inr _ => (0, u)
  have hP₁ : basePerm r a = mark u 0 := by simp [basePerm, a, roundStep, mark]
  have hP₂ : basePerm r b = mark u 1 := by
    simp [basePerm, b, roundStep, mark]
    field_simp
  have hP₃ : basePerm r c = mark u 2 := by simp [basePerm, c, roundStep, mark]
  have hP₄ : basePerm r d = mark u 3 := by simp [basePerm, d, roundStep, mark]
  have hLt : ψ t = t := by simp [ψ, s, t, a, b, c, d, swap_apply_def]
  have hψ : Set.BijOn ψ {z | z ≠ t} {z | z ≠ t} :=
    ψ.bijOn (fun z => by
      change ψ z ≠ t ↔ z ≠ t
      conv_lhs => rw [← hLt]
      exact not_congr ψ.injective.eq_iff)
  have he : Set.BijOn (fun v => edgeLabel r u (rowCoordinates r u v))
      Set.univ {v | v.1 ≠ 0} :=
    (labels_bijective r hr u).comp (rowCoordinates r u).bijective.bijOn_univ
  have hL : Set.BijOn L {z | z ≠ t} ({v | v.1 ≠ 0} ∪ {(0, u)}) := by
    constructor
    · rintro (v | i) hz
      · exact Or.inl (he.1 trivial)
      · exact Or.inr rfl
    constructor
    · rintro (v | i) hz (w | j) hw h
      · exact congrArg Sum.inl (he.2.1 trivial trivial h)
      · have hh := congrArg Prod.fst h
        exact ((he.1 (Set.mem_univ v)) hh).elim
      · have hh := congrArg Prod.fst h
        exact ((he.1 (Set.mem_univ w)) hh.symm).elim
      · have hi : i = 0 := by fin_cases i <;> simp_all [t]
        have hj : j = 0 := by fin_cases j <;> simp_all [t]
        simp [hi, hj]
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨v, _, hv⟩ := he.2.2 hy
        exact ⟨.inl v, by simp [t], hv⟩
      · exact ⟨s, by simp [s, t], hy.symm⟩
  have hdiff (z : Carrier K) (hz : z ≠ t) :
      coordinate r u (surgery r u z) - coordinate r u z = L (ψ z) := by
    by_cases hza : z = a
    · subst z
      apply Prod.ext
      · norm_num [surgery, rewire, coordinate, ψ, L, s, a, b, c, d, mark,
          basePerm, vertex, column, edgeLabel, lift_apply, rowCoordinates, sign, shift,
          roundStep, swap_apply_def]
      · simp [surgery, rewire, coordinate, ψ, L, s, a, b, c, d, mark,
          basePerm, vertex, column, edgeLabel, lift_apply, rowCoordinates, sign, shift,
          roundStep, swap_apply_def]
        ring
    by_cases hzb : z = b
    · subst z
      rw [show surgery r u b = mark u 2 by
        rw [surgery, Perm.mul_apply, hP₂]
        simp [rewire, mark, swap_apply_def]]
      apply Prod.ext
      · norm_num [coordinate, ψ, L, s, a, b, c, d, mark, vertex, column,
          edgeLabel, lift_apply, rowCoordinates, sign, shift, swap_apply_def]
      · simp [coordinate, ψ, L, s, a, b, c, d, mark, vertex, column,
          edgeLabel, lift_apply, rowCoordinates, sign, shift, swap_apply_def]
        field_simp
        ring
    by_cases hzc : z = c
    · subst z
      rw [show surgery r u c = mark u 3 by
        rw [surgery, Perm.mul_apply, hP₃]
        simp [rewire, mark, swap_apply_def]]
      apply Prod.ext
      · norm_num [coordinate, ψ, L, s, a, b, c, d, mark, vertex, column,
          edgeLabel, lift_apply, rowCoordinates, sign, shift, swap_apply_def]
      · simp [coordinate, ψ, L, s, a, b, c, d, mark, vertex, column,
          edgeLabel, lift_apply, rowCoordinates, sign, shift, swap_apply_def]
        field_simp
        ring
    by_cases hzd : z = d
    · subst z
      rw [show surgery r u d = t by
        rw [surgery, Perm.mul_apply, hP₄]
        simp [rewire, mark, t, swap_apply_def]]
      apply Prod.ext
      · norm_num [coordinate, ψ, L, s, t, a, b, c, d, mark, vertex, column,
          edgeLabel, lift_apply, rowCoordinates, sign, shift, swap_apply_def]
      · simp [coordinate, ψ, L, s, t, a, b, c, d, mark, vertex, column,
          edgeLabel, lift_apply, rowCoordinates, sign, shift, swap_apply_def]
    by_cases hzs : z = s
    · subst z
      apply Prod.ext
      · norm_num [surgery, rewire, coordinate, ψ, L, s, a, b, c, d, mark,
          basePerm, vertex, column, edgeLabel, lift_apply, rowCoordinates, sign, shift,
          roundStep, swap_apply_def]
      · simp [surgery, rewire, coordinate, ψ, L, s, a, b, c, d, mark,
          basePerm, vertex, column, edgeLabel, lift_apply, rowCoordinates, sign, shift,
          roundStep, swap_apply_def]
    have hp₁ : basePerm r z ≠ mark u 0 := by
      rw [← hP₁]; exact (basePerm r).injective.ne hza
    have hp₂ : basePerm r z ≠ mark u 1 := by
      rw [← hP₂]; exact (basePerm r).injective.ne hzb
    have hp₃ : basePerm r z ≠ mark u 2 := by
      rw [← hP₃]; exact (basePerm r).injective.ne hzc
    have hp₄ : basePerm r z ≠ mark u 3 := by
      rw [← hP₄]; exact (basePerm r).injective.ne hzd
    have hps : basePerm r z ≠ mark u 4 := by
      have hs : basePerm r s = mark u 4 := rfl
      rw [← hs]; exact (basePerm r).injective.ne hzs
    have hpt : basePerm r z ≠ mark u 5 := by
      have ht : basePerm r t = mark u 5 := rfl
      rw [← ht]; exact (basePerm r).injective.ne hz
    have hψz : ψ z = z := by
      simp [ψ, Perm.mul_apply, swap_apply_of_ne_of_ne, hza, hzb, hzc, hzd, hzs]
    rw [hψz]
    have hQz : surgery r u z = basePerm r z := by
      simp only [surgery, rewire, Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hp₁ hp₂,
        swap_apply_of_ne_of_ne hp₁ hp₃, swap_apply_of_ne_of_ne hp₁ hp₄,
        swap_apply_of_ne_of_ne hp₁ hpt, swap_apply_of_ne_of_ne hp₁ hps]
    rw [hQz]
    cases z with
    | inl v =>
      change vertex (rowCoordinates r u (roundStep r v)) - vertex (rowCoordinates r u v) =
        vertex (lift r u (rowCoordinates r u v)) - vertex (rowCoordinates r u v)
      simp only [lift, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    | inr i => fin_cases i <;> simp_all [s, t]
  exact (hL.comp hψ).congr (fun z hz => (hdiff z hz).symm)



private theorem primitive_data [Finite K] [CharP K 11] :
    ∃ r : Kˣ, (∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) ∧
      (r : K) + 1 ≠ 0 ∧ orderOf r = Nat.card K - 1 ∧
      ∃ k : ℕ, 0 < k ∧ k < Nat.card K - 1 ∧ (r : K) ^ k = 2 := by
  let := Fintype.ofFinite K
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hn : ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z := by
    intro z
    exact (Submonoid.mem_powers_iff z r).mp (mem_powers_iff_mem_zpowers.mpr (hr z))
  have hord : orderOf r = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hr, Nat.card_eq_fintype_card,
      Fintype.card_units, ← Nat.card_eq_fintype_card]
  have htwo : (2 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 11 2).not.mpr (by decide)
  have hthree : (3 : K) ≠ 0 := (CharP.cast_eq_zero_iff K 11 3).not.mpr (by decide)
  have hrn : (r : K) + 1 ≠ 0 := by
    intro he
    have he' : (r : K) = -1 := by linear_combination he
    obtain ⟨n, h⟩ := hn (Units.mk0 2 htwo)
    have h' : (-1 : K) ^ n = 2 := by
      simpa [he'] using congrArg (fun z : Kˣ => (z : K)) h
    have hpall : ∀ m : ℕ, (-1 : K) ^ m = 1 ∨ (-1 : K) ^ m = -1 := by
      intro m
      induction m with
      | zero => exact Or.inl (by simp)
      | succ m ih => rcases ih with ih | ih <;> simp [pow_succ, ih]
    rcases hpall n with hp | hp
    · apply one_ne_zero (α := K)
      linear_combination hp - h'
    · apply hthree
      linear_combination hp - h'
  obtain ⟨n, hn₂⟩ := hn (Units.mk0 2 htwo)
  let k := n % orderOf r
  have hkL : k < orderOf r := Nat.mod_lt _ (orderOf_pos r)
  have hkpow : (r : K) ^ k = 2 := by
    have h : r ^ k = Units.mk0 2 htwo := (pow_mod_orderOf r n).trans hn₂
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using
      congrArg (fun z : Kˣ => (z : K)) h
  have hk0 : 0 < k := by
    by_contra h
    have hk : k = 0 := by omega
    rw [hk, pow_zero] at hkpow
    apply one_ne_zero (α := K)
    linear_combination -hkpow
  exact ⟨r, hn, hrn, hord, k, hk0, hord ▸ hkL, hkpow⟩

/-- Every finite field of characteristic eleven has the translated relative path,
with exact vertex and full vector-label inventories and all bounded intervals. -/
theorem exists_characteristic_eleven_relative_path (K : Type*)
    [Field K] [Finite K] [CharP K 11] (u : K) (hu : u ≠ 0) :
    let M := 10 * Nat.card K + 1
    ∃ v : ℕ → ZMod 11 × K,
      v 0 = (0, 0) ∧ v M = (0, u) ∧
      Function.Injective (fun n : Fin (M + 1) => v n.val) ∧
      Set.BijOn v (Set.Ioo 0 M) {z | z.1 ≠ 0} ∧
      Set.BijOn (fun n => v (n + 1) - v n) (Set.Iio M)
        ({z | z.1 ≠ 0} ∪ {(0, u)}) ∧
      Function.Injective (fun k : Fin (M + 1) =>
        ∑ i ∈ Finset.range k.val, (v (i + 1) - v i)) ∧
      (∀ a b : ℕ, a < b → b ≤ M →
        (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) ≠ 0) ∧
      (∑ i ∈ Finset.range M, (v (i + 1) - v i)) = (0, u) := by
  let := Fintype.ofFinite K
  let M := 10 * Nat.card K + 1
  obtain ⟨r, hr, hrn, hord, k, hk0, hkL, hkpow⟩ := primitive_data (K := K)
  let Q := surgery r u
  let s : Carrier K := .inr 0
  let t : Carrier K := .inr 1
  let orbit : ℕ → Carrier K := fun n => (Q ^ n) s
  let v : ℕ → ZMod 11 × K := coordinate r u ∘ orbit
  have hcard : Fintype.card (Carrier K) = M + 1 := by
    simp only [Carrier, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      M, Nat.card_eq_fintype_card]
  have hcyc : Q.IsCycleOn (Finset.univ : Finset (Carrier K)) := by
    simpa only [Finset.coe_univ] using surgery_cycle r hr u hu k hk0 (hord.symm ▸ hkL) hkpow
  have hbound : Set.InjOn orbit (Set.Iio (M + 1)) := by
    simpa only [Finset.card_univ, hcard] using hcyc.injOn_pow_apply (Finset.mem_univ s)
  have horbit (z : Carrier K) : ∃ n < M + 1, orbit n = z := by
    simpa only [Finset.card_univ, hcard] using
      hcyc.exists_pow_eq (Finset.mem_univ s) (Finset.mem_univ z)
  have hzero : orbit 0 = s := rfl
  have hcoord := coordinate_injective r u hu
  have hclosing : coordinate r u (Q t) - coordinate r u t = (0, -u) := by
    simp [Q, surgery, rewire, t, coordinate, basePerm, mark, Perm.mul_apply,
      swap_apply_def]
  have hQt : Q t = s := by
    apply hcoord
    have he : coordinate r u t = (0, u) := by simp [coordinate, t]
    have hs : coordinate r u s = (0, 0) := by simp [coordinate, s]
    rw [he] at hclosing
    rw [hs]
    apply Prod.ext
    · have h := congrArg Prod.fst hclosing
      simpa using h
    · have h := congrArg Prod.snd hclosing
      change (coordinate r u (Q t)).2 - u = -u at h
      linear_combination h
  have hlast : orbit M = t := by
    apply Q.injective
    rw [hQt]
    have hclose := hcyc.pow_card_apply (Finset.mem_univ s)
    simpa only [Finset.card_univ, hcard, pow_succ', Perm.mul_apply] using hclose
  have hvinj : Function.Injective (fun n : Fin (M + 1) => v n.val) := by
    intro i j hij
    exact Fin.ext (hbound i.isLt j.isLt (hcoord hij))
  have hv0 : v 0 = (0, 0) := rfl
  have hvM : v M = (0, u) := by simp [v, Function.comp_apply, hlast, coordinate, t]
  have hinside : Set.BijOn orbit (Set.Ioo 0 M) (Set.range Sum.inl) := by
    constructor
    · intro n hn
      rcases hn with ⟨hn0, hnM⟩
      cases heq : orbit n with
      | inl z => exact ⟨z, rfl⟩
      | inr i =>
        fin_cases i
        · have hh : n = 0 := hbound (x₁ := n) (x₂ := 0)
            (by change n < M + 1; omega) (by change 0 < M + 1; omega)
            (heq.trans hzero.symm)
          omega
        · have hh : n = M := hbound (x₁ := n) (x₂ := M)
            (by change n < M + 1; omega) (by change M < M + 1; omega)
            (heq.trans hlast.symm)
          omega
    constructor
    · intro i hi j hj hij
      exact hbound (x₁ := i) (x₂ := j)
        (by change i < M + 1; exact Nat.lt_succ_of_lt hi.2)
        (by change j < M + 1; exact Nat.lt_succ_of_lt hj.2) hij
    · rintro z ⟨w, rfl⟩
      obtain ⟨n, hn, heq⟩ := horbit (.inl w)
      have hn0 : n ≠ 0 := by intro h; subst n; cases heq
      have hnM : n ≠ M := by
        intro h
        subst n
        rw [hlast] at heq
        simp only [t, reduceCtorEq] at heq
      exact ⟨n, ⟨by omega, by omega⟩, heq⟩
  have hcoords : Set.BijOn (coordinate r u) (Set.range Sum.inl) {z | z.1 ≠ 0} := by
    have hv := vertices_bijective (K := K)
    constructor
    · rintro z ⟨w, rfl⟩
      exact hv.1 trivial
    constructor
    · exact hcoord.injOn
    · intro z hz
      obtain ⟨w, _, hw⟩ := hv.2.2 hz
      exact ⟨.inl ((rowCoordinates r u).symm w), ⟨_, rfl⟩, by
        simpa only [coordinate, Equiv.apply_symm_apply] using hw⟩
  have hpunctured : Set.BijOn orbit (Set.Iio M) {z | z ≠ t} := by
    constructor
    · intro n hn heq
      change n < M at hn
      have hh : n = M := hbound (x₁ := n) (x₂ := M)
            (by change n < M + 1; omega) (by change M < M + 1; omega)
            (heq.trans hlast.symm)
      omega
    constructor
    · intro i hi j hj hij
      exact hbound (x₁ := i) (x₂ := j)
        (by change i < M + 1; exact Nat.lt_succ_of_lt hi)
        (by change j < M + 1; exact Nat.lt_succ_of_lt hj) hij
    · intro z hz
      obtain ⟨n, hn, heq⟩ := horbit z
      have hnM : n ≠ M := by intro h; subst n; exact hz (heq.symm.trans hlast)
      exact ⟨n, (show n < M from by omega), heq⟩
  have hlabels := (surgery_labels r hrn u).comp hpunctured
  have hstep (n : ℕ) : orbit (n + 1) = Q (orbit n) := by
    simp only [orbit, pow_succ', Perm.mul_apply]
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, (v (i + 1) - v i)) = v n - v 0 :=
    Finset.sum_range_sub v n
  refine ⟨v, hv0, hvM, hvinj, hcoords.comp hinside, ?_, ?_, ?_, ?_⟩
  · exact hlabels.congr (fun n _ => by
      change coordinate r u (Q (orbit n)) - coordinate r u (orbit n) =
        coordinate r u (orbit (n + 1)) - coordinate r u (orbit n)
      rw [hstep])
  · intro i j heq
    apply hvinj
    simpa only [hsum, sub_left_inj] using heq
  · intro a b hab hb hzero
    have hinterval : (∑ i ∈ Finset.Ico a b, (v (i + 1) - v i)) = v b - v a := by
      rw [Finset.sum_Ico_eq_sub _ hab.le, hsum, hsum]
      abel
    have heq : v b = v a := sub_eq_zero.mp (hinterval.symm.trans hzero)
    have hij := hvinj (a₁ := ⟨b, by omega⟩) (a₂ := ⟨a, by omega⟩) heq
    have heqb : b = a := congrArg Fin.val hij
    omega
  · rw [hsum, hv0, hvM]
    simp

#print axioms exists_characteristic_eleven_relative_path

end
end D5.S3.Combinatorics.Sequenceability.CharacteristicElevenDetour
