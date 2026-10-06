/- GID: D5/S1/Digit/Infinite/LateLabelStateBound
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/LateLabelStateBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Late nonnull windows at finite-source extrema require signed surviving states. -/

import D5.S1.Digit.Infinite.ClosedObservationGraphRealization
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.LateLabelStateBound

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.ClosedObservationGraphRealization
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open private prependBlock from D5.S1.Digit.Infinite.SignedSeriesFibres

universe u v

/-- A finite multigraph whose edges are literal lawful three-bit FIB windows.
The initial vertices all have incoming guard zero. -/
structure Representation (V : Type u) (E : Type v) [Fintype V] [Fintype E] where
  source : E → V
  target : E → V
  guard : V → Bool
  label : E → Label
  lawful_edge : ∀ e, lawful (guard (source e)) (label e) (guard (target e))
  initial : Finset V
  initial_guard : ∀ z ∈ initial, guard z = false

variable {V : Type u} {E : Type v} [Fintype V] [Fintype E]

/-- All infinite compatible edge sequences, with no further acceptance condition. -/
def Path (G : Representation V E) :=
  {a : ℕ → E // ∀ n, G.target (a n) = G.source (a (n + 1))}

/-- Delete exactly n edges of an infinite graph path. -/
def shiftPath {G : Representation V E} (p : Path G) (n : ℕ) : Path G :=
  ⟨fun j => p.val (j + n), fun j => by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using p.property (j + n)⟩

/-- Concatenation of a prefix and any compatible infinite continuation. -/
def splicePath {G : Representation V E} (p q : Path G) (n : ℕ)
    (h : G.source (q.val 0) = G.source (p.val n)) : Path G :=
  ⟨fun j => if j < n then p.val j else q.val (j - n), by
    intro j
    by_cases hj : j < n
    · by_cases hj' : j + 1 < n
      · simpa [hj, hj'] using p.property j
      · have he : j + 1 = n := by omega
        simp only [hj, ↓reduceIte, he, Nat.sub_self, Nat.lt_irrefl]
        have hp := p.property j
        rw [he] at hp
        exact hp.trans h.symm
    · have hj' : ¬ j + 1 < n := by omega
      simp only [hj, hj', ↓reduceIte]
      simpa [Nat.sub_add_comm (by omega : n ≤ j)] using q.property (j - n)⟩

/-- The unique legal digit address obtained by concatenating the original windows. -/
def pathAddress {G : Representation V E} (p : Path G) : LegalDigits :=
  ⟨fun j => (G.label (p.val (j / 3))).val ⟨j % 3, Nat.mod_lt _ (by decide)⟩, by
    intro j
    by_cases h : j % 3 < 2
    · have hd : (j + 1) / 3 = j / 3 := by omega
      have hm : (j + 1) % 3 = j % 3 + 1 := by omega
      simpa [hd, hm] using (G.label (p.val (j / 3))).property (j % 3) (by omega)
    · have hm : j % 3 = 2 := by omega
      have hd : (j + 1) / 3 = j / 3 + 1 := by omega
      have hm' : (j + 1) % 3 = 0 := by omega
      intro hh
      have ht : G.guard (G.source (p.val (j / 3 + 1))) = true := by
        rw [← p.property (j / 3), (G.lawful_edge (p.val (j / 3))).2]
        simpa [outgoing, hm] using hh.1
      have hz := (G.lawful_edge (p.val (j / 3 + 1))).1 ht
      have hn : (G.label (p.val (j / 3 + 1))).val 0 = true := by
        simpa [hd, hm'] using hh.2
      exact Bool.false_ne_true (hz.symm.trans hn)⟩

/-- The scalar image of every infinite path from the finite initial set. -/
def scalarImage (G : Representation V E) : Set ℝ :=
  {e | ∃ p : Path G, G.source (p.val 0) ∈ G.initial ∧ kappa p.pathAddress = e}

/-- Exactly the vertices retained after removing those with no infinite continuation. -/
def Surviving (G : Representation V E) :=
  {z : V // ∃ p : Path G, G.source (p.val 0) = z}

/-- The number of surviving vertices, whether reachable from the initial set or not. -/
noncomputable def survivorCount (G : Representation V E) : ℕ := Nat.card (Surviving G)

private theorem address_window {G : Representation V E} (p : Path G) (n : ℕ) :
    window p.pathAddress n = G.label (p.val n) := by
  apply Subtype.ext
  funext i
  simp only [window, D5.S1.Digit.Infinite.WindowSuccessorGraph.P, bitShift, pathAddress]
  have hd : (↑i + 3 * n) / 3 = n := by omega
  have hm : (↑i + 3 * n) % 3 = ↑i := by omega
  simp [hd, hm]

private theorem address_shift {G : Representation V E} (p : Path G) (n : ℕ) :
    (p.shiftPath n).pathAddress = bitShift p.pathAddress (3 * n) := by
  apply Subtype.ext
  funext j
  simp only [pathAddress, shiftPath, bitShift]
  have hd : (j + 3 * n) / 3 = j / 3 + n := by omega
  have hm : (j + 3 * n) % 3 = j % 3 := by omega
  simp [hd, hm]

private theorem splice_shift {G : Representation V E} (p q : Path G) (n : ℕ)
    (h : G.source (q.val 0) = G.source (p.val n)) :
    (p.splicePath q n h).shiftPath n = q := by
  apply Subtype.ext
  funext j
  simp [splicePath, shiftPath]

private theorem prepend_nonfinite (w : List Block) (x : LegalDigits)
    (hx : ¬ finiteTail x) : ¬ finiteTail (prependWord w x) := by
  induction w with
  | nil => exact hx
  | cons c w ih =>
    intro hh
    apply ih
    obtain ⟨N, hN⟩ := hh
    refine ⟨N, fun j hj => ?_⟩
    cases c with
    | zero => exact hN (j + 1) (by omega)
    | oneZero => exact hN (j + 2) (by omega)

private theorem alternating_nonfinite : ¬ finiteTail v := by
  rintro ⟨N, hN⟩
  have hh := hN (2 * N + 1) (by omega)
  simp [v] at hh

private theorem finite_address_unique (x y : LegalDigits) (hx : finiteTail x)
    (he : kappa y = kappa x) : y = x := by
  have ht : t ≠ 0 := (inv_pos.mpr Real.goldenRatio_pos).ne'
  have hv : signedValue y = signedValue x := by
    rw [closed_observation_graph_realization.1, closed_observation_graph_realization.1] at he
    exact neg_injective ((div_left_inj' (pow_ne_zero 2 ht)).mp he)
  have hn : signedValue x ∉ Set.range seam := by
    rintro ⟨w, hw⟩
    have hh := (signed_series_fibres.1 w).2 x
    obtain h | h := hh.mp hw.symm
    · apply prepend_nonfinite (w ++ [.zero]) v alternating_nonfinite
      simpa only [h, leftStream] using hx
    · apply prepend_nonfinite (w ++ [.oneZero]) v alternating_nonfinite
      simpa only [h, rightStream] using hx
  have hr : signedValue x ∈ Set.Icc a b := by
    rw [← signed_series_range.1]
    exact ⟨x, rfl⟩
  obtain ⟨z, hz, hu⟩ := signed_series_fibres.2.2 (signedValue x) hr hn
  exact (hu y hv).trans (hu x rfl).symm

private theorem finite_shift (x : LegalDigits) (n : ℕ) (hx : finiteTail x) :
    finiteTail (bitShift x n) := by
  obtain ⟨N, hN⟩ := hx
  exact ⟨N, fun j hj => hN (j + n) (by omega)⟩

private theorem path_recurrence {G : Representation V E} (p : Path G) :
    kappa p.pathAddress = offset (G.label (p.val 0)) - g * kappa (p.shiftPath 1).pathAddress := by
  have h := (closed_observation_graph_realization.2.2.1 p.pathAddress).1
  rw [address_window] at h
  simpa only [branch, originalT, address_shift, Nat.mul_one] using h

private theorem shift_add {G : Representation V E} (p : Path G) (n m : ℕ) :
    (p.shiftPath n).shiftPath m = p.shiftPath (m + n) := by
  apply Subtype.ext
  funext j
  simp [shiftPath, Nat.add_assoc]

private theorem prefix_difference {G : Representation V E} (p q : Path G) (n : ℕ)
    (h : ∀ j < n, G.label (p.val j) = G.label (q.val j)) :
    kappa p.pathAddress - kappa q.pathAddress =
      (-g) ^ n * (kappa (p.shiftPath n).pathAddress - kappa (q.shiftPath n).pathAddress) := by
  induction n generalizing p q with
  | zero =>
    simp only [pow_zero, one_mul]
    rfl
  | succ n ih =>
    have hh : ∀ j < n,
        G.label ((p.shiftPath 1).val j) = G.label ((q.shiftPath 1).val j) := by
      intro j hj
      exact h (j + 1) (by omega)
    have hi := ih (p.shiftPath 1) (q.shiftPath 1) hh
    rw [shift_add, shift_add] at hi
    calc
      kappa p.pathAddress - kappa q.pathAddress =
          (-g) * (kappa (p.shiftPath 1).pathAddress - kappa (q.shiftPath 1).pathAddress) := by
        rw [path_recurrence p, path_recurrence q, h 0 (by omega)]
        ring
      _ = (-g) ^ (n + 1) *
          (kappa (p.shiftPath (n + 1)).pathAddress - kappa (q.shiftPath (n + 1)).pathAddress) := by
        rw [hi, pow_succ]
        ring

private theorem splice_difference {G : Representation V E} (p q : Path G) (n : ℕ)
    (h : G.source (q.val 0) = G.source (p.val n)) :
    kappa (p.splicePath q n h).pathAddress - kappa p.pathAddress =
      (-g) ^ n * (kappa q.pathAddress - kappa (p.shiftPath n).pathAddress) := by
  have hh := prefix_difference (p.splicePath q n h) p n
    (fun j hj => by simp [splicePath, hj])
  rwa [splice_shift] at hh

private theorem splice_start {G : Representation V E} (p q : Path G) (n : ℕ)
    (h : G.source (q.val 0) = G.source (p.val n)) :
    G.source ((p.splicePath q n h).val 0) = G.source (p.val 0) := by
  by_cases hn : 0 < n
  · simp [splicePath, hn]
  · have hn' : n = 0 := by omega
    subst n
    simpa [splicePath] using h

private theorem equal_signed_tails {G : Representation V E} (p : Path G)
    (hp : G.source (p.val 0) ∈ G.initial)
    (he : IsLeast (scalarImage G) (kappa p.pathAddress) ∨
      IsGreatest (scalarImage G) (kappa p.pathAddress))
    (i k : ℕ) (hv : G.source (p.val i) = G.source (p.val k))
    (hs : i % 2 = k % 2) :
    kappa (p.shiftPath i).pathAddress = kappa (p.shiftPath k).pathAddress := by
  have hi : G.source ((p.shiftPath k).val 0) = G.source (p.val i) := by
    simpa [shiftPath] using hv.symm
  have hk : G.source ((p.shiftPath i).val 0) = G.source (p.val k) := by
    simpa [shiftPath] using hv
  have hmi : kappa (p.splicePath (p.shiftPath k) i hi).pathAddress ∈ scalarImage G :=
    ⟨_, (splice_start p (p.shiftPath k) i hi).symm ▸ hp, rfl⟩
  have hmk : kappa (p.splicePath (p.shiftPath i) k hk).pathAddress ∈ scalarImage G :=
    ⟨_, (splice_start p (p.shiftPath i) k hk).symm ▸ hp, rfl⟩
  have hdi := splice_difference p (p.shiftPath k) i hi
  have hdk := splice_difference p (p.shiftPath i) k hk
  have ht : g ≠ 0 := pow_ne_zero 3 (inv_pos.mpr Real.goldenRatio_pos).ne'
  have hpos : 0 < (-g) ^ i * (-g) ^ k := by
    rw [← pow_add]
    exact (Nat.even_iff.mpr (by omega : (i + k) % 2 = 0)).pow_pos (neg_ne_zero.mpr ht)
  rcases he with he | he
  · have hli := he.2 hmi
    have hlk := he.2 hmk
    have hai : 0 ≤ (-g) ^ i *
        (kappa (p.shiftPath k).pathAddress - kappa (p.shiftPath i).pathAddress) := by linarith
    have hak : 0 ≤ (-g) ^ k *
        (kappa (p.shiftPath i).pathAddress - kappa (p.shiftPath k).pathAddress) := by linarith
    rcases lt_or_gt_of_ne (pow_ne_zero i (neg_ne_zero.mpr ht)) with hn | hn
    · have hkn : (-g) ^ k < 0 := by nlinarith
      have h1 := nonpos_of_mul_nonneg_right hai hn
      have h2 := nonpos_of_mul_nonneg_right hak hkn
      linarith
    · have hkn : 0 < (-g) ^ k := by nlinarith
      have h1 := (mul_nonneg_iff_of_pos_left hn).mp hai
      have h2 := (mul_nonneg_iff_of_pos_left hkn).mp hak
      linarith
  · have hli := he.2 hmi
    have hlk := he.2 hmk
    have hai : (-g) ^ i *
        (kappa (p.shiftPath k).pathAddress - kappa (p.shiftPath i).pathAddress) ≤ 0 := by linarith
    have hak : (-g) ^ k *
        (kappa (p.shiftPath i).pathAddress - kappa (p.shiftPath k).pathAddress) ≤ 0 := by linarith
    rcases lt_or_gt_of_ne (pow_ne_zero i (neg_ne_zero.mpr ht)) with hn | hn
    · have hkn : (-g) ^ k < 0 := by nlinarith
      have h1 := nonneg_of_mul_nonpos_right hai hn
      have h2 := nonneg_of_mul_nonpos_right hak hkn
      linarith
    · have hkn : 0 < (-g) ^ k := by nlinarith
      have h1 := nonpos_of_mul_nonpos_right hai hn
      have h2 := nonpos_of_mul_nonpos_right hak hkn
      linarith

private theorem repeated_tail_null (x : LegalDigits) (hx : finiteTail x)
    (i k j : ℕ) (hik : i < k) (hij : i ≤ j)
    (he : bitShift x (3 * i) = bitShift x (3 * k)) : window x j = nullLabel := by
  obtain ⟨N, hN⟩ := hx
  let f : ℕ → Bool := fun n => x.val (n + 3 * i)
  have hp : Function.Periodic f (3 * (k - i)) := by
    intro n
    have hh := congrArg (fun z : LegalDigits => z.val n) he
    dsimp only [bitShift] at hh
    change x.val (n + 3 * (k - i) + 3 * i) = x.val (n + 3 * i)
    have hi : n + 3 * (k - i) + 3 * i = n + 3 * k := by omega
    rw [hi]
    exact hh.symm
  have hd : 1 ≤ 3 * (k - i) := by omega
  apply Subtype.ext
  funext r
  change x.val (↑r + 3 * j) = false
  have hm : ↑r + 3 * j = (3 * (j - i) + ↑r) + 3 * i := by omega
  rw [hm]
  change f (3 * (j - i) + ↑r) = false
  rw [← hp.nat_mul (N + 1) (3 * (j - i) + ↑r)]
  apply hN
  have hmul := Nat.mul_le_mul_left (N + 1) hd
  nlinarith

/-- Every actual finite-source extremum with a nonnull window at zero-based position j
requires at least ceil((j+2)/2) surviving vertices in any finite full-path representation. -/
theorem result (G : Representation V E) (e : ℝ)
    (he : IsLeast (scalarImage G) e ∨ IsGreatest (scalarImage G) e)
    (x : LegalDigits) (hx : finiteTail x) (hxe : kappa x = e)
    (j : ℕ) (hj : window x j ≠ nullLabel) :
    Nat.ceil (((j : ℝ) + 2) / 2) ≤ survivorCount G := by
  classical
  have hem : e ∈ scalarImage G := he.elim (fun h => h.1) (fun h => h.1)
  obtain ⟨p, hp, hpe⟩ := hem
  have haddr : p.pathAddress = x := finite_address_unique x p.pathAddress hx (hpe.trans hxe.symm)
  have hpf : finiteTail p.pathAddress := by rwa [haddr]
  have hpn : window p.pathAddress j ≠ nullLabel := by rwa [haddr]
  have hpex : IsLeast (scalarImage G) (kappa p.pathAddress) ∨
      IsGreatest (scalarImage G) (kappa p.pathAddress) := by rwa [hpe]
  haveI : Finite (Surviving G) :=
    inferInstanceAs (Finite {z : V // ∃ p : Path G, G.source (p.val 0) = z})
  letI : Fintype (Surviving G) := Fintype.ofFinite (Surviving G)
  let state : Fin (j + 2) → Surviving G × Fin 2 := fun n =>
    (⟨G.source (p.val n), ⟨p.shiftPath n, by simp [shiftPath]⟩⟩,
      ⟨n.val % 2, Nat.mod_lt _ (by decide)⟩)
  have hinj : Function.Injective state := by
    intro a b hab
    apply Fin.ext
    by_contra hne
    have hv : G.source (p.val a) = G.source (p.val b) :=
      congrArg (fun z : Surviving G × Fin 2 => z.1.val) hab
    have hs : a.val % 2 = b.val % 2 :=
      congrArg (fun z : Surviving G × Fin 2 => z.2.val) hab
    have ht := equal_signed_tails p hp hpex a b hv hs
    have hf : finiteTail (p.shiftPath a).pathAddress := by
      rw [address_shift]
      exact finite_shift p.pathAddress (3 * a.val) hpf
    have ha := finite_address_unique (p.shiftPath a).pathAddress (p.shiftPath b).pathAddress hf ht.symm
    rw [address_shift, address_shift] at ha
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hpn (repeated_tail_null p.pathAddress hpf a b j hlt (by omega) ha.symm)
    · exact hpn (repeated_tail_null p.pathAddress hpf b a j hlt (by omega) ha)
  have hc := Fintype.card_le_of_injective state hinj
  have hcount : j + 2 ≤ 2 * survivorCount G := by
    simpa only [Fintype.card_fin, Fintype.card_prod, survivorCount,
      Nat.card_eq_fintype_card, Nat.mul_comm] using hc
  rw [Nat.ceil_le]
  have hreal : (j : ℝ) + 2 ≤ 2 * (survivorCount G : ℝ) := by exact_mod_cast hcount
  linarith

end D5.S1.Digit.Infinite.LateLabelStateBound
