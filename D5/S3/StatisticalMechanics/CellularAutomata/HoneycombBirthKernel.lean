/- GID: D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel
   mirror-E: none(waiver:pure)
   anchors: []
   utility: none
   digest: Adjacent-cut birth polynomials and their normalized honeycomb kernels. -/

import D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch

/-! Signed birth polynomials, dyadic strip transport, and the normalized kernel readout. -/

namespace D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel

open D5.S3.StatisticalMechanics.HoneycombCylinderCoordination (Vertex honeycombGraph)
open D5.S3.StatisticalMechanics.CellularAutomata.HoneycombFirstTouch
open Polynomial
open scoped BigOperators

section

/-! Birth counting and signed support. -/

variable {G : SimpleGraph Vertex} [DecidableRel G.Adj]

private theorem adjacent_cut_subset (a d : ℕ) : omegaDomain a (d + 1) ⊆ omegaDomain a d :=
  domain_cut_mono (by omega)

private noncomputable def birthMonomial (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (D : Finset Vertex) (v : Vertex) : ℤ[X] := by
  classical
  exact if event : ∃ t, Born G D (A 0 0) t v then X ^ Nat.find event else 0

/-- The Definition 3 polynomial. Each retained vertex supplies at most one monomial. -/
private noncomputable def L (G : SimpleGraph Vertex) [DecidableRel G.Adj] (a d : ℕ) : ℤ[X] :=
  ∑ v ∈ omegaDomain a d, birthMonomial G (omegaDomain a d) v

noncomputable def delta (G : SimpleGraph Vertex) [DecidableRel G.Adj] (a d : ℕ) : ℤ[X] :=
  L G a d - L G a (d + 1)

def birthWeight (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (D : Finset Vertex) (t : ℕ) (v : Vertex) : ℤ :=
  if state G D (A 0 0) t v = some (t, 1) then 1 else 0

def signedWeight (G : SimpleGraph Vertex) [DecidableRel G.Adj]
    (a d t : ℕ) (v : Vertex) : ℤ :=
  birthWeight G (omegaDomain a d) t v - birthWeight G (omegaDomain a (d + 1)) t v

private theorem birthMonomial_coeff (D : Finset Vertex) (t : ℕ) (v : Vertex) :
    (birthMonomial G D v).coeff t = birthWeight G D t v := by
  classical
  unfold birthMonomial birthWeight
  split
  · rename_i event
    rw [coeff_X_pow]
    by_cases birth : Born G D (A 0 0) t v
    · have timeEq := (touch_unique birth (Nat.find_spec event)).1
      have stored : state G D (A 0 0) t v = some (t, 1) := birth
      simp [timeEq, timeEq ▸ stored]
    · have timeNe : t ≠ Nat.find event := fun eq => birth (eq ▸ Nat.find_spec event)
      have storedNe : state G D (A 0 0) t v ≠ some (t, 1) := birth
      simp [timeNe, storedNe]
  · rename_i noEvent
    have storedNe : state G D (A 0 0) t v ≠ some (t, 1) :=
      fun he => noEvent ⟨t, he⟩
    simp [storedNe]

private theorem birthWeight_outside {D : Finset Vertex} {t : ℕ} {v : Vertex}
    (outside : v ∉ D) : birthWeight G D t v = 0 := by
  have storedNe : state G D (A 0 0) t v ≠ some (t, 1) :=
    fun he => outside (touch_retained_and_positive he).1
  simp [birthWeight, storedNe]

private theorem coeff_L_on {U : Finset Vertex} {a d : ℕ} (sub : omegaDomain a d ⊆ U) (t : ℕ) :
    (L G a d).coeff t = ∑ v ∈ U, birthWeight G (omegaDomain a d) t v := by
  rw [L, finsetSum_coeff]
  simp only [birthMonomial_coeff]
  exact Finset.sum_subset sub (fun _ _ outside => birthWeight_outside outside)

theorem coeff_delta_on {U : Finset Vertex} {a d : ℕ} (sub : omegaDomain a d ⊆ U) (t : ℕ) :
    (delta G a d).coeff t = ∑ v ∈ U, signedWeight G a d t v := by
  rw [delta, coeff_sub, coeff_L_on sub t, coeff_L_on ((adjacent_cut_subset a d).trans sub) t,
    ← Finset.sum_sub_distrib]
  rfl

/-- The signed-support consequence of Lemma 36, at arbitrary positive integral heights. -/
private def SignedSupport (G : SimpleGraph Vertex) [DecidableRel G.Adj] : Prop :=
  ∀ a d, d < a → ∀ j v, signedWeight G a d (2 * a - d - 1 + j) v ≠ 0 →
    v ∈ omegaDomain a d ∧
      ∃ i : ℕ, g v = ((2 * a - d - 1 : ℕ) : ℤ) - i ∧ i + v.2.2.toNat ≤ j

end

section

/-! Translation and interface geometry of a dyadic strip. -/

variable {G : SimpleGraph Vertex} [DecidableRel G.Adj]

/-- Translation of the small triangle by (k) in the x direction. -/
private def shiftX (k : ℤ) : Vertex ≃ Vertex where
  toFun v := (v.1, v.2.1 + k, v.2.2)
  invFun v := (v.1, v.2.1 - k, v.2.2)
  left_inv := by rintro ⟨p, x, y⟩; simp
  right_inv := by rintro ⟨p, x, y⟩; simp

omit [DecidableRel G.Adj] in
private theorem shiftX_adj (laws : NeighborLaws G) (k : ℤ) (v w : Vertex) :
    G.Adj (shiftX k v) (shiftX k w) ↔ G.Adj v w := by
  obtain ⟨p, x, y⟩ := v
  obtain ⟨q, u, z⟩ := w
  cases p <;> cases q
  · constructor <;> intro h <;> exact (laws.opposite h rfl).elim
  · change G.Adj (A (x + k) y) (B (u + k) z) ↔ G.Adj (A x y) (B u z)
    rw [laws.fromA, laws.fromA]
    omega
  · rw [G.adj_comm (v := _), G.adj_comm (v := (false, u, z))]
    change G.Adj (A (u + k) z) (B (x + k) y) ↔ G.Adj (A u z) (B x y)
    rw [laws.fromA, laws.fromA]
    omega
  · constructor <;> intro h <;> exact (laws.opposite h rfl).elim

private theorem shiftX_domain {P k d : ℕ} (hd : d ≤ P) (v : Vertex) :
    shiftX k v ∈ omegaDomain (k + P) d ∧ (k : ℤ) ≤ (shiftX k v).2.1 ↔
      v ∈ omegaDomain P d := by
  unfold omegaDomain
  simp only [mem_domain]
  rcases v with ⟨p, x, y⟩
  cases p <;> simp [shiftX, heightSum, g, part] <;> omega

private theorem left_domain {P k d e : ℕ} (hd : d ≤ P) (he : e ≤ P) {v : Vertex}
    (hv : v.2.1 < k) : v ∈ omegaDomain (k + P) d ↔ v ∈ omegaDomain (k + P) e := by
  unfold omegaDomain
  simp only [mem_domain]
  rcases v with ⟨p, x, y⟩
  cases p <;> simp [heightSum, g, part] at * <;> omega

omit [DecidableRel G.Adj] in
private theorem strip_crossing (laws : NeighborLaws G) {k : ℕ} {v w : Vertex}
    (right : (k : ℤ) ≤ v.2.1) (left : w.2.1 < k) (adj : G.Adj v w) :
    v = A k v.2.2 ∧ w = B ((k : ℤ) - 1) v.2.2 := by
  rcases v with ⟨p, x, y⟩
  cases p
  · change G.Adj (A x y) w at adj
    rcases (neighbors_A laws x y w).mp adj with rfl | rfl | rfl <;>
      simp [A, B] at * <;> omega
  · change G.Adj (B x y) w at adj
    rcases (neighbors_B laws x y w).mp adj with rfl | rfl | rfl <;>
      simp [A, B] at * <;> omega

private theorem strip_axis_mem {P k d y : ℕ} (hy : y < P) (hd : d ≤ P) :
    A k y ∈ omegaDomain (k + P) d := by
  apply mem_domain.mpr
  dsimp [A, heightSum, g, part]
  omega

private theorem strip_bits {b k y : ℕ} (divides : 2 ^ b ∣ k) (hy : y < 2 ^ b) :
    k &&& y = 0 := by
  have residue : k % 2 ^ b = 0 := Nat.mod_eq_zero_of_dvd divides
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.zero_testBit]
  by_cases hi : i < b
  · have hb : k.testBit i = false := by
      simpa [Nat.testBit_mod_two_pow, hi] using congrArg (fun n : ℕ => n.testBit i) residue
    simp [hb]
  · have hp : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    simp [Nat.testBit_lt_two_pow (hy.trans_le hp)]

private theorem strip_pred_bits {b k y : ℕ} (hk : 0 < k) (divides : 2 ^ b ∣ k)
    (hy : y < 2 ^ b) : (k - 1) &&& y = y := by
  have residue : (k - 1) % 2 ^ b = 2 ^ b - 1 := by
    obtain ⟨q, rfl⟩ := divides
    cases q with
    | zero => simp at hk
    | succ q =>
      rw [Nat.mul_succ, show 2 ^ b * q + 2 ^ b - 1 = 2 ^ b * q + (2 ^ b - 1) by omega,
        Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  by_cases hi : i < b
  · have hb : (k - 1).testBit i = true := by
      have hb' := congrArg (fun n : ℕ => n.testBit i) residue
      have hp : 0 < 2 ^ b := Nat.two_pow_pos b
      simpa [Nat.testBit_mod_two_pow, hi, Nat.testBit_two_pow_sub_succ hp] using hb'
    simp [hb]
  · have hp : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    simp [Nat.testBit_lt_two_pow (hy.trans_le hp)]

private theorem strip_axis_birth (first : EarliestBirthIff G) {b k d y : ℕ}
    (divides : 2 ^ b ∣ k) (hy : y < 2 ^ b) (hd : d ≤ 2 ^ b) :
    Born G (omegaDomain (k + 2 ^ b) d) (A 0 0) (2 * (k + y)) (A k y) := by
  have h := (first (k + 2 ^ b) d (by have := Nat.two_pow_pos b; omega) (by omega)
    _ (strip_axis_mem hy hd)).mpr
  have ht : earliest (A k y) = 2 * (k + y) := by simp [earliest, g, A, part]; omega
  rw [← ht]
  apply h
  simpa [A] using strip_bits divides hy

/-- A sender from the left cannot reach an intact site on the right after the seed tick. -/
private theorem strip_no_external_sender (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b k d t : ℕ} (hk : 0 < k) (divides : 2 ^ b ∣ k) (hd : d ≤ 2 ^ b)
    (ht : 2 * k ≤ t) {v w : Vertex} (hv : v ∈ omegaDomain (k + 2 ^ b) d)
    (right : (k : ℤ) ≤ v.2.1) (left : w.2.1 < k) (adj : G.Adj v w)
    (intact : Intact G (omegaDomain (k + 2 ^ b) d) (A 0 0) t v) :
    ¬ Born G (omegaDomain (k + 2 ^ b) d) (A 0 0) t w := by
  intro born
  obtain ⟨rfl', hw⟩ := strip_crossing laws right left adj
  let y := v.2.2.toNat
  have hycast : (y : ℤ) = v.2.2 := Int.toNat_of_nonneg (mem_domain.mp hv).2.1
  rw [← hycast] at rfl' hw
  have hy : y < 2 ^ b := by
    have hsum := (mem_domain.mp hv).2.2.1
    rw [rfl'] at hsum
    change (k : ℤ) + (y : ℤ) < ((k + 2 ^ b : ℕ) : ℤ) at hsum
    exact Nat.lt_of_add_lt_add_left (by exact_mod_cast hsum)
  have leftTime : earliest (B ((k : ℤ) - 1) y) = 2 * (k + y) - 1 := by
    simp [earliest, g, B, part]
    omega
  have hret := (touch_retained_and_positive born).1
  rw [hw] at born hret
  have leftBound := earliest_bound laws born
  rw [leftTime] at leftBound
  rw [rfl'] at intact
  have before : t < 2 * (k + y) := by
    by_contra! after
    exact intact_iff_no_touch.mp intact _ after _ (strip_axis_birth first divides hy hd)
  have timeEq : t = 2 * (k + y) - 1 := by omega
  have yPos : y ≠ 0 := by intro eq; omega
  have bitEq := (first (k + 2 ^ b) d (by omega) (by omega) _ hret).mp (by
    rwa [leftTime, ← timeEq])
  have cast : ((k : ℤ) - 1).toNat = k - 1 := by omega
  apply yPos
  simpa [B, cast, strip_pred_bits hk divides hy] using bitEq

/-- The complete tick at the translated seed time. -/
private theorem strip_initial_state (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b k d : ℕ} (divides : 2 ^ b ∣ k) (hd : d ≤ 2 ^ b) (v : Vertex)
    (hv : v ∈ omegaDomain (2 ^ b) d) :
    state G (omegaDomain (k + 2 ^ b) d) (A 0 0) (2 * k) (shiftX k v) =
      (state G (omegaDomain (2 ^ b) d) (A 0 0) 0 v).map
        (fun data => (2 * k + data.1, data.2)) := by
  by_cases seed : v = A 0 0
  · subst v
    have born := strip_axis_birth first divides (y := 0) (Nat.two_pow_pos b) hd
    have seedState := (touch_zero_iff.mpr ⟨hv, rfl, rfl⟩ :
      Touch G (omegaDomain (2 ^ b) d) (A 0 0) 0 (A 0 0) 1)
    change state G _ _ _ _ = some (0, 1) at seedState
    rw [seedState]
    simpa [Born, Touch, shiftX, A] using born
  · have hnone : Intact G (omegaDomain (2 ^ b) d) (A 0 0) 0 v := by
      simp [Intact, state, seed]
    change state G _ _ _ _ = none at hnone
    rw [hnone]
    apply intact_iff_no_touch.mpr
    intro s hs μ event
    have limit := earliest_bound laws event
    obtain ⟨hx, hy, _, _⟩ := mem_domain.mp hv
    rcases v with ⟨p, x, y⟩
    cases p <;> simp [shiftX, earliest, g, part, A] at * <;> omega

end

section

/-! First-touch evolution in the translated strip. -/

variable {G : SimpleGraph Vertex} [DecidableRel G.Adj]

private theorem next_state (D : Finset Vertex) (t : ℕ) (v : Vertex) :
    state G D (A 0 0) (t + 1) v =
      (state G D (A 0 0) t v).or
        (if v ∈ D ∧ (senders G D (A 0 0) t v).card ≠ 0
          then some (t + 1, (senders G D (A 0 0) t v).card) else none) := by
  cases h : state G D (A 0 0) t v with
  | some data => simp [state, h]
  | none =>
    by_cases hv : v ∈ D <;> simp [state, h, hv, senders]

private theorem born_of_shifted_state {D E : Finset Vertex} {t delay : ℕ} {v w : Vertex}
    (eq : state G E (A 0 0) (delay + t) w =
      (state G D (A 0 0) t v).map (fun data => (delay + data.1, data.2))) :
    Born G E (A 0 0) (delay + t) w ↔ Born G D (A 0 0) t v := by
  change state G E (A 0 0) (delay + t) w = some (delay + t, 1) ↔
    state G D (A 0 0) t v = some (t, 1)
  rw [eq]
  cases state G D (A 0 0) t v with
  | none => simp
  | some data => rcases data with ⟨r, μ⟩; simp

/-- The translated right strip has no first touches before its translated seed. -/
private theorem strip_no_early_touch (laws : NeighborLaws G) {a d k t μ : ℕ} {v : Vertex}
    (right : (k : ℤ) ≤ v.2.1) (ht : t < 2 * k) :
    ¬ Touch G (omegaDomain a d) (A 0 0) t v μ := by
  intro event
  have hy := (mem_domain.mp (touch_retained_and_positive event).1).2.1
  have lower := earliest_bound laws event
  rcases v with ⟨p, x, y⟩
  cases p <;> simp [earliest, g, part] at * <;> omega

/-- Compare the full stored first-touch data, with time and x translated explicitly. -/
private theorem strip_state_translate (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b k d : ℕ} (divides : 2 ^ b ∣ k) (hd : d ≤ 2 ^ b)
    (t : ℕ) (v : Vertex) (hv : v ∈ omegaDomain (2 ^ b) d) :
    state G (omegaDomain (k + 2 ^ b) d) (A 0 0) (2 * k + t) (shiftX k v) =
      (state G (omegaDomain (2 ^ b) d) (A 0 0) t v).map
        (fun data => (2 * k + data.1, data.2)) := by
  induction t generalizing v with
  | zero => simpa using strip_initial_state laws first divides hd v hv
  | succ t ih =>
    let D := omegaDomain (2 ^ b) d
    let E := omegaDomain (k + 2 ^ b) d
    let delay := 2 * k
    let f := shiftX (k : ℤ)
    change state G E (A 0 0) (delay + t + 1) (f v) =
      (state G D (A 0 0) (t + 1) v).map (fun data => (delay + data.1, data.2))
    obtain ⟨hfv, right⟩ := (shiftX_domain (k := k) hd v).mpr hv
    have hvD : v ∈ D := hv
    have hvE : f v ∈ E := hfv
    have previous := ih v hv
    change state G E (A 0 0) (delay + t) (f v) =
      (state G D (A 0 0) t v).map (fun data => (delay + data.1, data.2)) at previous
    cases small : state G D (A 0 0) t v with
    | some data =>
      have large : state G E (A 0 0) (delay + t) (f v) =
          some (delay + data.1, data.2) := by rw [previous, small]; rfl
      rw [next_state, next_state, small, large]
      rfl
    | none =>
      have large : state G E (A 0 0) (delay + t) (f v) = none := by
        rw [previous, small]; rfl
      have sameSenders :
          (senders G D (A 0 0) t v).map f.toEmbedding =
            senders G E (A 0 0) (delay + t) (f v) := by
        ext w
        rw [Finset.mem_map, mem_senders]
        constructor
        · rintro ⟨u, hu, rfl⟩
          obtain ⟨hu, adj, born⟩ := mem_senders.mp hu
          exact ⟨((shiftX_domain hd u).mpr hu).1, (shiftX_adj laws _ _ _).mpr adj,
            (born_of_shifted_state (ih u hu)).mpr born⟩
        · rintro ⟨hw, adj, born⟩
          have hRight : (k : ℤ) ≤ w.2.1 := by
            by_contra! left
            have hk : 0 < k := by
              have hx := (mem_domain.mp hw).1
              omega
            exact strip_no_external_sender laws first hk divides hd (by omega : delay ≤ delay + t)
              hfv right left adj large born
          refine ⟨f.symm w, ?_, f.apply_symm_apply w⟩
          have hu : f.symm w ∈ D :=
            (shiftX_domain (k := k) hd (f.symm w)).mp (by
              change f (f.symm w) ∈ E ∧ (k : ℤ) ≤ (f (f.symm w)).2.1
              rw [f.apply_symm_apply]
              exact ⟨hw, hRight⟩)
          have adj' : G.Adj (f v) (f (f.symm w)) := by rwa [f.apply_symm_apply]
          have born' : Born G E (A 0 0) (delay + t) (f (f.symm w)) := by
            rwa [f.apply_symm_apply]
          exact mem_senders.mpr ⟨hu, (shiftX_adj laws _ _ _).mp adj',
            (born_of_shifted_state (ih _ hu)).mp born'⟩
      have cards := congrArg Finset.card sameSenders
      rw [Finset.card_map] at cards
      rw [next_state, next_state, small, large, ← cards]
      simp only [Option.none_or, hvD, hvE, true_and]
      split <;> rfl

private theorem strip_born_translate (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b k d : ℕ} (divides : 2 ^ b ∣ k) (hd : d ≤ 2 ^ b)
    (t : ℕ) (v : Vertex) (hv : v ∈ omegaDomain (2 ^ b) d) :
    Born G (omegaDomain (k + 2 ^ b) d) (A 0 0) (2 * k + t) (shiftX k v) ↔
      Born G (omegaDomain (2 ^ b) d) (A 0 0) t v :=
  born_of_shifted_state (strip_state_translate laws first divides hd t v hv)

end

section

/-! First-touch evolution to the left of the strip. -/

variable {G : SimpleGraph Vertex} [DecidableRel G.Adj]

private theorem left_boundary_birth (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b k d e t : ℕ} (divides : 2 ^ b ∣ k) (hd : d ≤ 2 ^ b) (he : e ≤ 2 ^ b)
    {v w : Vertex} (left : v.2.1 < k) (right : (k : ℤ) ≤ w.2.1) (adj : G.Adj v w) :
    Born G (omegaDomain (k + 2 ^ b) d) (A 0 0) t w ↔
      Born G (omegaDomain (k + 2 ^ b) e) (A 0 0) t w := by
  have go (d₁ d₂ : ℕ) (h₁ : d₁ ≤ 2 ^ b) (h₂ : d₂ ≤ 2 ^ b)
      (birth : Born G (omegaDomain (k + 2 ^ b) d₁) (A 0 0) t w) :
      Born G (omegaDomain (k + 2 ^ b) d₂) (A 0 0) t w := by
    have eq := (strip_crossing laws right left ((G.adj_comm v w).mp adj)).1
    obtain ⟨_, hy, sum, _⟩ := mem_domain.mp (touch_retained_and_positive birth).1
    let y := w.2.2.toNat
    have hycast : (y : ℤ) = w.2.2 := Int.toNat_of_nonneg hy
    rw [← hycast] at eq
    rw [eq] at sum birth ⊢
    change (k : ℤ) + (y : ℤ) < ((k + 2 ^ b : ℕ) : ℤ) at sum
    have ySmall : y < 2 ^ b := Nat.lt_of_add_lt_add_left (by exact_mod_cast sum)
    have birth₁ := strip_axis_birth first divides ySmall h₁
    have birth₂ := strip_axis_birth first divides ySmall h₂
    rwa [(touch_unique birth birth₁).1]
  exact ⟨go d e hd he, go e d he hd⟩

/-- On the left of the strip, all stored first-touch data are independent of the cut. -/
private theorem left_state_eq (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b k d e : ℕ} (divides : 2 ^ b ∣ k) (hd : d ≤ 2 ^ b) (he : e ≤ 2 ^ b)
    (t : ℕ) (v : Vertex) (left : v.2.1 < k) :
    state G (omegaDomain (k + 2 ^ b) d) (A 0 0) t v =
      state G (omegaDomain (k + 2 ^ b) e) (A 0 0) t v := by
  let D := omegaDomain (k + 2 ^ b) d
  let E := omegaDomain (k + 2 ^ b) e
  change state G D (A 0 0) t v = state G E (A 0 0) t v
  have mem : ∀ v : Vertex, v.2.1 < k → (v ∈ D ↔ v ∈ E) := fun _ h =>
    left_domain hd he h
  induction t generalizing v with
  | zero => simp only [state, mem v left]
  | succ t ih =>
    have sendersEq : senders G D (A 0 0) t v = senders G E (A 0 0) t v := by
      ext w
      simp only [mem_senders]
      by_cases adj : G.Adj v w
      · have born : Born G D (A 0 0) t w ↔ Born G E (A 0 0) t w := by
          by_cases hw : w.2.1 < k
          · change state G D (A 0 0) t w = some (t, 1) ↔
              state G E (A 0 0) t w = some (t, 1)
            rw [ih w hw]
          · exact left_boundary_birth laws first divides hd he left (le_of_not_gt hw) adj
        constructor
        · rintro ⟨_, _, birth⟩
          have birth' := born.mp birth
          exact ⟨(touch_retained_and_positive birth').1, adj, birth'⟩
        · rintro ⟨_, _, birth⟩
          have birth' := born.mpr birth
          exact ⟨(touch_retained_and_positive birth').1, adj, birth'⟩
      · simp [adj]
    have prior := ih v left
    change sendingNeighbors G D t (state G D (A 0 0) t) v =
      sendingNeighbors G E t (state G E (A 0 0) t) v at sendersEq
    simp only [state, prior, mem v left, sendersEq]

end

section

/-! Copy identity for adjacent cuts. -/

variable {G : SimpleGraph Vertex} [DecidableRel G.Adj]

private theorem weight_zero_of_no_birth {D : Finset Vertex} {t : ℕ} {v : Vertex}
    (none : ¬ Born G D (A 0 0) t v) : birthWeight G D t v = 0 := by
  change state G D (A 0 0) t v ≠ some (t, 1) at none
  simp [birthWeight, none]

private theorem strip_weight_translate (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b k d : ℕ} (divides : 2 ^ b ∣ k) (hd : d ≤ 2 ^ b)
    (t : ℕ) (v : Vertex) (hx : 0 ≤ v.2.1) :
    birthWeight G (omegaDomain (k + 2 ^ b) d) (2 * k + t) (shiftX k v) =
      birthWeight G (omegaDomain (2 ^ b) d) t v := by
  by_cases hv : v ∈ omegaDomain (2 ^ b) d
  · have eq := strip_born_translate laws first divides hd t v hv
    change state G _ _ _ _ = some (_, 1) ↔ state G _ _ _ _ = some (_, 1) at eq
    simp only [birthWeight, eq]
  · have right : (k : ℤ) ≤ (shiftX k v).2.1 := by
      change (k : ℤ) ≤ v.2.1 + k
      omega
    rw [weight_zero_of_no_birth, weight_zero_of_no_birth]
    · exact fun h => hv (touch_retained_and_positive h).1
    · exact fun h => hv ((shiftX_domain hd v).mp ⟨(touch_retained_and_positive h).1, right⟩)

private theorem left_signed_zero (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b k c : ℕ} (divides : 2 ^ b ∣ k) (hc : c + 1 ≤ 2 ^ b)
    (t : ℕ) (v : Vertex) (left : v.2.1 < k) :
    signedWeight G (k + 2 ^ b) c t v = 0 := by
  unfold signedWeight birthWeight
  rw [left_state_eq laws first divides (by omega : c ≤ 2 ^ b) hc t v left, sub_self]

/-- The adjacent-cut identity at every positive integral multiple of the dyadic copy size. -/
theorem adjacent_copy_of_earliest (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b a c : ℕ} (positive : 0 < a) (divides : 2 ^ b ∣ a) (hc : c + 1 ≤ 2 ^ b) :
    delta G a c = X ^ (2 * (a - 2 ^ b)) * delta G (2 ^ b) c := by
  let P := 2 ^ b
  let k := a - P
  have hPa : P ≤ a := Nat.le_of_dvd positive divides
  have ha : k + P = a := by dsimp [k]; omega
  have hk : 2 ^ b ∣ k := Nat.dvd_sub divides (dvd_refl _)
  change delta G a c = X ^ (2 * k) * delta G P c
  rw [← ha]
  ext t
  rw [coeff_X_pow_mul']
  by_cases time : 2 * k ≤ t
  · simp only [time, ite_true]
    let D := omegaDomain P c
    let E := omegaDomain (k + P) c
    let f := shiftX (k : ℤ)
    let right (v : Vertex) : Prop := (k : ℤ) ≤ v.2.1
    have mapped : D.map f.toEmbedding = E.filter right := by
      ext w
      rw [Finset.mem_map, Finset.mem_filter]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact (shiftX_domain (by omega : c ≤ P) v).mpr hv
      · intro hw
        refine ⟨f.symm w, ?_, f.apply_symm_apply w⟩
        apply (shiftX_domain (k := k) (by omega : c ≤ P) _).mp
        change f (f.symm w) ∈ E ∧ right (f (f.symm w))
        rwa [f.apply_symm_apply]
    rw [coeff_delta_on (fun _ h => h) t, coeff_delta_on (fun _ h => h) (t - 2 * k)]
    change (∑ v ∈ E, signedWeight G (k + P) c t v) = ∑ v ∈ D, signedWeight G P c (t - 2 * k) v
    calc
      (∑ v ∈ E, signedWeight G (k + P) c t v) =
          ∑ v ∈ E.filter right, signedWeight G (k + P) c t v := by
            symm
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro v hv outside
            have left : v.2.1 < k := by
              by_contra! hr
              exact outside (Finset.mem_filter.mpr ⟨hv, hr⟩)
            exact left_signed_zero laws first hk hc t v left
      _ = ∑ v ∈ D, signedWeight G P c (t - 2 * k) v := by
        rw [← mapped, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro v hv
        have hx := (mem_domain.mp hv).1
        have lo := strip_weight_translate laws first hk (by omega : c ≤ P) (t - 2 * k) v hx
        have hi := strip_weight_translate laws first hk hc (t - 2 * k) v hx
        rw [show 2 * k + (t - 2 * k) = t by omega] at lo hi
        change signedWeight G (k + P) c t (f v) = _
        unfold signedWeight
        rw [lo, hi]
  · simp only [time, ite_false]
    rw [coeff_delta_on (fun _ h => h) t]
    apply Finset.sum_eq_zero
    intro v _
    by_cases left : v.2.1 < k
    · exact left_signed_zero laws first hk hc t v left
    · have noBirth (d : ℕ) : ¬ Born G (omegaDomain (k + P) d) (A 0 0) t v :=
        strip_no_early_touch laws (le_of_not_gt left) (by omega)
      simp only [signedWeight, weight_zero_of_no_birth (noBirth c),
        weight_zero_of_no_birth (noBirth (c + 1)), sub_self]

end

section

/-! Signed support at and after the cut layer. -/

variable {G : SimpleGraph Vertex} [DecidableRel G.Adj]

private def layerTime (a d : ℕ) : ℕ := 2 * a - d - 1

/-- On a layer with g = τ - i, this is τ + i + y. -/
private def cutHorizon (τ : ℕ) (v : Vertex) : ℕ := (2 * (τ : ℤ) - (g v - v.2.2)).toNat

omit [DecidableRel G.Adj] in
private theorem cutHorizon_step (laws : NeighborLaws G) (τ : ℕ) {v w : Vertex}
    (adj : G.Adj v w) : cutHorizon τ v ≤ cutHorizon τ w + 1 := by
  obtain ⟨p, x, y⟩ := v
  cases p
  · change G.Adj (A x y) w at adj
    rcases (neighbors_A laws x y w).mp adj with rfl | rfl | rfl <;>
      dsimp [cutHorizon, g, A, B, part] <;> omega
  · change G.Adj (B x y) w at adj
    rcases (neighbors_B laws x y w).mp adj with rfl | rfl | rfl <;>
      dsimp [cutHorizon, g, A, B, part] <;> omega

private theorem layer_of_removed {a d : ℕ} (hd : d < a) {v : Vertex}
    (outer : v ∈ omegaDomain a d) (outside : v ∉ omegaDomain a (d + 1)) :
    g v = (layerTime a d : ℤ) := by
  unfold omegaDomain at outer outside
  obtain ⟨hx, hy, sum, hg⟩ := mem_domain.mp outer
  have lower : ((2 * a - (d + 1) : ℕ) : ℤ) ≤ g v := by
    by_contra! below
    exact outside (mem_domain.mpr ⟨hx, hy, sum, below⟩)
  unfold layerTime
  omega

/-- The strict first-touch horizon for adjacent g cuts (the support assertion of Lemma 36). -/
private theorem adjacent_cut_horizon (laws : NeighborLaws G) {a d : ℕ} (hd : d < a) (t : ℕ) :
    (∀ v ∈ omegaDomain a (d + 1), t < cutHorizon (layerTime a d) v → ∀ μ, 0 < μ →
      (Touch G (omegaDomain a (d + 1)) (A 0 0) t v μ ↔
        Touch G (omegaDomain a d) (A 0 0) t v μ)) ∧
    (∀ v ∈ omegaDomain a d, v ∉ omegaDomain a (d + 1) →
      t < cutHorizon (layerTime a d) v → ¬ Born G (omegaDomain a d) (A 0 0) t v) := by
  have sub : omegaDomain a (d + 1) ⊆ omegaDomain a d :=
    domain_cut_mono (by omega)
  have seed : A 0 0 ∈ omegaDomain a (d + 1) := seed_mem (by omega) (by omega)
  apply strict_horizon (cutHorizon (layerTime a d)) sub seed
    (fun {_ _} adj => cutHorizon_step laws _ adj)
  intro v outer outside _ s short born
  have hg := layer_of_removed hd outer outside
  have low := earliest_bound laws born
  unfold cutHorizon at short
  unfold earliest at low
  rw [hg] at short low
  omega

private theorem signed_zero_before_horizon (laws : NeighborLaws G) {a d t : ℕ} (hd : d < a)
    {v : Vertex} (short : t < cutHorizon (layerTime a d) v) :
    signedWeight G a d t v = 0 := by
  have comparison := adjacent_cut_horizon laws hd t
  have equiv : Born G (omegaDomain a (d + 1)) (A 0 0) t v ↔
      Born G (omegaDomain a d) (A 0 0) t v := by
    by_cases shared : v ∈ omegaDomain a (d + 1)
    · exact comparison.1 v shared short 1 (by decide)
    · have noneSmall : ¬ Born G (omegaDomain a (d + 1)) (A 0 0) t v := fun birth =>
        shared (touch_retained_and_positive birth).1
      have noneLarge : ¬ Born G (omegaDomain a d) (A 0 0) t v := fun birth =>
        comparison.2 v (touch_retained_and_positive birth).1 shared short birth
      exact ⟨fun birth => (noneSmall birth).elim, fun birth => (noneLarge birth).elim⟩
  change state G _ _ _ _ = some (_, 1) ↔ state G _ _ _ _ = some (_, 1) at equiv
  simp only [signedWeight, birthWeight, ← equiv, sub_self]

/-- The exact signed-support interface used by the independent prefix argument. -/
theorem signedSupport_of_neighborLaws (laws : NeighborLaws G) : SignedSupport G := by
  intro a d hd j v active
  change signedWeight G a d (layerTime a d + j) v ≠ 0 at active
  have retained : v ∈ omegaDomain a d := by
    by_contra outside
    have noOuter : ¬ Born G (omegaDomain a d) (A 0 0) (layerTime a d + j) v :=
      fun birth => outside (touch_retained_and_positive birth).1
    have noInner : ¬ Born G (omegaDomain a (d + 1)) (A 0 0) (layerTime a d + j) v :=
      fun birth => outside (domain_cut_mono (by omega) (touch_retained_and_positive birth).1)
    change state G _ _ _ _ ≠ some (_, 1) at noOuter noInner
    exact active (by simp [signedWeight, birthWeight, noOuter, noInner])
  have gUpper := (mem_domain.mp retained).2.2.2
  change g v < ((2 * a - d : ℕ) : ℤ) at gUpper
  have yNonneg := (mem_domain.mp retained).2.1
  have timeLower : cutHorizon (layerTime a d) v ≤ layerTime a d + j := by
    by_contra! short
    exact active (signed_zero_before_horizon laws hd short)
  refine ⟨retained, ((layerTime a d : ℤ) - g v).toNat, ?_, ?_⟩
  · unfold layerTime
    omega
  · unfold cutHorizon layerTime at timeLower
    unfold layerTime
    omega

private theorem coeff_delta_zero_before_layer (laws : NeighborLaws G) {a d t : ℕ}
    (hd : d < a) (ht : t < layerTime a d) : (delta G a d).coeff t = 0 := by
  rw [coeff_delta_on (fun _ h => h) t]
  apply Finset.sum_eq_zero
  intro v hv
  apply signed_zero_before_horizon laws hd
  obtain ⟨_, hy, _, hg⟩ := mem_domain.mp hv
  change g v < ((2 * a - d : ℕ) : ℤ) at hg
  unfold cutHorizon layerTime at *
  omega

end

section

/-! Removal of the delay and independence of dyadic enclosure. -/

variable {G : SimpleGraph Vertex} [DecidableRel G.Adj]

private noncomputable def removeDelay (p : ℤ[X]) : ℕ → ℤ[X]
  | 0 => p
  | n + 1 => (removeDelay p n).divX

private theorem coeff_removeDelay (p : ℤ[X]) (n j : ℕ) :
    (removeDelay p n).coeff j = p.coeff (n + j) := by
  induction n generalizing j with
  | zero => simp [removeDelay]
  | succ n ih => rw [removeDelay, coeff_divX, ih]; congr 1; omega

/-- The normalized polynomial at an enclosing height. Applications use `d < a`. -/
private noncomputable def kernelAt (G : SimpleGraph Vertex) [DecidableRel G.Adj] (a d : ℕ) : ℤ[X] :=
  removeDelay (delta G a d) (layerTime a d)

private theorem coeff_kernelAt (a d j : ℕ) :
    (kernelAt G a d).coeff j = (delta G a d).coeff (2 * a - d - 1 + j) :=
  coeff_removeDelay _ _ _

/-- Equation (17) as an equality in integer polynomials, with the delay restored. -/
private theorem delta_eq_delayed_kernelAt (laws : NeighborLaws G) {a d : ℕ} (hd : d < a) :
    delta G a d = X ^ layerTime a d * kernelAt G a d := by
  ext t
  rw [coeff_X_pow_mul']
  by_cases ht : layerTime a d ≤ t
  · simp only [ht, ite_true, coeff_kernelAt]
    unfold layerTime at ht ⊢
    congr 1
    omega
  · simp only [ht, ite_false]
    exact coeff_delta_zero_before_layer laws hd (by omega)

private theorem exists_dyadic_enclosure (d : ℕ) : ∃ b : ℕ, d < 2 ^ b :=
  ⟨d, Nat.lt_two_pow_self⟩

private def leastEnclosureExponent (d : ℕ) : ℕ := Nat.find (exists_dyadic_enclosure d)

private theorem leastEnclosure_spec (d : ℕ) :
    d < 2 ^ leastEnclosureExponent d ∧
      ∀ b : ℕ, d < 2 ^ b → leastEnclosureExponent d ≤ b :=
  ⟨Nat.find_spec (exists_dyadic_enclosure d), fun _ => Nat.find_min' (exists_dyadic_enclosure d)⟩

/-- The kernel in (17), defined using the least dyadic height with `d < a`. -/
private noncomputable def kernel (G : SimpleGraph Vertex) [DecidableRel G.Adj] (d : ℕ) : ℤ[X] :=
  kernelAt G (2 ^ leastEnclosureExponent d) d

/-- Lemma 17's kernel independence, even for a positive multiple of an eligible copy height. -/
private theorem kernelAt_eq_of_dvd (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b a d : ℕ} (ha : 0 < a) (divides : 2 ^ b ∣ a) (hd : d < 2 ^ b) :
    kernelAt G a d = kernelAt G (2 ^ b) d := by
  let P := 2 ^ b
  have le : P ≤ a := Nat.le_of_dvd ha divides
  ext j
  rw [coeff_kernelAt, coeff_kernelAt,
    adjacent_copy_of_earliest laws first ha divides (by omega : d + 1 ≤ P)]
  have delay : 2 * a - d - 1 + j = (2 * P - d - 1 + j) + 2 * (a - P) := by omega
  rw [delay]
  exact coeff_X_pow_mul _ _ _

private theorem kernel_eq_at_dyadic (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b d : ℕ} (hd : d < 2 ^ b) : kernel G d = kernelAt G (2 ^ b) d := by
  have spec := leastEnclosure_spec d
  exact (kernelAt_eq_of_dvd laws first (Nat.two_pow_pos b)
    (Nat.pow_dvd_pow 2 (spec.2 b hd)) spec.1).symm

noncomputable def kernelEntry (G : SimpleGraph Vertex) [DecidableRel G.Adj] (j d : ℕ) : ℤ :=
  (kernel G d).coeff j

/-- Equation (17) gives the readout at every eligible dyadic height. -/
theorem kernelEntry_eq_coeff (laws : NeighborLaws G) (first : EarliestBirthIff G)
    {b d : ℕ} (j : ℕ) (hd : d < 2 ^ b) :
    kernelEntry G j d = (delta G (2 ^ b) d).coeff (2 * 2 ^ b - d - 1 + j) := by
  rw [kernelEntry, kernel_eq_at_dyadic laws first hd]
  have eq := congrArg (fun p : ℤ[X] => p.coeff (j + layerTime (2 ^ b) d))
    (delta_eq_delayed_kernelAt laws hd)
  rw [coeff_X_pow_mul] at eq
  simpa [layerTime, Nat.add_comm] using eq.symm

/-- Coefficients of the V-toothpick kernel on the repository honeycomb. -/
noncomputable def birthKernelEntry (j d : ℕ) : ℤ :=
  @kernelEntry honeycombGraph repositoryAdjacency j d

end

end D5.S3.StatisticalMechanics.CellularAutomata.HoneycombBirthKernel
