/- GID: D5/S3/Combinatorics/Circle/MixedSuffixEnergy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/MixedSuffixEnergy
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic, mathlib/module/Mathlib.Order.Prod.Lex.Basic]
   utility: none
   digest: Physical mixed-suffix exchange with full-prefix legality, strict energy descent, and exact inventory. -/
module
public import D5.S3.Combinatorics.Circle.ExpandingSourcePath
public import Mathlib.Data.List.Perm.Basic
public import D5.S3.Combinatorics.Circle.ZeroSumSubsets

/-! Native source candidate. This file contains no minimizer or C3.1 completion
claim. No energy inequality, strip-legal replacement, partition, or availability
of a favorable path is assumed. Every occurrence is still an element of Fin k. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.MixedSuffixEnergy
open SourceWidth ExpandingSourcePath
open scoped BigOperators

def mass {α β : Type*} [AddMonoid β] (w : α → β) (L : List α) : β := (L.map w).sum

def remainingMass {k : ℕ} {β : Type*} [AddCommMonoid β]
    (w : Fin k → β) (L : List (Fin k)) : β := ∑ p ∈ L.toFinsetᶜ, w p

def largeWeight (k t : ℕ) (p : Fin k) : ℕ := if Large k t p then 1 else 0
def smallWeight (k t : ℕ) (p : Fin k) : ℕ := if Large k t p then 0 else 1
def energyWeight (k t : ℕ) (p : Fin k) : ℕ :=
  if Large k t p then 3 ^ (actualSource k t p).natAbs else 0

def largeUsed (k t : ℕ) (L : List (Fin k)) : ℕ := mass (largeWeight k t) L
def smallUsed (k t : ℕ) (L : List (Fin k)) : ℕ := mass (smallWeight k t) L
def G (k t : ℕ) (L : List (Fin k)) : ℕ := remainingMass (largeWeight k t) L
def H (k t : ℕ) (L : List (Fin k)) : ℕ := mass (energyWeight k t) L
def U {k : ℕ} (L : List (Fin k)) : ℕ := remainingMass (fun _ => (1 : ℕ)) L
def J (k t : ℕ) (L : List (Fin k)) : Lex (ℕ × Lex (ℕ × ℕ)) :=
  toLex (G k t L, toLex (H k t L, U L))

theorem orient_choose (z : ℤ) : orient (decide (z < 0)) z = |z| := by
  by_cases hz : z < 0
  · simp [orient, hz, abs_of_neg hz]
  · simp [orient, hz, abs_of_nonneg (show 0 ≤ z by omega)]

private theorem mass_congr {α β : Type*} [AddMonoid β]
    (L : List α) (v w : α → β) (h : ∀ p ∈ L, v p = w p) : mass v L = mass w L := by
  revert h
  induction L with
  | nil => intro _; rfl
  | cons p L ih =>
    intro h
    simp only [mass, List.map_cons, List.sum_cons]
    rw [h p (by simp)]
    exact congrArg (fun z => w p + z) (ih (fun q hq => h q (by simp [hq])))

theorem physical_balance {k : ℕ} {β : Type*} [AddCommMonoid β]
    (w : Fin k → β) (L : List (Fin k)) (hL : L.Nodup) :
    remainingMass w L + mass w L = ∑ p : Fin k, w p := by
  unfold remainingMass mass
  rw [← List.sum_toFinset w hL]
  exact Finset.sum_compl_add_sum L.toFinset w

theorem counts_partition {k : ℕ} (t : ℕ) (L : List (Fin k)) :
    largeUsed k t L + smallUsed k t L = L.length := by
  induction L with
  | nil => simp [largeUsed, smallUsed, mass]
  | cons p L ih =>
    have hp : largeWeight k t p + smallWeight k t p = 1 := by
      by_cases hp : Large k t p <;> simp [largeWeight, smallWeight, hp]
    simp only [largeUsed, smallUsed, mass, List.map_cons, List.sum_cons,
      List.length_cons] at ih ⊢
    omega

theorem strip_split {α : Type*} {f : α → ℤ} {C a : ℤ} (A B : List α)
    (h : InStrip f C a (A ++ B)) :
    InStrip f C a A ∧ InStrip f C (a + mass f A) B := by
  induction A generalizing a with
  | nil =>
    have h0 := inStrip_prefix h 0
    exact ⟨by simpa [InStrip] using h0, by simpa [mass] using h⟩
  | cons p A ih =>
    obtain ⟨hA, hB⟩ := ih h.2.2
    refine ⟨⟨h.1, h.2.1, hA⟩, ?_⟩
    simpa [mass, add_assoc] using hB

theorem strip_of_all_prefixes {α : Type*} {f : α → ℤ} {C a : ℤ}
    (L : List α)
    (h : ∀ n : ℕ, 0 ≤ a + mass f (L.take n) ∧ a + mass f (L.take n) ≤ C) :
    InStrip f C a L := by
  induction L generalizing a with
  | nil => simpa [mass, InStrip] using h 0
  | cons p L ih =>
    have h0 := h 0
    simp only [List.take_zero, mass, List.map_nil, List.sum_nil, add_zero] at h0
    refine ⟨h0.1, h0.2, ih ?_⟩
    intro n
    simpa [mass, List.take_succ_cons, add_assoc] using h (n + 1)

/-- Unusedness plus a consumed terminal label forces physical length < k.
Repeated numerical values and a short numerical orbit do not enter this argument. -/
private theorem physical_unused_path
    {k : ℕ} (hk : 0 < k) (p x : Fin k) (m : ℕ) (W : List (Fin k))
    (hx : phase hk p m = x) (hxW : x ∈ W)
    (hu : ∀ j < m, phase hk p j ∉ W) :
    m < k ∧ (path hk p m).Nodup ∧ List.Disjoint (path hk p m) W := by
  have hm : m < k := by
    by_contra h
    have hkm : k ≤ m := by omega
    have hj : m % k < m := lt_of_lt_of_le (Nat.mod_lt _ hk) hkm
    have he : phase hk p (m % k) = phase hk p m := by
      apply Fin.ext
      simp [phase, Nat.add_mod]
    have hbad := hu (m % k) hj
    rw [he, hx] at hbad
    exact hbad hxW
  have hnod : (path hk p m).Nodup := by
    apply List.Nodup.map_on (l := List.range m) ?_ (List.nodup_range (n := m))
    intro i hi j hj hij
    have he : Nat.ModEq k (p.val + i) (p.val + j) := congrArg Fin.val hij
    have hc : Nat.ModEq k i j := Nat.ModEq.add_left_cancel' p.val he
    have hi' : i < k := lt_trans (List.mem_range.mp hi) hm
    have hj' : j < k := lt_trans (List.mem_range.mp hj) hm
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] using hc
  refine ⟨hm, hnod, List.disjoint_left.mpr ?_⟩
  intro q hq hqW
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  exact hu j (List.mem_range.mp hj) hqW

/-- E_mix and its strict-G companion, for the identical explicit native word.
The suffix hypothesis is only its LARGE count. SMALL signs, numbers, and positions
are unrestricted. Equality is in subtraction-free Nat form before the corollaries.
The returned physical partitions and disjoint unions are conclusions. -/
theorem mixed_suffix_energy_exchange
    {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (p x : Fin k) (m : ℕ)
    (hm : 2 ≤ m) (heven : m % 2 = 0)
    (A B : List (Fin k))
    (hW : (A ++ x :: B).Nodup)
    (hlegal : InStrip (actualSource k t) (half k) 0 (A ++ x :: B))
    (hhit : phase (by omega) p m = x)
    (hunused : ∀ j < m, phase (by omega) p j ∉ A ++ x :: B)
    (hlarge : ∀ j < m, Large k t (phase (by omega) p j))
    (hexpanding : 0 < 3 * |actualSource k t p| - modulus k)
    (hsuffix : largeUsed k t B ≤ m - 1) :
    let W := A ++ x :: B
    let P := path (by omega) p m
    let V := A ++ P
    m < k ∧ P.Nodup ∧ List.Disjoint P W ∧ V.Nodup ∧
    InStrip (actualSource k t) (half k) 0 V ∧
    (∀ n : ℕ, 0 ≤ mass (actualSource k t) (V.take n) ∧
      mass (actualSource k t) (V.take n) ≤ half k) ∧
    V.toFinset = (W.toFinset \ insert x B.toFinset) ∪ P.toFinset ∧
    Disjoint (W.toFinset \ insert x B.toFinset) P.toFinset ∧
    V.toFinsetᶜ = (W.toFinsetᶜ \ P.toFinset) ∪ insert x B.toFinset ∧
    Disjoint (W.toFinsetᶜ \ P.toFinset) (insert x B.toFinset) ∧
    G k t V + m = G k t W + 1 + largeUsed k t B ∧
    U V + m = U W + 1 + B.length ∧
    H k t V < H k t W ∧
    remainingMass (actualSource k t) V = -mass (actualSource k t) V ∧
    (largeUsed k t B = m - 1 → G k t V = G k t W ∧
      U V = U W + smallUsed k t B) ∧
    (largeUsed k t B ≤ m - 2 → G k t V < G k t W) ∧
    J k t V < J k t W := by
  dsimp only
  let W := A ++ x :: B
  let P := path (by omega) p m
  let V := A ++ P
  let negative : Bool := decide (actualSource k t p < 0)
  have hk0 : 0 < k := by omega
  have hxW : x ∈ W := by simp [W]
  obtain ⟨hmk, hPnod, hPW⟩ := physical_unused_path hk0 p x m W hhit hxW hunused
  obtain ⟨hAnod, hBnod, hAB⟩ := List.nodup_append'.mp hW
  have hAP : List.Disjoint A P := by
    apply List.disjoint_left.mpr
    intro q hqA hqP
    exact List.disjoint_left.mp hPW hqP (by simp [W, hqA])
  have hVnod : V.Nodup := hAnod.append hPnod hAP
  have hPLarge : ∀ q ∈ P, Large k t q := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    exact hlarge j (List.mem_range.mp hj)
  have hexpanding' : 0 < 3 * orient negative (actualSource k t p) - modulus k := by
    simpa only [negative, orient_choose] using hexpanding
  have hprofile := expanding_path_estimates hk t p m hm heven negative hlarge hexpanding'
  dsimp only at hprofile
  rw [hhit] at hprofile
  obtain ⟨hxpos, hxLarge, hprefix, hgap, hgaplo, henergy⟩ := hprofile
  obtain ⟨hAlegal, htail⟩ := strip_split A (x :: B) hlegal
  let a := mass (actualSource k t) A
  have ha : 0 ≤ a ∧ a ≤ half k := by
    simpa only [zero_add] using And.intro htail.1 htail.2.1
  have hax : 0 ≤ a + actualSource k t x ∧ a + actualSource k t x ≤ half k := by
    have h := inStrip_prefix htail.2.2 0
    simpa [mass, a] using h
  have hPlegal : InStrip (actualSource k t) (half k) a P := by
    apply strip_of_all_prefixes
    intro n
    have h := hprefix n
    change 0 ≤ orient negative (mass (actualSource k t) (P.take n)) ∧
      orient negative (mass (actualSource k t) (P.take n)) ≤
        orient negative (actualSource k t x) at h
    by_cases hneg : negative = true
    · have h' : 0 ≤ -mass (actualSource k t) (P.take n) ∧
          -mass (actualSource k t) (P.take n) ≤ -actualSource k t x := by
        simpa [orient, hneg] using h
      constructor <;> linarith only [ha.1, ha.2, hax.1, hax.2, h'.1, h'.2]
    · have h' : 0 ≤ mass (actualSource k t) (P.take n) ∧
          mass (actualSource k t) (P.take n) ≤ actualSource k t x := by
        simpa [orient, hneg] using h
      constructor <;> linarith only [ha.1, ha.2, hax.1, hax.2, h'.1, h'.2]
  have hVlegal : InStrip (actualSource k t) (half k) 0 V := by
    apply inStrip_append hAlegal
    simpa [mass, a] using hPlegal
  have hVprefix : ∀ n : ℕ, 0 ≤ mass (actualSource k t) (V.take n) ∧
      mass (actualSource k t) (V.take n) ≤ half k := by
    intro n
    simpa [mass] using inStrip_prefix hVlegal n
  have hUsed : V.toFinset = (W.toFinset \ insert x B.toFinset) ∪ P.toFinset := by
    ext q
    have hAR : q ∈ A → q ∉ x :: B := fun hq => List.disjoint_left.mp hAB hq
    simp only [List.mem_cons] at hAR
    simp only [V, W, List.mem_toFinset, List.mem_append, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_insert, List.mem_cons]
    tauto
  have hUsedDis : Disjoint (W.toFinset \ insert x B.toFinset) P.toFinset := by
    apply Finset.disjoint_left.mpr
    intro q hq hqP
    exact List.disjoint_left.mp hPW (List.mem_toFinset.mp hqP)
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hq).1)
  have hUnused : V.toFinsetᶜ = (W.toFinsetᶜ \ P.toFinset) ∪ insert x B.toFinset := by
    ext q
    have hAR : q ∈ A → q ∉ x :: B := fun hq => List.disjoint_left.mp hAB hq
    have hPR : q ∈ P → q ∉ W := fun hq => List.disjoint_left.mp hPW hq
    simp only [W, List.mem_append, List.mem_cons] at hAR hPR
    simp only [V, W, Finset.mem_compl, List.mem_toFinset, List.mem_append,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, List.mem_cons]
    tauto
  have hUnusedDis : Disjoint (W.toFinsetᶜ \ P.toFinset) (insert x B.toFinset) := by
    apply Finset.disjoint_left.mpr
    intro q hq hqR
    have hqW : q ∈ W := by
      apply List.mem_append_right A
      exact List.mem_cons.mpr (by
        simpa only [Finset.mem_insert, List.mem_toFinset] using hqR)
    exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp hq).1) (List.mem_toFinset.mpr hqW)
  have hPcount : largeUsed k t P = m := by
    have h := mass_congr P (largeWeight k t) (fun _ => (1 : ℕ))
      (by intro q hq; simp [largeWeight, hPLarge q hq])
    simpa [largeUsed, mass, P, List.map_const'] using h
  have hCountsW : largeUsed k t W = largeUsed k t A + 1 + largeUsed k t B := by
    simp [W, largeUsed, mass, largeWeight, hxLarge, Nat.add_assoc]
  have hCountsV : largeUsed k t V = largeUsed k t A + m := by
    calc
      largeUsed k t V = largeUsed k t A + largeUsed k t P := by
        simp [V, largeUsed, mass]
      _ = largeUsed k t A + m := by rw [hPcount]
  have hG : G k t V + m = G k t W + 1 + largeUsed k t B := by
    have hw : G k t W + largeUsed k t W = ∑ q : Fin k, largeWeight k t q :=
      physical_balance (largeWeight k t) W hW
    have hv : G k t V + largeUsed k t V = ∑ q : Fin k, largeWeight k t q :=
      physical_balance (largeWeight k t) V hVnod
    omega
  have hU : U V + m = U W + 1 + B.length := by
    have hw : U W + W.length = k := by
      simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) W hW
    have hv : U V + V.length = k := by
      simpa [U, mass, List.map_const'] using physical_balance (fun _ : Fin k => (1 : ℕ)) V hVnod
    have hwlen : W.length = A.length + (1 + B.length) := by simp [W]; omega
    have hvlen : V.length = A.length + m := by simp [V, P]
    rw [hwlen] at hw
    rw [hvlen] at hv
    omega
  have hPenergy : H k t P = mass (fun q => (3 : ℕ) ^ (actualSource k t q).natAbs) P := by
    exact mass_congr P (energyWeight k t) _
      (by intro q hq; simp [energyWeight, hPLarge q hq])
  have hH : H k t V < H k t W := by
    have hv : H k t V = H k t A + H k t P := by simp [V, H, mass]
    have hw : H k t W = H k t A + (3 : ℕ) ^ (actualSource k t x).natAbs + H k t B := by
      simp [W, H, mass, energyWeight, hxLarge, Nat.add_assoc]
    change mass (fun q => (3 : ℕ) ^ (actualSource k t q).natAbs) P <
      (3 : ℕ) ^ (actualSource k t x).natAbs at henergy
    omega
  have hComplement : remainingMass (actualSource k t) V = -mass (actualSource k t) V := by
    have h := physical_balance (actualSource k t) V hVnod
    rw [(ZeroSumSubsets.source_cycle hk0 t).2.1] at h
    omega
  have hEqual : largeUsed k t B = m - 1 → G k t V = G k t W ∧
      U V = U W + smallUsed k t B := by
    intro he
    have hc := counts_partition t B
    omega
  have hLower : largeUsed k t B ≤ m - 2 → G k t V < G k t W := by
    intro he
    omega
  have hJ : J k t V < J k t W := by
    apply Prod.Lex.toLex_lt_toLex.mpr
    by_cases hg : G k t V < G k t W
    · exact Or.inl hg
    · refine Or.inr ⟨by omega, ?_⟩
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hH)
  exact ⟨hmk, hPnod, hPW, hVnod, hVlegal, hVprefix, hUsed, hUsedDis,
    hUnused, hUnusedDis, hG, hU, hH, hComplement, hEqual, hLower, hJ⟩

end D5.S3.Combinatorics.Circle.MixedSuffixEnergy
