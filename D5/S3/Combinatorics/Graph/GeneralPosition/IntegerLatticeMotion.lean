/- GID: D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer lattice distances and separated serialized robot translations. -/

import D5.S3.Combinatorics.Graph.WellCoveredPowerCliqueProduct
import D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Countable.Basic
import Mathlib.Data.Fintype.EquivFin

/-! The signed-unit graph, its metric, and separated coordinate configurations. -/

namespace D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion

open Finset

abbrev Vertex (k : ℕ) := Fin k → ℤ

/-- The integer lattice with one signed unit change on each edge. -/
def lattice (k : ℕ) : SimpleGraph (Vertex k) where
  Adj x y := ∃ j, (y j = x j + 1 ∨ y j = x j - 1) ∧ ∀ i, i ≠ j → y i = x i
  symm := ⟨by
    intro x y h
    obtain ⟨j, hj, he⟩ := h
    refine ⟨j, ?_, fun i hi => (he i hi).symm⟩
    rcases hj with hj | hj
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)⟩
  loopless := ⟨by
    intro x h
    obtain ⟨j, hj, _⟩ := h
    rcases hj with hj | hj <;> omega⟩

/-- Sum of coordinate distances; this is not the sup metric on a function space. -/
def l1 {k : ℕ} (x y : Vertex k) : ℕ := ∑ j, (x j - y j).natAbs

private theorem abs_triangle (a b c : ℤ) :
    (a - c).natAbs ≤ (a - b).natAbs + (b - c).natAbs := by
  have h := Int.natAbs_add_le (a - b) (b - c)
  simpa only [sub_add_sub_cancel] using h

private theorem abs_between (a b c : ℤ) :
    (a - b).natAbs + (b - c).natAbs = (a - c).natAbs ↔
      (a ≤ b ∧ b ≤ c) ∨ (c ≤ b ∧ b ≤ a) := by
  omega

private theorem l1_zero {k : ℕ} (x y : Vertex k) : l1 x y = 0 ↔ x = y := by
  simp only [l1, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    Int.natAbs_eq_zero, sub_eq_zero]
  exact ⟨fun h => funext h, fun h => by subst y; simp⟩

private theorem l1_edge {k : ℕ} (x y z : Vertex k) (h : (lattice k).Adj x y) :
    l1 x z ≤ l1 y z + 1 := by
  obtain ⟨j, hj, he⟩ := h
  have hsum : ∑ i ∈ Finset.univ.erase j, (x i - z i).natAbs =
      ∑ i ∈ Finset.univ.erase j, (y i - z i).natAbs := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i (Finset.mem_erase.mp hi).1]
  have hx := Finset.sum_erase_add Finset.univ (fun i => (x i - z i).natAbs) (Finset.mem_univ j)
  have hy := Finset.sum_erase_add Finset.univ (fun i => (y i - z i).natAbs) (Finset.mem_univ j)
  have hab : (x j - y j).natAbs = 1 := by rcases hj with hj | hj <;> omega
  have hb := abs_triangle (x j) (y j) (z j)
  unfold l1
  omega

private theorem l1_descent {k : ℕ} (x y : Vertex k) (h : l1 x y ≠ 0) :
    ∃ z, (lattice k).Adj x z ∧ l1 z y + 1 = l1 x y := by
  have hne : x ≠ y := by simpa [l1_zero] using h
  obtain ⟨j,hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.mp hne
  let a : ℤ := if x j < y j then x j + 1 else x j - 1
  let z : Vertex k := Function.update x j a
  have ha : a = x j + 1 ∨ a = x j - 1 := by unfold a; split_ifs <;> simp
  have he : ∀ i, i ≠ j → z i = x i := by intro i hi; simp [z, hi]
  have hzj : z j = a := by simp [z]
  refine ⟨z, ⟨j, by simpa [hzj] using ha, he⟩, ?_⟩
  have hsum : ∑ i ∈ Finset.univ.erase j, (z i - y i).natAbs =
      ∑ i ∈ Finset.univ.erase j, (x i - y i).natAbs := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i (Finset.mem_erase.mp hi).1]
  have hx := Finset.sum_erase_add Finset.univ (fun i => (x i - y i).natAbs) (Finset.mem_univ j)
  have hz := Finset.sum_erase_add Finset.univ (fun i => (z i - y i).natAbs) (Finset.mem_univ j)
  have hab : (z j - y j).natAbs + 1 = (x j - y j).natAbs := by
    rw [hzj]
    unfold a
    split_ifs <;> omega
  unfold l1
  omega

/-- Connectivity and the exact graph distance of the signed-unit lattice. -/
theorem lattice_distance (k : ℕ) :
    (lattice k).Connected ∧ ∀ x y, (lattice k).dist x y = l1 x y :=
  WellCoveredPowerCliqueProduct.distance_certificate (lattice k) l1
    l1_zero l1_edge l1_descent

/-- Coordinatewise order betweenness, with either orientation in each coordinate. -/
def Between {k : ℕ} (x y z : Vertex k) : Prop :=
  ∀ j, (x j ≤ y j ∧ y j ≤ z j) ∨ (z j ≤ y j ∧ y j ≤ x j)

/-- Coordinate betweenness is exactly shortest-path betweenness in the actual graph. -/
theorem between_iff_geodesic {k : ℕ} (x y z : Vertex k) :
    Between x y z ↔ CylinderSevenTen.OnGeodesic (lattice k) x y z := by
  unfold CylinderSevenTen.OnGeodesic
  simp only [(lattice_distance k).2]
  unfold Between l1
  rw [← Finset.sum_add_distrib]
  constructor
  · intro h
    apply Finset.sum_congr rfl
    intro i _
    exact (abs_between _ _ _).mpr (h i)
  · intro h j
    have hj : (x j - y j).natAbs + (y j - z j).natAbs = (x j - z j).natAbs := by
      have ht : ∀ i ∈ Finset.univ, (x i - z i).natAbs ≤
          (x i - y i).natAbs + (y i - z i).natAbs := fun i _ => abs_triangle _ _ _
      exact ((Finset.sum_eq_sum_iff_of_le ht).mp h.symm j (Finset.mem_univ j)).symm
    exact (abs_between _ _ _).mp hj

/-- Each robot can receive a separate bounded coordinate perturbation. -/
private def perturb {k : ℕ} {ι : Type*} (s : ι → Vertex k) (z : Vertex k)
    (o : ι → Vertex k) (i : ι) : Vertex k := fun j => 4 * s i j + z j + o i j

private theorem order_reflection (a b z u v : ℤ)
    (hu : -1 ≤ u ∧ u ≤ 1) (hv : -1 ≤ v ∧ v ≤ 1)
    (h : 4 * a + z + u ≤ 4 * b + z + v) : a ≤ b := by omega

/-- Bounded perturbations of the scaled set cannot create coordinate betweenness. -/
private theorem perturb_between_reflect {k : ℕ} {ι : Type*} (s : ι → Vertex k)
    (z : Vertex k) (o : ι → Vertex k)
    (ho : ∀ i j, -1 ≤ o i j ∧ o i j ≤ 1) (a b c : ι)
    (h : Between (perturb s z o a) (perturb s z o b) (perturb s z o c)) :
    Between (s a) (s b) (s c) := by
  intro j
  rcases h j with h | h
  · exact Or.inl ⟨order_reflection _ _ _ _ _ (ho a j) (ho b j) h.1,
      order_reflection _ _ _ _ _ (ho b j) (ho c j) h.2⟩
  · exact Or.inr ⟨order_reflection _ _ _ _ _ (ho c j) (ho b j) h.1,
      order_reflection _ _ _ _ _ (ho b j) (ho a j) h.2⟩

/-- Distinct labels remain at distinct lattice vertices throughout a partial translation. -/
private theorem perturb_injective {k : ℕ} {ι : Type*} (s : ι → Vertex k)
    (hs : Function.Injective s) (z : Vertex k) (o : ι → Vertex k)
    (ho : ∀ i j, -1 ≤ o i j ∧ o i j ≤ 1) :
    Function.Injective (perturb s z o) := by
  intro a b hab
  apply hs
  funext j
  have he := congrFun hab j
  exact le_antisymm
    (order_reflection _ _ _ _ _ (ho a j) (ho b j) he.le)
    (order_reflection _ _ _ _ _ (ho b j) (ho a j) he.symm.le)

/-- The coordinate general-position hypothesis gives actual graph general position
for every triple of distinct labels after bounded perturbation. -/
private theorem perturb_no_geodesic {k : ℕ} {ι : Type*} (s : ι → Vertex k)
    (hgp : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → ¬ Between (s a) (s b) (s c))
    (z : Vertex k) (o : ι → Vertex k)
    (ho : ∀ i j, -1 ≤ o i j ∧ o i j ≤ 1) :
    ∀ a b c, a ≠ b → b ≠ c → a ≠ c →
      ¬ CylinderSevenTen.OnGeodesic (lattice k)
        (perturb s z o a) (perturb s z o b) (perturb s z o c) := by
  intro a b c hab hbc hac h
  exact hgp a b c hab hbc hac
    (perturb_between_reflect s z o ho a b c ((between_iff_geodesic _ _ _).mpr h))

/-- A partially completed translation, with independently chosen robot flags. -/
private def mixed {k : ℕ} {ι : Type*} (s : ι → Vertex k) (z w : Vertex k)
    (A : ι → Prop) [DecidablePred A] (i : ι) : Vertex k :=
  fun j => 4 * s i j + z j + if A i then w j - z j else 0

private theorem mixed_bounds {k : ℕ} {ι : Type*} (z w : Vertex k)
    (hzw : (lattice k).Adj z w) (A : ι → Prop) [DecidablePred A] :
    ∀ i j, -1 ≤ (if A i then w j - z j else 0) ∧
      (if A i then w j - z j else 0) ≤ 1 := by
  obtain ⟨j,hj,he⟩ := hzw
  intro a i
  by_cases ha : A a
  · simp only [ite_eq_left ha]
    by_cases hij : i = j
    · subst i; rcases hj with hj | hj <;> omega
    · rw [he i hij]; omega
  · simp [ha]

/-- Every partial unit translation remains injective. -/
private theorem mixed_injective {k : ℕ} {ι : Type*} (s : ι → Vertex k)
    (hs : Function.Injective s) (z w : Vertex k) (hzw : (lattice k).Adj z w)
    (A : ι → Prop) [DecidablePred A] : Function.Injective (mixed s z w A) :=
  perturb_injective s hs z _ (mixed_bounds z w hzw A)

/-- All intermediate labelled configurations in a serialized unit translation are
in general position for the actual lattice graph. -/
private theorem mixed_no_geodesic {k : ℕ} {ι : Type*} (s : ι → Vertex k)
    (hgp : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → ¬ Between (s a) (s b) (s c))
    (z w : Vertex k) (hzw : (lattice k).Adj z w)
    (A : ι → Prop) [DecidablePred A] :
    ∀ a b c, a ≠ b → b ≠ c → a ≠ c →
      ¬ CylinderSevenTen.OnGeodesic (lattice k)
        (mixed s z w A a) (mixed s z w A b) (mixed s z w A c) :=
  perturb_no_geodesic s hgp z _ (mixed_bounds z w hzw A)

private noncomputable def tour_next {k : ℕ} (e : ℕ → Vertex k) (j : Fin k)
    (a : ℕ × Vertex k) : ℕ × Vertex k :=
  if h : l1 a.2 (e a.1) = 0 then
    (a.1 + 1, Function.update a.2 j (a.2 j + 1))
  else (a.1, (l1_descent a.2 (e a.1) h).choose)

private theorem tour_next_adj {k : ℕ} (e : ℕ → Vertex k) (j : Fin k)
    (a : ℕ × Vertex k) : (lattice k).Adj a.2 (tour_next e j a).2 := by
  classical
  unfold tour_next
  split_ifs with h
  · exact ⟨j, Or.inl (by simp), fun i hi => by simp [hi]⟩
  · exact (l1_descent a.2 (e a.1) h).choose_spec.1

private theorem tour_next_finish {k : ℕ} (e : ℕ → Vertex k) (j : Fin k)
    (a : ℕ × Vertex k) (h : a.2 = e a.1) :
    (tour_next e j a).1 = a.1 + 1 := by
  classical
  simp [tour_next, (l1_zero _ _).mpr h]

private theorem tour_next_continue {k : ℕ} (e : ℕ → Vertex k) (j : Fin k)
    (a : ℕ × Vertex k) (h : a.2 ≠ e a.1) :
    (tour_next e j a).1 = a.1 ∧
      l1 (tour_next e j a).2 (e a.1) + 1 = l1 a.2 (e a.1) := by
  classical
  have hn : l1 a.2 (e a.1) ≠ 0 := (l1_zero _ _).not.mpr h
  dsimp only [tour_next]
  rw [dite_eq_right hn]
  exact ⟨rfl, (l1_descent a.2 (e a.1) hn).choose_spec.2⟩

private noncomputable def tour_state {k : ℕ} (e : ℕ → Vertex k) (j : Fin k) :
    ℕ → ℕ × Vertex k
  | 0 => (0, 0)
  | n + 1 => tour_next e j (tour_state e j n)

private theorem tour_reaches_target {k : ℕ} (e : ℕ → Vertex k) (j : Fin k)
    (t q : ℕ) (hq : (tour_state e j t).1 = q) :
    ∃ u, t ≤ u ∧ (tour_state e j u).1 = q ∧ (tour_state e j u).2 = e q := by
  classical
  generalize hd : l1 (tour_state e j t).2 (e q) = d
  induction d using Nat.strong_induction_on generalizing t with
  | h d ih =>
    by_cases hz : d = 0
    · exact ⟨t, le_rfl, hq, (l1_zero _ _).mp (hd.trans hz)⟩
    · have hne : (tour_state e j t).2 ≠ e (tour_state e j t).1 := by
        rw [hq]
        intro he
        exact hz (hd.symm.trans ((l1_zero _ _).mpr he))
      have hn := tour_next_continue e j (tour_state e j t) hne
      have hq' : (tour_state e j (t + 1)).1 = q := hn.1.trans hq
      have hl : l1 (tour_state e j (t + 1)).2 (e q) < d := by
        change l1 (tour_next e j (tour_state e j t)).2 (e q) < d
        rw [hq] at hn
        omega
      obtain ⟨u,hu,huq,hue⟩ := ih _ hl (t + 1) hq' rfl
      exact ⟨u, by omega, huq, hue⟩

/-- One infinite signed-unit walk starts at zero and visits every lattice vertex.
A finished target always causes a genuine edge step, even for repeated targets. -/
private theorem exists_covering_walk (k : ℕ) (hk : 1 ≤ k) :
    ∃ z : ℕ → Vertex k, z 0 = 0 ∧
      (∀ t, (lattice k).Adj (z t) (z (t + 1))) ∧ Function.Surjective z := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat (Vertex k)
  let j : Fin k := ⟨0, by omega⟩
  have stages : ∀ q, ∃ t, (tour_state e j t).1 = q := by
    intro q
    induction q with
    | zero => exact ⟨0,rfl⟩
    | succ q ih =>
      obtain ⟨t,ht⟩ := ih
      obtain ⟨u,_,hu,hue⟩ := tour_reaches_target e j t q ht
      refine ⟨u + 1, ?_⟩
      change (tour_next e j (tour_state e j u)).1 = q + 1
      rw [tour_next_finish e j _ (by simpa [hu] using hue), hu]
  refine ⟨fun t => (tour_state e j t).2, rfl,
    fun t => tour_next_adj e j (tour_state e j t), ?_⟩
  intro x
  obtain ⟨q,rfl⟩ := he x
  obtain ⟨t,ht⟩ := stages q
  obtain ⟨u,_,_,hu⟩ := tour_reaches_target e j t q ht
  exact ⟨u,hu⟩

/-- At time `m * q + r`, precisely the first `r` robots have completed the next
unit translation. -/
private def serialized {k m : ℕ} (s : Fin m → Vertex k) (z : ℕ → Vertex k)
    (t : ℕ) : Fin m → Vertex k :=
  mixed s (z (t / m)) (z (t / m + 1)) (fun i => i.val < t % m)

private theorem serialized_checkpoint {k m : ℕ} (hm : 0 < m)
    (s : Fin m → Vertex k) (z : ℕ → Vertex k) (q : ℕ) (i : Fin m) :
    serialized s z (m * q) i = fun j => 4 * s i j + z q j := by
  funext j
  simp [serialized, mixed, Nat.mul_div_cancel_left q hm]

private theorem mixed_adj {k : ℕ} {ι : Type*} (s : ι → Vertex k)
    (z w : Vertex k) (h : (lattice k).Adj z w) (i : ι) :
    (lattice k).Adj (fun j => 4 * s i j + z j) (fun j => 4 * s i j + w j) := by
  obtain ⟨j,hj,he⟩ := h
  refine ⟨j, ?_, fun a ha => by dsimp; rw [he a ha]⟩
  rcases hj with hj | hj
  · exact Or.inl (by dsimp; omega)
  · exact Or.inr (by dsimp; omega)

/-- The quotient / remainder trace changes exactly one labelled robot on each
step, including the transition between consecutive translation blocks. -/
private theorem serialized_step {k m : ℕ} (hm : 0 < m) (s : Fin m → Vertex k)
    (z : ℕ → Vertex k) (hz : ∀ q, (lattice k).Adj (z q) (z (q + 1))) (t : ℕ) :
    ∃ i : Fin m,
      (lattice k).Adj (serialized s z t i) (serialized s z (t + 1) i) ∧
      ∀ a, a ≠ i → serialized s z t a = serialized s z (t + 1) a := by
  classical
  let r := t % m
  let q := t / m
  have hr : r < m := Nat.mod_lt _ hm
  have ht : t = m * q + r := by
    simpa [q, r, Nat.add_comm] using (Nat.mod_add_div t m).symm
  let i : Fin m := ⟨r, hr⟩
  have he0 : serialized s z t i = fun j => 4 * s i j + z q j := by
    funext j
    simp [serialized, mixed, q, i, r]
  have hlast : r + 1 = m ∨ r + 1 < m := by omega
  rcases hlast with hlast | hmore
  · have ht' : t + 1 = m * (q + 1) := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    have he1 : serialized s z (t + 1) i = fun j => 4 * s i j + z (q + 1) j := by
      rw [ht']
      exact serialized_checkpoint hm s z (q + 1) i
    refine ⟨i, ?_, ?_⟩
    · rw [he0,he1]; exact mixed_adj s _ _ (hz q) i
    · intro a hai
      have har : a.val < r := by
        have hne : a.val ≠ r := fun h => hai (Fin.ext h)
        omega
      rw [ht', serialized_checkpoint hm]
      funext j
      simp [serialized, mixed, q, show a.val < t%m from har]
  · have ht' : t + 1 = m * q + (r + 1) := by omega
    have hdiv : (t + 1) / m = q := by
      rw [ht', Nat.mul_add_div hm]
      simp [Nat.div_eq_of_lt hmore]
    have hmod : (t + 1)%m = r + 1 := by
      rw [ht', Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hmore
    have he1 : serialized s z (t + 1) i = fun j => 4 * s i j + z (q + 1) j := by
      funext j
      simp [serialized, mixed, hdiv, hmod, i, r]
    refine ⟨i, ?_, ?_⟩
    · rw [he0,he1]; exact mixed_adj s _ _ (hz q) i
    · intro a hai
      have hne : a.val ≠ r := fun h => hai (Fin.ext h)
      have hiff : a.val < r ↔ a.val < r + 1 := by omega
      funext j
      simp only [serialized, mixed, hdiv, hmod]
      change 4 * s a j + z q j + (if a.val < r then _ else _) = _
      simp only [hiff, show t / m = q from rfl]

/-- One infinite trace starting at the fourfold scaled labelled configuration,
with injective positions, graph general position, exactly one adjacent move
into a vacant vertex at each step, and coverage by every fixed robot. -/
def ScaledCoveringTrace {k m : ℕ} (s : Fin m → Vertex k)
    (p : ℕ → Fin m → Vertex k) : Prop :=
      (∀ i, p 0 i = fun j => 4 * s i j) ∧
      (∀ t, Function.Injective (p t)) ∧
      (∀ t a b c, a ≠ b → b ≠ c → a ≠ c →
        ¬ CylinderSevenTen.OnGeodesic (lattice k) (p t a) (p t b) (p t c)) ∧
      (∀ t, ∃ i,
        (lattice k).Adj (p t i) (p (t + 1) i) ∧
        (∀ a, a ≠ i → p t a = p (t + 1) a) ∧
        p (t + 1) i ∉ Set.range (p t)) ∧
      ∀ i x, ∃ t, p t i = x

/-- A single common infinite trace serializes all translations. Every fixed
robot visits every lattice vertex, while each time step moves one robot into
an unoccupied vertex and preserves actual graph general position. -/
private theorem scaled_labelled_mobile (k m : ℕ) (hk : 1 ≤ k) (hm : 0 < m)
    (s : Fin m → Vertex k) (hs : Function.Injective s)
    (hgp : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → ¬ Between (s a) (s b) (s c)) :
    ∃ p : ℕ → Fin m → Vertex k, ScaledCoveringTrace s p := by
  classical
  obtain ⟨z,hz0,hz,hcover⟩ := exists_covering_walk k hk
  let p := serialized s z
  have hinj : ∀ t, Function.Injective (p t) := fun t =>
    mixed_injective s hs _ _ (hz (t / m)) _
  refine ⟨p, ?_, hinj, ?_, ?_, ?_⟩
  · intro i
    have hc := serialized_checkpoint hm s z 0 i
    simpa [hz0] using hc
  · intro t
    exact mixed_no_geodesic s hgp _ _ (hz (t / m)) _
  · intro t
    obtain ⟨i,hi,he⟩ := serialized_step hm s z hz t
    refine ⟨i,hi,he,?_⟩
    rintro ⟨a,ha⟩
    by_cases hai : a = i
    · subst a
      exact (lattice k).ne_of_adj hi ha
    · exact hai (hinj (t + 1) ((he a hai).symm.trans ha))
  · intro i x
    obtain ⟨q,hq⟩ := hcover (fun j => x j - 4 * s i j)
    refine ⟨m * q, ?_⟩
    change serialized s z (m * q) i = x
    rw [serialized_checkpoint hm]
    funext j
    have he := congrFun hq j
    change z q j = x j - 4 * s i j at he
    omega

/-- Every nonempty finite coordinate general-position set has a labelled
common covering trace from its fourfold scaled configuration. The labels
enumerate exactly the given finite set. -/
theorem scaled_finset_trace {k : ℕ} (hk : 1 ≤ k) (S : Finset (Vertex k))
    (hne : S.Nonempty)
    (hgp : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      a ≠ b → b ≠ c → a ≠ c → ¬ Between a b c) :
    ∃ (s : Fin S.card → Vertex k) (p : ℕ → Fin S.card → Vertex k),
      Function.Injective s ∧ Finset.univ.image s = S ∧ ScaledCoveringTrace s p := by
  classical
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
  let s : Fin S.card → Vertex k := fun i => (e.symm i).val
  have hs : Function.Injective s := by
    intro a b hab
    apply e.symm.injective
    exact Subtype.ext hab
  have himage : Finset.univ.image s = S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact (e.symm i).property
    · intro hx
      refine ⟨e ⟨x,hx⟩, ?_⟩
      change (e.symm (e ⟨x,hx⟩)).val = x
      simp
  have hlabel : ∀ a b c, a ≠ b → b ≠ c → a ≠ c →
      ¬ Between (s a) (s b) (s c) := by
    intro a b c hab hbc hac
    exact hgp _ (e.symm a).property _ (e.symm b).property _ (e.symm c).property
      (fun h => hab (hs h)) (fun h => hbc (hs h)) (fun h => hac (hs h))
  obtain ⟨p,hp⟩ := scaled_labelled_mobile k S.card hk (Finset.card_pos.mpr hne) s hs hlabel
  exact ⟨s,p,hs,himage,hp⟩

end D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion
