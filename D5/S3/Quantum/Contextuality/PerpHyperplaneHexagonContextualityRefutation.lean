/- GID: D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.claim; result=D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.result; claim=D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.claim
   digest: The perp hyperplane refutes the classical-hexagon contextuality conjecture. -/

import D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity

/-! The line-set reading of Saniga et al., arXiv:2312.07738v3, preregistered in #24997.
Assignments and line signs use additive binary notation: one denotes a negative sign.
The witness consists of all isotropic lines inside the perp of the observable IIZ.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity

namespace D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation

noncomputable section

/-- Binary labels of three-qubit Pauli observables, including the identity label. -/
abbrev point := Fin 3 → ZMod 2 × ZMod 2

/-- The full three-qubit symplectic space. Its projective points exclude zero. -/
def w : Submodule (ZMod 2) point := ⊤

/-- The additive sign of the canonical Pauli product: one is negative. -/
def lineSign (l : Finset point) : ZMod 2 := by
  classical
  exact if lineProduct l = -1 then 1 else 0

/-- The number of contexts whose additive parity disagrees with the Pauli sign. -/
def violations (c : Finset (Finset point)) (f : point → ZMod 2) : ℕ := by
  classical
  exact (c.filter fun l => (∑ q ∈ l, f q) ≠ lineSign l).card

/-- Minimum number of violated contexts over all binary hidden-variable assignments. -/
def contextualityDegree (c : Finset (Finset point)) : ℕ :=
  sInf (Set.range (violations c))

/-- Every classically embedded split Cayley hexagon satisfies these axioms:
three lines per point, no ordinary triangle, and planarity at every point.
Thus this class contains every classical embedding used in the source conjecture. -/
def IsClassicalHexagon (h : Finset (Finset point)) : Prop :=
  h ⊆ lines w ∧
  (∀ q ∈ points w, (h.filter fun l => q ∈ l).card = 3) ∧
  (∀ a b c : point, ∀ l ∈ h, ∀ m ∈ h, ∀ n ∈ h,
    a ≠ b → b ≠ c → c ≠ a → l ≠ m → m ≠ n → n ≠ l →
    a ∈ l → b ∈ l → b ∈ m → c ∈ m → c ∈ n → a ∈ n → False) ∧
  (∀ z a b : point, ∀ l ∈ h, ∀ m ∈ h,
    z ∈ l → z ∈ m → a ∈ l → b ∈ m → B a b = 0)

/-- The source's generalization to arbitrary contextual line subgeometries. -/
def claim : Prop :=
  ∀ c : Finset (Finset point), c ⊆ lines w → 0 < contextualityDegree c →
    ∃ h, IsClassicalHexagon h ∧ contextualityDegree c = (c ∩ h).card

private def pole : point := ![(0, 0), (0, 0), (0, 1)]

private def counterexample : Finset (Finset point) := by
  classical
  exact (lines w).filter fun l => ∀ q ∈ l, B pole q = 0

private theorem counterexample_subset : counterexample ⊆ lines w := by
  classical
  exact Finset.filter_subset _ _

private def triple (u v : point) : Finset point := {u, v, u + v}

private def exponent (u v : point) : ZMod 4 :=
  ∑ j, localExponent (u j) (v j)

private def perpPoints : Finset point :=
  Finset.univ.filter fun q => q ≠ 0 ∧ B pole q = 0

private def negativeCertificate : Finset (Finset point) :=
  perpPoints.biUnion fun u =>
    (perpPoints.filter fun v => u ≠ v ∧ B u v = 0 ∧ exponent u v = 2).image (triple u)

private theorem point_count : (points w).card = 63 := by
  delta w
  simp only [points, Submodule.mem_top, true_and]
  decide

private theorem perp_count : perpPoints.card = 31 := by decide

private theorem certificate_count : negativeCertificate.card = 12 := by decide

private theorem line_data (l : Finset point) (hl : l ∈ lines w) :
    l ⊆ points w ∧ l.card = 3 ∧
      ∀ u ∈ l, ∀ v ∈ l, u ≠ v → u + v ∈ l ∧ B u v = 0 := by
  classical
  simpa only [lines, Finset.mem_filter, Finset.mem_powerset] using hl

private theorem line_pair (l : Finset point) (hl : l ∈ lines w) :
    ∃ u v : point, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ B u v = 0 ∧ l = triple u v := by
  classical
  obtain ⟨hs, hc, hp⟩ := line_data l hl
  obtain ⟨u, v, t, huv, hut, hvt, he⟩ := Finset.card_eq_three.mp hc
  have hu : u ∈ l := by simp [he]
  have hv : v ∈ l := by simp [he]
  have hu0 := (Finset.mem_filter.mp (hs hu)).2.2
  have hv0 := (Finset.mem_filter.mp (hs hv)).2.2
  obtain ⟨ha, hb⟩ := hp u hu v hv huv
  have ht : u + v = t := by
    have hh : u + v = u ∨ u + v = v ∨ u + v = t := by simpa [he] using ha
    rcases hh with h | h | h
    · exact False.elim (hv0 (add_left_cancel (h.trans (add_zero u).symm)))
    · exact False.elim (hu0 (add_right_cancel (h.trans (zero_add v).symm)))
    · exact h
  exact ⟨u, v, hu0, hv0, huv, hb, by simpa [triple, ht] using he⟩

private theorem triple_line (u v : point) (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : u ≠ v) (hb : B u v = 0) : triple u v ∈ lines w := by
  classical
  delta w
  have hs0 : u + v ≠ 0 := fun he => hne (CharTwo.add_eq_zero.mp he)
  have hsu : u + v ≠ u := fun he => hv (add_left_cancel (he.trans (add_zero u).symm))
  have hsv : u + v ≠ v := fun he => hu (add_right_cancel (he.trans (zero_add v).symm))
  have hsum : v + (u + v) = u := by rw [add_comm u v, CharTwo.add_cancel_left]
  simp only [lines, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> simp [points, hu, hv, hs0]
  · simp [triple, hne, Ne.symm hsu, Ne.symm hsv]
  · intro a ha b hbmem hab
    simp only [triple, Finset.mem_insert, Finset.mem_singleton] at ha hbmem
    rcases ha with rfl | rfl | rfl <;> rcases hbmem with rfl | rfl | rfl <;>
      simp_all [triple, B_add_right, B_self, B_comm, add_comm]
    all_goals rw [add_comm _ (_ + _), CharTwo.add_cancel_right]

private theorem phase_exponent (u v : point) :
    phase u v = AddChar.zmodChar 4 Complex.I_pow_four (exponent u v) := by
  delta phase exponent
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ,
    AddChar.map_add_eq_mul, Fin.prod_univ_zero, Fin.sum_univ_zero,
    mul_one, add_zero]

private theorem char_negative (a : ZMod 4) :
    AddChar.zmodChar 4 Complex.I_pow_four a = -1 ↔ a = 2 := by
  fin_cases a
  · change (Complex.I ^ 0 = -1 ↔ (0 : ZMod 4) = 2)
    norm_num [Complex.ext_iff]
    decide
  · change (Complex.I ^ 1 = -1 ↔ (1 : ZMod 4) = 2)
    norm_num [Complex.ext_iff]
    decide
  · change (Complex.I ^ 2 = -1 ↔ (2 : ZMod 4) = 2)
    norm_num [Complex.I_sq]
  · change (Complex.I ^ 3 = -1 ↔ (3 : ZMod 4) = 2)
    norm_num [pow_succ, Complex.I_sq, Complex.ext_iff]
    decide

private theorem triple_negative (u v : point) (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : u ≠ v) (hb : B u v = 0) :
    lineProduct (triple u v) = -1 ↔ exponent u v = 2 := by
  rw [triple, lineProduct_triple u v hu hv hne hb, phase_exponent]
  constructor
  · intro he
    apply (char_negative _).mp
    have hee := congrArg (fun m => m (fun _ => 0) (fun _ => 0)) he
    simpa using hee
  · intro he
    rw [(char_negative _).mpr he]
    simp

private theorem negative_cover (l : Finset point) (hl : l ∈ counterexample)
    (hn : lineProduct l = -1) : l ∈ negativeCertificate := by
  classical
  obtain ⟨hlw, hlp⟩ := Finset.mem_filter.mp hl
  obtain ⟨u, v, hu, hv, hne, hb, he⟩ := line_pair l hlw
  have hum : u ∈ l := by simp [he, triple]
  have hvm : v ∈ l := by simp [he, triple]
  apply Finset.mem_biUnion.mpr
  refine ⟨u, ?_, Finset.mem_image.mpr ⟨v, ?_, he.symm⟩⟩
  · delta perpPoints
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hu, hlp u hum⟩
  · delta perpPoints
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨hv, hlp v hvm⟩, hne, hb,
      (triple_negative u v hu hv hne hb).mp (he ▸ hn)⟩

private theorem negative_certificate_exact :
    counterexample ∩ negativeLines w = negativeCertificate := by
  classical
  ext l
  constructor
  · intro hl
    obtain ⟨hc, hn⟩ := Finset.mem_inter.mp hl
    exact negative_cover l hc (Finset.mem_filter.mp hn).2
  · intro hl
    obtain ⟨u, hu, hrest⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hrest
    obtain ⟨hvp, hne, hb, he⟩ := Finset.mem_filter.mp hv
    have hup := (Finset.mem_filter.mp hu).2
    have hvp := (Finset.mem_filter.mp hvp).2
    have hlw := triple_line u v hup.1 hvp.1 hne hb
    have hcp : triple u v ∈ counterexample := by
      refine Finset.mem_filter.mpr ⟨hlw, ?_⟩
      simp [triple, B_add_right, hup.2, hvp.2]
    exact Finset.mem_inter.mpr ⟨hcp, Finset.mem_filter.mpr
      ⟨hlw, (triple_negative u v hup.1 hvp.1 hne hb).mpr he⟩⟩

private theorem incidence_swap (h : Finset (Finset point)) (s : Finset point) :
    (∑ l ∈ h, (l ∩ s).card) = ∑ q ∈ s, (h.filter fun l => q ∈ l).card := by
  classical
  have he (l : Finset point) : (l ∩ s).card = ∑ q ∈ s, if q ∈ l then 1 else 0 := by
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

private theorem binary_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

private theorem line_perp_profile (l : Finset point) (hl : l ∈ lines w) :
    (l ∩ perpPoints).card = if l ∈ counterexample then 3 else 1 := by
  classical
  obtain ⟨u, v, hu, hv, hne, hb, rfl⟩ := line_pair l hl
  have hs0 : u + v ≠ 0 := fun he => hne (CharTwo.add_eq_zero.mp he)
  have hsu : u + v ≠ u := fun he => hv (add_left_cancel (he.trans (add_zero u).symm))
  have hsv : u + v ≠ v := fun he => hu (add_right_cancel (he.trans (zero_add v).symm))
  have he : triple u v ∩ perpPoints =
      (triple u v).filter (fun q => B pole q = 0) := by
    ext q
    delta perpPoints
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · tauto
    · rintro ⟨hq, hqp⟩
      refine ⟨hq, ?_, hqp⟩
      simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;> assumption
  have hm : triple u v ∈ counterexample ↔ B pole u = 0 ∧ B pole v = 0 := by
    delta counterexample
    simp only [Finset.mem_filter, hl, true_and]
    simp [triple, B_add_right]
    intro hpu hpv
    rw [hpu, hpv, zero_add]
  rw [he]
  simp only [hm]
  rcases binary_cases (B pole u) with hx | hx <;>
    rcases binary_cases (B pole v) with hy | hy <;>
    simp [triple, Finset.filter_insert, Finset.filter_singleton, B_add_right,
      hx, hy, hne, Ne.symm hsu, Ne.symm hsv, CharTwo.add_self_eq_zero]



private theorem hexagon_card (h : Finset (Finset point)) (hh : IsClassicalHexagon h) :
    h.card = 63 := by
  classical
  have hi := incidence_swap h (points w)
  have he : (∑ l ∈ h, (l ∩ points w).card) = h.card * 3 := by
    calc
      _ = ∑ _l ∈ h, 3 := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.inter_eq_left.mpr (line_data l (hh.1 hl)).1]
        exact (line_data l (hh.1 hl)).2.1
      _ = _ := by simp
  have hd : (∑ q ∈ points w, (h.filter fun l => q ∈ l).card) =
      (points w).card * 3 := by
    calc
      _ = ∑ _q ∈ points w, 3 := Finset.sum_congr rfl (fun q hq => hh.2.1 q hq)
      _ = _ := by simp
  rw [he, hd, point_count] at hi
  omega

private def squarePairs : Fin 6 → point × point :=
  ![(![(1, 0), (0, 0), (0, 0)], ![(0, 0), (1, 0), (0, 0)]),
    (![(0, 0), (0, 1), (0, 0)], ![(0, 1), (0, 0), (0, 0)]),
    (![(1, 0), (0, 1), (0, 0)], ![(0, 1), (1, 0), (0, 0)]),
    (![(1, 0), (0, 0), (0, 0)], ![(0, 0), (0, 1), (0, 0)]),
    (![(0, 0), (1, 0), (0, 0)], ![(0, 1), (0, 0), (0, 0)]),
    (![(1, 0), (1, 0), (0, 0)], ![(0, 1), (0, 1), (0, 0)])]

private def squareLine (i : Fin 6) : Finset point :=
  triple (squarePairs i).1 (squarePairs i).2

private theorem square_data : ∀ i : Fin 6,
    (squarePairs i).1 ≠ 0 ∧ (squarePairs i).2 ≠ 0 ∧
    (squarePairs i).1 ≠ (squarePairs i).2 ∧
    B (squarePairs i).1 (squarePairs i).2 = 0 ∧
    B pole (squarePairs i).1 = 0 ∧ B pole (squarePairs i).2 = 0 ∧
    (exponent (squarePairs i).1 (squarePairs i).2 = 2 ↔ i = 5) := by decide

private theorem square_mem (i : Fin 6) : squareLine i ∈ counterexample := by
  classical
  obtain ⟨hu, hv, hne, hb, hpu, hpv, _⟩ := square_data i
  refine Finset.mem_filter.mpr ⟨triple_line _ _ hu hv hne hb, ?_⟩
  delta squareLine
  simp [triple, B_add_right, hpu, hpv]

private theorem square_even : ∀ q : point,
    (∑ i : Fin 6, if q ∈ squareLine i then (1 : ZMod 2) else 0) = 0 := by decide

private theorem square_parity (f : point → ZMod 2) :
    (∑ i : Fin 6, ∑ q ∈ squareLine i, f q) = 0 := by
  classical
  calc
    _ = ∑ i : Fin 6, ∑ q : point, if q ∈ squareLine i then f q else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ q : point, ∑ i : Fin 6, if q ∈ squareLine i then f q else 0 :=
      Finset.sum_comm
    _ = ∑ q : point,
        (∑ i : Fin 6, if q ∈ squareLine i then (1 : ZMod 2) else 0) * f q := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_mul]
      simp
    _ = 0 := by simp_rw [square_even, zero_mul]; simp

private theorem square_signs : (∑ i : Fin 6, lineSign (squareLine i)) = 1 := by
  classical
  have he (i : Fin 6) : lineSign (squareLine i) = if i = 5 then 1 else 0 := by
    obtain ⟨hu, hv, hne, hb, _, _, hs⟩ := square_data i
    delta lineSign squareLine
    simp only [triple_negative _ _ hu hv hne hb, hs]
  simp_rw [he]
  simp

private theorem square_violation (f : point → ZMod 2) :
    ∃ i : Fin 6, (∑ q ∈ squareLine i, f q) ≠ lineSign (squareLine i) := by
  by_contra hn
  push Not at hn
  have he := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 6))) rfl
    (fun i _ => hn i)
  rw [square_parity f, square_signs] at he
  exact zero_ne_one he

private theorem counterexample_contextual : 0 < contextualityDegree counterexample := by
  classical
  apply Nat.succ_le_iff.mp
  apply le_csInf (Set.range_nonempty _)
  rintro n ⟨f, rfl⟩
  obtain ⟨i, hi⟩ := square_violation f
  exact Finset.card_pos.mpr ⟨squareLine i, Finset.mem_filter.mpr ⟨square_mem i, hi⟩⟩

private theorem counterexample_degree_le : contextualityDegree counterexample ≤ 12 := by
  classical
  have hmin : contextualityDegree counterexample ≤ violations counterexample (fun _ => 0) :=
    csInf_le (OrderBot.bddBelow _) ⟨_, rfl⟩
  have he : violations counterexample (fun _ => 0) =
      (counterexample ∩ negativeLines w).card := by
    unfold violations
    congr 1
    ext l
    constructor
    · intro hl
      obtain ⟨hc, hn⟩ := Finset.mem_filter.mp hl
      refine Finset.mem_inter.mpr ⟨hc, Finset.mem_filter.mpr
        ⟨counterexample_subset hc, ?_⟩⟩
      by_contra hp
      delta lineSign at hn
      simp [hp] at hn
    · intro hl
      obtain ⟨hc, hneg⟩ := Finset.mem_inter.mp hl
      have hn := (Finset.mem_filter.mp hneg).2
      apply Finset.mem_filter.mpr
      refine ⟨hc, ?_⟩
      delta lineSign
      simp [hn]
  rw [he, negative_certificate_exact, certificate_count] at hmin
  exact hmin

private theorem hexagon_intersection_ge (h : Finset (Finset point))
    (hh : IsClassicalHexagon h) : 15 ≤ (counterexample ∩ h).card := by
  classical
  have hi := incidence_swap h perpPoints
  have hp : ∀ q ∈ perpPoints, q ∈ points w := by
    intro q hq
    delta perpPoints at hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    delta w
    simp [points, hq.1]
  have hd : (∑ q ∈ perpPoints, (h.filter fun l => q ∈ l).card) = 93 := by
    trans ∑ _q ∈ perpPoints, 3
    · exact Finset.sum_congr rfl (fun q hq => hh.2.1 q (hp q hq))
    · simp [perp_count]
  rw [hd] at hi
  have he : (∑ l ∈ h, (l ∩ perpPoints).card) =
      2 * (h.filter fun l => l ∈ counterexample).card + h.card := by
    calc
      _ = ∑ l ∈ h, ((if l ∈ counterexample then 2 else 0) + 1) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [line_perp_profile l (hh.1 hl)]
        split_ifs <;> rfl
      _ = _ := by simp [Finset.sum_add_distrib, Finset.filter_mem_eq_inter, mul_comm]
  rw [he, hexagon_card h hh] at hi
  have hf : h.filter (fun l => l ∈ counterexample) = counterexample ∩ h := by
    ext l
    simp [and_comm]
  rw [hf] at hi
  omega

/-- The IIZ perp hyperplane has positive degree at most twelve, but shares at least
fifteen lines with every classical hexagon. -/
theorem result : ¬ claim := by
  classical
  intro hc
  obtain ⟨h, hh, he⟩ := hc counterexample counterexample_subset counterexample_contextual
  have hlo := hexagon_intersection_ge h hh
  have hhi := counterexample_degree_le
  omega

end

end D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation
