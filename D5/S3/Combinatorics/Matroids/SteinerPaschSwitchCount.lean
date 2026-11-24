/- GID: D5/S3/Combinatorics/Matroids/SteinerPaschSwitchCount
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/SteinerPaschSwitchCount
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Opposite pivots of a Pasch configuration characterize label-dependent switch counts. -/

import D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange

/-! The four blocks in a Pasch configuration form a square of the two pivot matchings. -/

namespace D5.S3.Combinatorics.Matroids.SteinerPaschSwitchCount

open SimpleGraph Function
open D5.S3.Combinatorics.Matroids.SteinerAlternatingSwitches (Matchings SuccessfulStart)
open D5.S3.Combinatorics.Matroids.SteinerSchreierExtension (extensionMul)
open D5.S3.Combinatorics.Matroids.SteinerFixedPivotCountRange (labelledFixedPivotCountRange)
open D5.S3.Combinatorics.Matroids.PointDeletedSteinerSwitch (pointDeletedFamily)
open D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition (IsPartialSteiner)
open D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap (Covered Uncovered)
open D5.S3.Combinatorics.Matroids.SteinerMatchingTranslations (translate)

/-- The six points are distinct and different from the adjoined identity. The four
multiplication equalities specify the four blocks, with the two pivots opposite. -/
def HasOppositePasch {L : Type*} [Mul L] (e p q : L) : Prop :=
  ∃ a b c d : L, [e, p, q, a, b, c, d].Nodup ∧
    q * a = b ∧ p * b = c ∧ q * c = d ∧ p * d = a

private theorem hasOppositePasch_iff_square {L : Type*} [Finite L] [Mul L]
    (G : SimpleGraph L) (e p q : L)
    (one : ∀ x, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (different : p ≠ q)
    (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v) :
    HasOppositePasch e p q ↔
      ∃ C : G.ConnectedComponent, C ≠ G.connectedComponentMk e ∧ C.supp.ncard = 4 := by
  classical
  have hp : p ≠ e := fun eq => G.irrefl ((edges e e).mpr (Or.inl (eq.symm ▸ one e)))
  have hq : q ≠ e := fun eq => G.irrefl ((edges e e).mpr (Or.inr (eq.symm ▸ one e)))
  have injectRight (x : L) : Injective (· * x) := by
    intro u v eq
    exact (show Involutive (x * ·) from invol x).injective
      (by simpa only [comm x u, comm x v] using eq)
  let M : Matchings L := {
    first := (p * ·)
    second := (q * ·)
    first_involutive := invol p
    second_involutive := invol q
    first_ne_self := fun x eq => hp (injectRight x (eq.trans (one x).symm))
    second_ne_self := fun x eq => hq (injectRight x (eq.trans (one x).symm))
    partners_ne := fun x eq => different (injectRight x eq)
  }
  have graphEq : G = M.graph := by
    ext u v
    exact edges u v
  subst G
  have atP : p * e = p := (comm p e).trans (one p)
  have atQ : q * e = q := (comm q e).trans (one q)
  have specialCommute : M.first (M.second e) = M.second (M.first e) := by
    change p * (q * e) = q * (p * e)
    rw [atP, atQ, comm p q]
  have special : (M.graph.connectedComponentMk e).supp = {e, p, q, p * q} := by
    simpa only [M, atP, atQ] using M.component_eq_square specialCommute
  constructor
  · rintro ⟨a, b, c, d, distinct, hab, hbc, hcd, hda⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
      not_false_eq_true, List.nodup_nil, and_true] at distinct
    have hpa : p * a = d := by rw [← hda, invol]
    have commute : M.first (M.second a) = M.second (M.first a) := by
      change p * (q * a) = q * (p * a)
      rw [hab, hbc, hpa, ← hcd, invol]
    refine ⟨M.graph.connectedComponentMk a, ?_, ?_⟩
    · intro same
      have mem : a ∈ (M.graph.connectedComponentMk e).supp :=
        (ConnectedComponent.mem_supp_iff _ _).mpr same
      rw [special] at mem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at mem
      have apart : a ≠ p * q := by
        intro eq
        have bp : b = p := by rw [← hab, eq, comm p q, invol]
        exact (by tauto : p ≠ b) bp.symm
      rcases mem with eq | eq | eq | eq
      · exact (by tauto : e ≠ a) eq.symm
      · exact (by tauto : p ≠ a) eq.symm
      · exact (by tauto : q ≠ a) eq.symm
      · exact apart eq
    · rw [M.component_eq_square commute, M.square_card]
  · rintro ⟨C, differentComponent, size⟩
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h a =>
      have commute : M.first (M.second a) = M.second (M.first a) := by
        by_contra neq
        have large := (M.noncommute_iff_six_le_component a).mp neq
        omega
      change p * (q * a) = q * (p * a) at commute
      let b := q * a
      let c := p * b
      let d := p * a
      have close : q * c = d := by
        change q * (p * (q * a)) = p * a
        rw [commute, invol]
      have square : (M.graph.connectedComponentMk a).supp = {a, d, b, c} :=
        M.component_eq_square commute
      have separated (y : L) (hy : y ∈ ({a, d, b, c} : Set L)) (z : L)
          (hz : z ∈ ({e, p, q, p * q} : Set L)) : z ≠ y := by
        intro eq
        subst z
        rw [← special, ConnectedComponent.mem_supp_iff] at hz
        rw [← square, ConnectedComponent.mem_supp_iff] at hy
        exact differentComponent (hy.symm.trans hz)
      have away (y : L) (hy : y ∈ ({a, d, b, c} : Set L)) :
          e ≠ y ∧ p ≠ y ∧ q ≠ y :=
        ⟨separated y hy e (by simp), separated y hy p (by simp), separated y hy q (by simp)⟩
      have ha := away a (by simp)
      have hb := away b (by simp)
      have hc := away c (by simp)
      have hd := away d (by simp)
      have ab : a ≠ b := (M.second_ne_self a).symm
      have ad : a ≠ d := (M.first_ne_self a).symm
      have bd : b ≠ d := (M.partners_ne a).symm
      have bc : b ≠ c := (M.first_ne_self b).symm
      have cd : c ≠ d := by
        intro h
        exact ab (M.first_involutive.injective (show M.first b = M.first a from h)).symm
      have ac : a ≠ c := by
        intro eq
        have same : p * a = b := by rw [eq]; exact invol p b
        exact bd same.symm
      refine ⟨a, b, c, d, ?_, rfl, rfl, close, invol p a⟩
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false,
        not_false_eq_true, List.nodup_nil, and_true]
      tauto

/-- The attainable count depends on the labels exactly when a Pasch has these opposite pivots. -/
theorem variableLabelledSwitchCount_iff {L A : Type*} [Finite L] [Mul L]
    [Finite A] [AddCommGroup A] [Module (ZMod 2) A] [Nontrivial A]
    (G : SimpleGraph L) (e p q : L)
    (one : ∀ x, e * x = x) (comm : ∀ x y : L, x * y = y * x)
    (invol : ∀ x y : L, x * (x * y) = y) (centreless : Set.center L = {e})
    (different : p ≠ q) (edges : ∀ u v, G.Adj u v ↔ p * u = v ∨ q * u = v) :
    let attainable (count : ℕ) := ∃ (labels : Set L → A) (r : ℕ)
      (label : Option (Fin (r + 1)) ≃ L × A)
      (S : Set (Set (Fin (r + 1)))) (valid : IsPartialSteiner S)
      (cover : ∀ a b : Fin (r + 1), a ≠ b → Covered S a b)
      (i : Fin (r + 1)) (v : Fin r) (m : Fin r → Fin r),
      letI := extensionMul e labels
      label none = (e, 0) ∧ label (some i) = (p, 0) ∧
      label (some (i.succAbove v)) = (q, 0) ∧
      (∀ j a, label (translate valid cover j a) = label (some j) * label a) ∧
      (∀ a b, Uncovered (pointDeletedFamily S i) a b ↔ m a = b) ∧
      ({a | SuccessfulStart (pointDeletedFamily S i) m v a} : Set (Fin r)).ncard = count
    (∃ n₁ n₂, attainable n₁ ∧ attainable n₂ ∧ n₁ ≠ n₂) ↔ HasOppositePasch e p q := by
  classical
  intro attainable
  let b := ({x : L | p * (q * (p * (q * x))) ≠ x} : Set L).ncard
  let squares := {C : G.ConnectedComponent | C ≠ G.connectedComponentMk e ∧ C.supp.ncard = 4}
  have range (n : ℕ) :
      attainable n ↔ ∃ k ≤ squares.ncard, (k = 0 ∨ Nontrivial A) ∧
        n = Nat.card A * (b + 4 * k) :=
    labelledFixedPivotCountRange (A := A) G e p q one comm invol centreless different edges n
  rw [hasOppositePasch_iff_square G e p q one comm invol different edges]
  constructor
  · rintro ⟨n₁, n₂, a₁, a₂, differentCounts⟩
    obtain ⟨k₁, le₁, _, eq₁⟩ := (range n₁).mp a₁
    obtain ⟨k₂, le₂, _, eq₂⟩ := (range n₂).mp a₂
    have positive : 0 < squares.ncard := by
      by_contra! nonpositive
      have same : k₁ = k₂ := by omega
      exact differentCounts (by rw [eq₁, eq₂, same])
    exact ((Set.ncard_pos (Set.toFinite squares)).mp positive)
  · rintro ⟨C, hc⟩
    have positive : 0 < squares.ncard :=
      (Set.ncard_pos (Set.toFinite squares)).mpr ⟨C, hc⟩
    have cardA : 0 < Nat.card A := Nat.card_pos
    refine ⟨Nat.card A * b, Nat.card A * (b + 4), ?_, ?_, ?_⟩
    · exact (range _).mpr ⟨0, Nat.zero_le _, Or.inl rfl, by simp⟩
    · exact (range _).mpr ⟨1, positive, Or.inr inferInstance, by simp⟩
    · exact Nat.ne_of_lt (Nat.mul_lt_mul_of_pos_left (by omega) cardA)

end D5.S3.Combinatorics.Matroids.SteinerPaschSwitchCount
