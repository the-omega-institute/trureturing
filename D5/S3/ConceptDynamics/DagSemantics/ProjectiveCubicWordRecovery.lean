/- GID: D5/S3/ConceptDynamics/DagSemantics/ProjectiveCubicWordRecovery
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/ProjectiveCubicWordRecovery
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Local ternary triple-equality readouts lose exactly one independent orientation per active incidence run. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Logic.Relation

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.ProjectiveCubicWordRecovery

variable {F V : Type*} [Field F]

/-- Edges of the comparison graph that link actual nonzero observations. -/
def Active (x : V → F) (A : V → V → Prop) (i j : V) : Prop :=
  A i j ∧ x i ≠ 0 ∧ x j ≠ 0

/-- Unsigned vertex readings and the squared sums selected by the incidence pattern. -/
def Same (A : V → V → Prop) (x y : V → F) : Prop :=
  (∀ i, x i ^ 2 = y i ^ 2) ∧
  ∀ ⦃i j⦄, A i j → (x i + x j)^2 = (y i + y j)^2

private theorem square_eq_iff (a b : F) : a^2 = b^2 ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    have he : (a-b) * (a+b) = 0 := by
      calc
        _ = a^2-b^2 := by ring
        _ = 0 := sub_eq_zero.mpr h
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · rintro (rfl | rfl) <;> ring

/-- All collisions in the projective readout are independent sign flips of the
active incidence components. Applies to arbitrary comparison graphs and any field
of characteristic different from two, not just the WSS alphabet. -/
private theorem same_iff_component_sign (h2 : (2:F) ≠ 0) (A : V → V → Prop) (x y : V → F) :
    Same A x y ↔
    ∃ s : V → F, (∀ i, s i = 1 ∨ s i = -1) ∧
      (∀ i, y i = s i * x i) ∧
      ∀ ⦃i j⦄, Relation.ReflTransGen (Active x A) i j → s i = s j := by
  classical
  constructor
  · rintro ⟨hsq, hpair⟩
    let s (i : V) := if x i = 0 then 1 else y i / x i
    have hyx (i : V) : y i = s i * x i := by
      by_cases hx : x i = 0
      · have h := (square_eq_iff _ _).mp (hsq i).symm
        rcases h with h | h <;> simp [s, hx, h]
      · simp [s, hx]
    have hs (i : V) : s i = 1 ∨ s i = -1 := by
      by_cases hx : x i = 0
      · simp [s,hx]
      · rcases (square_eq_iff _ _).mp (hsq i).symm with h | h
        · simp [s,hx,h]
        · exact Or.inr (by simp [s,hx,h])
    refine ⟨s,hs,hyx,?_⟩
    intro i j h
    induction h with
    | refl => rfl
    | tail hij he ih =>
      refine ih.trans ?_
      rename_i j k
      obtain ⟨ha,hj,hk⟩ := he
      have hh : (2:F) * (x j*x k-y j*y k) = 0 := by
        calc
          _ = ((x j+x k)^2-(y j+y k)^2) - (x j^2-y j^2) - (x k^2-y k^2) := by ring
          _ = 0 := by rw [hpair ha, hsq j, hsq k]; ring
      have hxy := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left h2)
      rw [hyx j, hyx k] at hxy
      have hp : (s j*s k) * (x j*x k) = 1 * (x j*x k) := by
        calc
          _ = (s j * x j) * (s k * x k) := by ring
          _ = x j * x k := hxy.symm
          _ = _ := by rw [one_mul]
      have hprod := mul_right_cancel₀ (mul_ne_zero hj hk) hp
      rcases hs j with hj'|hj' <;> rcases hs k with hk'|hk'
      · rw [hj',hk']
      · rw [hj',hk'] at hprod ⊢
        simpa using hprod.symm
      · rw [hj',hk'] at hprod ⊢
        simpa using hprod
      · rw [hj',hk']
  · rintro ⟨s,hs,hyx,hr⟩
    constructor
    · intro i
      rw [hyx]
      rcases hs i with h | h <;> rw [h] <;> ring
    · intro i j hA
      rw [hyx i,hyx j]
      by_cases hi : x i = 0
      · rw [hi]
        rcases hs j with h | h <;> rw [h] <;> ring
      by_cases hj : x j = 0
      · rw [hj]
        rcases hs i with h | h <;> rw [h] <;> ring
      rw [hr (Relation.ReflTransGen.single ⟨hA,hi,hj⟩)]
      rcases hs j with h | h <;> rw [h] <;> ring



/-- The signed row incidence of the path on n+1 vertices. -/
def derivative {n : ℕ} (c : Fin (n+1) → ZMod 3) (i : Fin n) : ZMod 3 :=
  c i.succ - c i.castSucc

def next {n : ℕ} (i j : Fin n) : Prop := j.val = i.val+1

/-- The five-mode ternary equality observations of consecutive triples, including
adjacent endpoints in words of length two. -/
def SameTriples {n : ℕ} (a b : Fin (n+1) → ZMod 3) : Prop :=
  ∀ i j, i.val < j.val → j.val ≤ i.val+2 → (a i = a j ↔ b i = b j)

private theorem sq_pair_iff : ∀ a b c d : ZMod 3,
    (a=b ↔ c=d) ↔ (b-a)^2=(d-c)^2 := by decide +kernel

private theorem sum_deriv {n : ℕ} (a : Fin (n+1) → ZMod 3) {i j : Fin n}
    (h : next i j) : derivative a i + derivative a j = a j.succ - a i.castSucc := by
  have h' : i.succ = j.castSucc := Fin.ext h.symm
  unfold derivative
  rw [h']
  ring

/-- Actual consecutive word observations coincide exactly when the signed
relative data coincide independently in every active path run. -/
private theorem triples_iff_run_sign {n : ℕ} (a b : Fin (n+1) → ZMod 3) :
    SameTriples a b ↔
      ∃ s : Fin n → ZMod 3, (∀ i, s i = 1 ∨ s i = -1) ∧
        (∀ i, derivative b i = s i * derivative a i) ∧
        ∀ ⦃i j⦄, Relation.ReflTransGen (Active (derivative a) next) i j → s i = s j := by
  rw [← same_iff_component_sign (by decide : (2 : ZMod 3) ≠ 0)]
  constructor
  · intro h
    constructor
    · intro i
      exact (sq_pair_iff _ _ _ _).mp (h i.castSucc i.succ (by simp)
        (by simp))
    · intro i j hij
      rw [sum_deriv _ hij, sum_deriv _ hij]
      have hh : j.val = i.val+1 := hij
      apply (sq_pair_iff _ _ _ _).mp
      apply h
      · simpa only [Fin.val_castSucc,Fin.val_succ,hh] using (show i.val < i.val+2 by omega)
      · simp only [Fin.val_castSucc,Fin.val_succ,hh]; omega
  · intro h i j hij hj
    have hij' : j.val = i.val+1 ∨ j.val = i.val+2 := by omega
    rcases hij' with ha | ha
    · let u : Fin n := ⟨i.val, by omega⟩
      have hi : u.castSucc=i := Fin.ext rfl
      have hj : u.succ=j := Fin.ext ha.symm
      have hq := h.1 u
      simp only [derivative, hi,hj] at hq
      exact (sq_pair_iff _ _ _ _).mpr hq
    · let u : Fin n := ⟨i.val, by omega⟩
      let v : Fin n := ⟨i.val+1, by omega⟩
      have hi : u.castSucc=i := Fin.ext rfl
      have hj : v.succ=j := Fin.ext ha.symm
      have hn : next u v := rfl
      have hq := h.2 hn
      rw [sum_deriv _ hn,sum_deriv _ hn,hi,hj] at hq
      exact (sq_pair_iff _ _ _ _).mpr hq


/-- A single observer records equality of two selected ternary entries. -/
def pairRead {n : ℕ} (b : Fin (n+1) → ZMod 3) (i j : Fin (n+1)) : Bool :=
  decide (b i = b j)

/-- Exactly the independent active-run orientations are lost when the
observers on consecutive triples read only pair equality. -/
theorem projective_cubic_word_recovery (n : ℕ) (a b : Fin (n+1) → ZMod 3) :
    (∀ (i j : Fin (n+1)), i.val < j.val → j.val ≤ i.val+2 →
      pairRead a i j = pairRead b i j) ↔
      ∃ s : Fin n → ZMod 3, (∀ i, s i = 1 ∨ s i = -1) ∧
        (∀ i, derivative b i = s i * derivative a i) ∧
        ∀ ⦃i j⦄, Relation.ReflTransGen (Active (derivative a) next) i j → s i = s j := by
  rw [← triples_iff_run_sign]
  constructor
  · intro h i j hi hj
    simpa [pairRead] using h i j hi hj
  · intro h i j hi hj
    simpa [pairRead] using h i j hi hj

#print axioms projective_cubic_word_recovery
end D5.S3.ConceptDynamics.DagSemantics.ProjectiveCubicWordRecovery
