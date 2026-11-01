/- GID: D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Perfect classical six-leg circuits have perfect two-wire factors. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization

universe u v

/-- Every selection of distinct columns contains every tuple exactly once. With
`|R| = |X|^s`, this is the source's strength-`s` orthogonal array with `D^s` rows. -/
def IsIndexOneOA {r : Type v} {x : Type u} [Fintype r] [Fintype x] {c : ℕ}
    (rows : r → Fin c → x) (s : ℕ) : Prop :=
  ∀ cols : Fin s → Fin c, Function.Injective cols →
    Function.Bijective (fun t => fun i => rows t (cols i))

/-- The four columns are the two input and two output symbols of the gate. -/
def gateGraph {x : Type u} (f : x × x → x × x) (t : x × x) : Fin 4 → x :=
  ![t.1, t.2, (f t).1, (f t).2]

/-- Apply the gates on wires `(1,2)`, `(1,3)`, and `(2,3)`, respectively. -/
def circuit {x : Type u} (a b c : x × x → x × x) (t : x × x × x) : x × x × x :=
  let ab := a (t.1, t.2.1)
  let pc := b (ab.1, t.2.2)
  let qr := c (ab.2, pc.2)
  (pc.1, qr.1, qr.2)

/-- The graph has columns `(x,y,z,p,q,r)` in the source's wire convention. -/
def circuitGraph {x : Type u} (a b c : x × x → x × x)
    (t : x × x × x) : Fin 6 → x :=
  ![t.1, t.2.1, t.2.2, (circuit a b c t).1,
    (circuit a b c t).2.1, (circuit a b c t).2.2]

/-- The nonlinear six-leg classical factorization assertion. -/
def claim : Prop :=
  ∀ (x : Type u) [Fintype x] [DecidableEq x] (a b c : x × x → x × x),
    IsIndexOneOA (circuitGraph a b c) 3 →
      IsIndexOneOA (gateGraph a) 2 ∧ IsIndexOneOA (gateGraph b) 2 ∧
        IsIndexOneOA (gateGraph c) 2

private def IsLatin {x : Type u} (f : x × x → x) : Prop :=
  (∀ t, Function.Bijective (fun s => f (s, t))) ∧
    (∀ s, Function.Bijective (fun t => f (s, t)))

private theorem oa_injective {r : Type v} {x : Type u} [Fintype r] [Fintype x]
    {n : ℕ} {rows : r → Fin n → x} (h : IsIndexOneOA rows 3)
    (i j k : Fin n) (hc : Function.Injective ![i, j, k]) {s t : r}
    (hi : rows s i = rows t i) (hj : rows s j = rows t j)
    (hk : rows s k = rows t k) : s = t := by
  sorry

private theorem oa_surjective {r : Type v} {x : Type u} [Fintype r] [Fintype x]
    {n : ℕ} {rows : r → Fin n → x} (h : IsIndexOneOA rows 3)
    (i j k : Fin n) (hc : Function.Injective ![i, j, k]) (a b c : x) :
    ∃ t, rows t i = a ∧ rows t j = b ∧ rows t k = c := by
  sorry

private theorem gate_perfect {x : Type u} [Fintype x] (f : x × x → x × x)
    (hf : Function.Bijective f) (h₁ : IsLatin (fun t => (f t).1))
    (h₂ : IsLatin (fun t => (f t).2)) : IsIndexOneOA (gateGraph f) 2 := by
  sorry

private theorem factors_bijective {x : Type u} [Fintype x] [Nonempty x]
    (a b c : x × x → x × x) (h : IsIndexOneOA (circuitGraph a b c) 3) :
    Function.Bijective a ∧ Function.Bijective b ∧ Function.Bijective c := by
  sorry

private theorem first_latin {x : Type u} [Fintype x] [Nonempty x]
    (a b c : x × x → x × x) (h : IsIndexOneOA (circuitGraph a b c) 3)
    (ha : Function.Bijective a) :
    IsLatin (fun t => (a t).1) ∧ IsLatin (fun t => (b t).1) := by
  sorry

private theorem second_latin {x : Type u} [Fintype x] [Nonempty x]
    (a b c : x × x → x × x) (h : IsIndexOneOA (circuitGraph a b c) 3)
    (ha : Function.Bijective a) (hc : Function.Bijective c)
    (h₁ : IsLatin (fun t => (a t).1)) :
    IsLatin (fun t => (a t).2) ∧ IsLatin (fun t => (b t).2) := by
  sorry

private theorem last_latin {x : Type u} [Fintype x] [Nonempty x]
    (a b c : x × x → x × x) (h : IsIndexOneOA (circuitGraph a b c) 3)
    (ha : Function.Bijective a) (h₂ : IsLatin (fun t => (b t).2)) :
    IsLatin (fun t => (c t).1) ∧ IsLatin (fun t => (c t).2) := by
  sorry

/-- All factors of an index-one strength-three classical circuit are perfect. -/
theorem result : claim := by
  intro x _ _ a b c h
  by_cases hn : Nonempty x
  · letI := hn
    obtain ⟨ha, hb, hc⟩ := factors_bijective a b c h
    obtain ⟨ha₁, hb₁⟩ := first_latin a b c h ha
    obtain ⟨ha₂, hb₂⟩ := second_latin a b c h ha hc ha₁
    obtain ⟨hc₁, hc₂⟩ := last_latin a b c h ha hb₂
    exact ⟨gate_perfect a ha ha₁ ha₂, gate_perfect b hb hb₁ hb₂,
      gate_perfect c hc hc₁ hc₂⟩
  · haveI : IsEmpty x := not_nonempty_iff.mp hn
    have he (f : x × x → x × x) : IsIndexOneOA (gateGraph f) 2 := by
      intro cols _
      exact ⟨fun t => isEmptyElim t.1, fun t => isEmptyElim (t 0)⟩
    exact ⟨he a, he b, he c⟩

end D5.S3.Combinatorics.Latin.ClassicalPerfectTensorFactorization
