/- GID: D5/S1/Words/Palindromes/PeriodDoubling/CanonicalSignedDigits
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/CanonicalSignedDigits
   mirror-E: none(waiver:nonadjacent-digit-uniqueness-induction)
   anchors: []
   utility: none
   digest: A nonadjacent signed binary expansion is unique at every fixed digit length. -/

/-
proof_shape: content (nonadjacent_digits_unique)
escape_witness: Modulo-four rigidity determines each nonzero digit, followed by digit induction.
admission_basis: escape-witness
Direct frozen dependencies: none.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.List.Chain
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

/-- Equal-length sparse signed binary expansions with equal value have identical digits. -/
theorem nonadjacent_digits_unique (digits other : List ℤ)
    (hd : ∀ z ∈ digits, z = -1 ∨ z = 0 ∨ z = 1)
    (he : ∀ z ∈ other, z = -1 ∨ z = 0 ∨ z = 1)
    (hnd : digits.IsChain (fun a b => a = 0 ∨ b = 0))
    (hne : other.IsChain (fun a b => a = 0 ∨ b = 0))
    (hlen : digits.length = other.length)
    (hvalue : digits.foldr (fun z x => z + 2*x) 0 = other.foldr (fun z x => z+2*x) 0) :
    digits = other := by
  have evenTail (d : ℤ) (ds : List ℤ)
      (hc : (d::ds).IsChain (fun a b => a=0 ∨ b=0)) (hd : d ≠ 0) :
      ds.foldr (fun z x => z+2*x) 0 % 2 = 0 := by
    cases ds with
    | nil => simp
    | cons a ds =>
      have hh := (List.isChain_cons_cons.mp hc).1
      have ha : a = 0 := hh.resolve_left hd
      simp only [List.foldr_cons, ha]
      omega
  induction digits generalizing other with
  | nil =>
    have ho : other = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    exact ho.symm
  | cons d ds ih =>
    cases other with
    | nil => simp at hlen
    | cons e es =>
      have hd0 := hd d (by simp)
      have he0 := he e (by simp)
      have hpd := evenTail d ds hnd
      have hpe := evenTail e es hne
      have hv : d+2*ds.foldr (fun z x => z+2*x) 0 = e+2*es.foldr (fun z x => z+2*x) 0 := hvalue
      have hde : d = e := by
        rcases hd0 with hd0 | hd0 | hd0 <;>
          rcases he0 with he0 | he0 | he0 <;> subst d <;> subst e <;> omega
      subst e
      have htail : ds.foldr (fun z x => z+2*x) 0 = es.foldr (fun z x => z+2*x) 0 := by omega
      have hl : ds.length = es.length := by simpa using hlen
      have hd' : ∀ z ∈ ds, z=-1 ∨ z=0 ∨ z=1 := fun z hz => hd z (by simp [hz])
      have he' : ∀ z ∈ es, z=-1 ∨ z=0 ∨ z=1 := fun z hz => he z (by simp [hz])
      exact congrArg (List.cons d) (ih es hd' he' hnd.tail hne.tail hl htail)

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.nonadjacent_digits_unique
