/- GID: D5/S3/Combinatorics/CayleySumCodes/CentralizingInvolutionTranslation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/CentralizingInvolutionTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A centralizing involution preserves total perfect codes under translation in the same sum graph. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.CentralizingInvolutionTranslation

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

variable {G : Type*} [Group G]

private theorem translate_twice (b : G) (hb : b * b = 1) (g : G) :
    (g * b) * b = g := by
  rw [mul_assoc, hb, mul_one]

private theorem incidence (C : Set G) (Y : Set G) (hY : NormalSubset Y)
    (b : G) (hb : b * b = 1) (hc : ∀ h ∈ C, b * h = h * b)
    (g h : G) (hh : h ∈ C) :
    (sumGraph Y hY).Adj (g * b) h ↔ (sumGraph Y hY).Adj g (h * b) := by
  have prod : (g * b) * h = g * (h * b) := by
    rw [mul_assoc, hc h hh]
  have distinct : g * b ≠ h ↔ g ≠ h * b := by
    constructor
    · intro hn he
      apply hn
      rw [he, translate_twice b hb h]
    · intro hn he
      apply hn
      rw [← he, translate_twice b hb g]
  exact and_congr distinct (by rw [prod])

private theorem forward (C : Set G) (Y : Set G) (hY : NormalSubset Y)
    (b : G) (hb : b * b = 1) (hc : ∀ h ∈ C, b * h = h * b)
    (hC : IsTotalPerfectCode (sumGraph Y hY) C) :
    IsTotalPerfectCode (sumGraph Y hY) ((fun h => h * b) '' C) := by
  intro g
  obtain ⟨h, ⟨hh, he⟩, hu⟩ := hC (g * b)
  refine ⟨h * b, ⟨⟨h, hh, rfl⟩, (incidence C Y hY b hb hc g h hh).mp he⟩, ?_⟩
  rintro y ⟨⟨h', hh', rfl⟩, he'⟩
  have eqh : h' = h := hu h' ⟨hh', (incidence C Y hY b hb hc g h' hh').mpr he'⟩
  exact congrArg (fun x => x * b) eqh

/-- Right translation by an involution centralizing the code preserves total
perfect coding in the same simple sum graph. No normalizer-only claim or
change of connection set is used. The statement holds for every finite group,
and in fact does not need finiteness. -/
theorem result (C : Set G) (Y : Set G) (hY : NormalSubset Y)
    (b : G) (hb : b * b = 1) (hc : ∀ h ∈ C, b * h = h * b) :
    IsTotalPerfectCode (sumGraph Y hY) C ↔
      IsTotalPerfectCode (sumGraph Y hY) ((fun h => h * b) '' C) := by
  constructor
  · exact forward C Y hY b hb hc
  · intro hT
    have ht : ∀ h ∈ ((fun h => h * b) '' C), b * h = h * b := by
      rintro _ ⟨h, hh, rfl⟩
      calc
        b * (h * b) = (b * h) * b := (mul_assoc _ _ _).symm
        _ = (h * b) * b := by rw [hc h hh]
    have twice : (fun h => h * b) '' ((fun h => h * b) '' C) = C := by
      ext h
      constructor
      · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        simpa [translate_twice b hb] using hg
      · intro hh
        exact ⟨h * b, ⟨h, hh, rfl⟩, translate_twice b hb h⟩
    simpa only [twice] using forward ((fun h => h * b) '' C) Y hY b hb ht hT

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.CentralizingInvolutionTranslation
