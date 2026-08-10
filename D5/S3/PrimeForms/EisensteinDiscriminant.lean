/- GID: D5/S3/PrimeForms/EisensteinDiscriminant
   generality: G
   mirror-B: D5/B/S3/PrimeForms/EisensteinDiscriminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For B = −2(A+C), the binary quadratic forms in V at discriminant 4k are in bijection with the Eisenstein representations A²+AC+C² = k, so the incidence count equals the Eisenstein representation number. -/

import Mathlib

namespace D5.S3.PrimeForms.EisensteinDiscriminant

@[ext] structure BinaryQuadraticForm where
  a : ℤ
  b : ℤ
  c : ℤ

def BinaryQuadraticForm.discriminant (f : BinaryQuadraticForm) : ℤ :=
  f.b ^ 2 - 4 * f.a * f.c

def BinaryQuadraticForm.LiesInV (f : BinaryQuadraticForm) : Prop :=
  f.b = -2 * (f.a + f.c)

def eisensteinNorm (a c : ℤ) : ℤ := a ^ 2 + a * c + c ^ 2

def FormsAtDiscriminant (k : ℤ) :=
  {f : BinaryQuadraticForm // f.LiesInV ∧ f.discriminant = 4 * k}

def EisensteinRepresentations (k : ℤ) :=
  {p : ℤ × ℤ // eisensteinNorm p.1 p.2 = k}

def formToEisensteinRepresentation (k : ℤ) :
    FormsAtDiscriminant k → EisensteinRepresentations k := fun f => by
  refine ⟨(f.1.a, f.1.c), ?_⟩
  rcases f.2 with ⟨hb, hdisc⟩
  simp only [BinaryQuadraticForm.discriminant] at hdisc
  simp only [BinaryQuadraticForm.LiesInV] at hb
  simp only [eisensteinNorm]
  rw [hb] at hdisc
  nlinarith

def eisensteinRepresentationToForm (k : ℤ) :
    EisensteinRepresentations k → FormsAtDiscriminant k := fun p => by
  refine ⟨⟨p.1.1, -2 * (p.1.1 + p.1.2), p.1.2⟩, ?_⟩
  constructor
  · rfl
  · rcases p with ⟨⟨a, c⟩, hp⟩
    simp only [BinaryQuadraticForm.discriminant, eisensteinNorm] at hp ⊢
    nlinarith

theorem forms_biject_eisenstein_representations (k : ℤ) :
    Function.Bijective (formToEisensteinRepresentation k) := by
  have hleft : Function.LeftInverse
      (eisensteinRepresentationToForm k) (formToEisensteinRepresentation k) := by
    intro f
    apply Subtype.ext
    rcases f with ⟨⟨a, b, c⟩, hb, hdisc⟩
    simp only [BinaryQuadraticForm.LiesInV] at hb
    simp only [eisensteinRepresentationToForm, formToEisensteinRepresentation]
    ext <;> simp [hb]
  have hright : Function.RightInverse
      (eisensteinRepresentationToForm k) (formToEisensteinRepresentation k) := by
    intro p
    apply Subtype.ext
    rcases p with ⟨⟨a, c⟩, hp⟩
    rfl
  exact ⟨hleft.injective, hright.surjective⟩

end D5.S3.PrimeForms.EisensteinDiscriminant
