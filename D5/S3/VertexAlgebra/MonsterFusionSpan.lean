/- GID: D5/S3/VertexAlgebra/MonsterFusionSpan
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/MonsterFusionSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seven rank-three character sections span all sixty-four fusion labels. -/

/-
proof_shape: fusion_span_and_capacity: content
escape_witness: For each arbitrary target (g, xi), construct the residual
  character q after the three ground basis sections, then use the determinant
  carry directions to build six explicit coefficients mapping to that target.
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/VertexAlgebra/MonsterCharacterCarry.classification_and_carry.
-/

import D5.S3.VertexAlgebra.MonsterCharacterCarry
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.MonsterFusionSpan

open D5.S3.VertexAlgebra.MonsterCharacterCarry

abbrev Label := E × E

def unit (i : Fin 3) : E := fun j => if j = i then 1 else 0

private def u0 : E := unit 0
private def u1 : E := unit 1
private def u2 : E := unit 2
private def u012 : E := u0 + u1 + u2

/-- Coordinates of the sign character in the standard dual basis. -/
def ell (f : E → E → F) (g : E) : E := fun i => f g (unit i)

/-- The section of ground labels into six-bit defect-character labels. -/
def groundSection (f : E → E → F) (g : E) : Label := (g, ell f g)

private theorem basis_carries (f : E → E → F) (hf : IsSignTable f) :
    groundSection f u0 + groundSection f u1 + groundSection f (u0 + u1) = (0, u2) ∧
    groundSection f u0 + groundSection f u2 + groundSection f (u0 + u2) = (0, u1) ∧
    groundSection f u1 + groundSection f u2 + groundSection f (u1 + u2) = (0, u0) := by
  have hc := (classification_and_carry f hf).2.2.1
  constructor
  · apply Prod.ext
    · funext i
      change u0 i + u1 i + (u0 + u1) i = 0
      fin_cases i <;> decide
    · funext i
      have h := hc u0 u1 (unit i)
      change f u0 (unit i) + f u1 (unit i) + f (u0 + u1) (unit i) = u2 i
      rw [h]
      fin_cases i <;> decide
  constructor
  · apply Prod.ext
    · funext i
      change u0 i + u2 i + (u0 + u2) i = 0
      fin_cases i <;> decide
    · funext i
      have h := hc u0 u2 (unit i)
      change f u0 (unit i) + f u2 (unit i) + f (u0 + u2) (unit i) = u1 i
      rw [h]
      fin_cases i <;> decide
  · apply Prod.ext
    · funext i
      change u1 i + u2 i + (u1 + u2) i = 0
      fin_cases i <;> decide
    · funext i
      have h := hc u1 u2 (unit i)
      change f u1 (unit i) + f u2 (unit i) + f (u1 + u2) (unit i) = u0 i
      rw [h]
      fin_cases i <;> decide

private theorem coords (g : E) : g = g 0 • u0 + g 1 • u1 + g 2 • u2 := by
  funext i
  fin_cases i <;> simp [u0, u1, u2, unit, Pi.add_apply]

private theorem derived_span (f : E → E → F) (hf : IsSignTable f) (a : Label) :
    ∃ (c0 c1 c2 d0 d1 d2 : F),
      a = c0 • groundSection f u0 + c1 • groundSection f u1 +
        c2 • groundSection f u2 +
        d2 • (groundSection f u0 + groundSection f u1 + groundSection f (u0 + u1)) +
        d1 • (groundSection f u0 + groundSection f u2 + groundSection f (u0 + u2)) +
        d0 • (groundSection f u1 + groundSection f u2 + groundSection f (u1 + u2)) := by
  obtain ⟨g, ξ⟩ := a
  let β : E := g 0 • ell f u0 + g 1 • ell f u1 + g 2 • ell f u2
  let q : E := ξ + β
  refine ⟨g 0, g 1, g 2, q 0, q 1, q 2, ?_⟩
  obtain ⟨h01, h02, h12⟩ := basis_carries f hf
  rw [h01, h02, h12]
  apply Prod.ext
  · simpa [groundSection] using coords g
  · funext i
    have htwo : (2 : F) = 0 := by decide
    fin_cases i <;>
      simp [groundSection, β, q, ell, u0, u1, u2, unit, Pi.add_apply, Pi.smul_apply]
    <;> ring_nf <;> simp [htwo]

private theorem seven_relation (f : E → E → F) (hf : IsSignTable f) :
    groundSection f u0 + groundSection f u1 + groundSection f u2 +
      groundSection f (u0 + u1) + groundSection f (u0 + u2) +
      groundSection f (u1 + u2) + groundSection f u012 = 0 := by
  obtain ⟨b, ⟨hb, hrec⟩, _⟩ := (classification_and_carry f hf).2.1
  apply Prod.ext
  · funext i
    fin_cases i <;>
      simp only [groundSection, Prod.fst_add, Prod.fst_zero, Pi.add_apply, Pi.zero_apply]
      <;> decide
  · funext i
    fin_cases i <;>
      simp only [groundSection, ell, Prod.snd_add, Pi.add_apply]
    <;> rw [hrec u0, hrec u1, hrec u2, hrec (u0 + u1),
      hrec (u0 + u2), hrec (u1 + u2), hrec u012]
    <;> simp only [hb.left_add, u012]
    <;> simp [f0, u0, u1, u2, unit]
    <;> ring_nf
    <;> simp [show (4 : F) = 0 by decide, show (6 : F) = 0 by decide,
      show (10 : F) = 0 by decide, show (14 : F) = 0 by decide]

/- The six sections indexed by the nonzero vectors other than `u012`. -/
abbrev Six := F × F × F × F × F × F

def sixMap (f : E → E → F) (c : Six) : Label :=
  c.1 • groundSection f u0 + c.2.1 • groundSection f u1 +
    c.2.2.1 • groundSection f u2 + c.2.2.2.1 • groundSection f (u0 + u1) +
    c.2.2.2.2.1 • groundSection f (u0 + u2) +
      c.2.2.2.2.2 • groundSection f (u1 + u2)

private theorem six_surjective (f : E → E → F) (hf : IsSignTable f) :
    Function.Surjective (sixMap f) := by
  intro a
  obtain ⟨c0, c1, c2, d0, d1, d2, h⟩ := derived_span f hf a
  refine ⟨(c0 + d2 + d1, c1 + d2 + d0, c2 + d1 + d0, d2, d1, d0), ?_⟩
  rw [h]
  simp only [sixMap, add_smul, smul_add]
  abel

private theorem six_bijective (f : E → E → F) (hf : IsSignTable f) :
    Function.Bijective (sixMap f) := by
  apply (Fintype.bijective_iff_surjective_and_card (sixMap f)).2
  exact ⟨six_surjective f hf, by decide⟩

private def fiberEquiv (g : E) : {a : Label // a.1 = g} ≃ E where
  toFun a := a.1.2
  invFun ξ := ⟨(g, ξ), rfl⟩
  left_inv := by
    rintro ⟨⟨g', ξ⟩, hg⟩
    change g' = g at hg
    subst g'
    rfl
  right_inv := by intro ξ; rfl

/-- The seven nonzero ground sections generate the full six-bit label space;
their only nonzero relation uses all seven sections. This is a finite label
statement, with no assertion about realizing a VOA fusion rule. -/
theorem fusion_span_and_capacity (f : E → E → F) (hf : IsSignTable f) :
    Function.Bijective (sixMap f) ∧
    (groundSection f u0 + groundSection f u1 + groundSection f u2 +
      groundSection f (u0 + u1) + groundSection f (u0 + u2) +
      groundSection f (u1 + u2) + groundSection f u012 = 0) ∧
    (∀ (c : Six) (t : F), sixMap f c + t • groundSection f u012 = 0 ↔
      c = (t, t, t, t, t, t)) ∧
    Fintype.card Label = 64 ∧
    (∀ g : E, Fintype.card {a : Label // a.1 = g} = 8) ∧
    (∃ encode : E → Fin 8, Function.Bijective encode) ∧
    ¬ ∃ encode : E → Fin 4, Function.Injective encode := by
  have hrel := seven_relation f hf
  have hneg (a : Label) : -a = a := by
    apply Prod.ext <;> funext i <;> exact CharTwo.neg_eq _
  have hprefix : sixMap f (1, 1, 1, 1, 1, 1) = groundSection f u012 := by
    have h := (add_eq_zero_iff_eq_neg.mp hrel).trans (hneg _)
    simpa [sixMap] using h
  have hline (t : F) : sixMap f (t, t, t, t, t, t) = t • groundSection f u012 := by
    rw [← hprefix]
    simp only [sixMap, smul_add, one_smul]
  refine ⟨six_bijective f hf, hrel, ?_, by decide, ?_, ?_, ?_⟩
  · intro c t
    constructor
    · intro h
      apply (six_bijective f hf).1
      rw [hline]
      exact (add_eq_zero_iff_eq_neg.mp h).trans (hneg _)
    · intro h
      subst c
      rw [hline]
      exact add_eq_zero_iff_eq_neg.mpr (hneg _).symm
  · intro g
    calc
      Fintype.card {a : Label // a.1 = g} = Fintype.card E :=
        Fintype.card_congr (fiberEquiv g)
      _ = 8 := by decide
  · let e : E ≃ Fin 8 := Fintype.equivFinOfCardEq (by decide)
    exact ⟨e, e.bijective⟩
  · rintro ⟨encode, he⟩
    have hc := Fintype.card_le_of_injective encode he
    have hE : Fintype.card E = 8 := by decide
    simp [hE] at hc

end D5.S3.VertexAlgebra.MonsterFusionSpan
