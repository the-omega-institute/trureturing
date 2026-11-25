/- GID: D5/S3/Quantum/Matrix/Schur/TwoHiddenScalarResponse
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/Schur/TwoHiddenScalarResponse
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Algebra.Field.Basic]
   utility: none
   digest: The four scalar coordinates of a two-hidden-site Schur response have an exact image. -/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Set.Defs
import Mathlib.Tactic.Ring

/-! The image of the scalar response with allowed nonsingular mixing parameters. -/

namespace D5.S3.Quantum.Matrix.Schur.TwoHiddenScalarResponse

variable {K : Type*} [Field K]

/-- For nonzero mixing, the zero edges between two nonzero edges are the obstructions. -/
private theorem nonzero_response_iff (t β γ ε ζ : K) (ht : t ≠ 0) (hdet : t * t ≠ 1) :
    (∃ a b d e f : K,
      β = -b * d * t ∧ γ = -d * (e + t * f) ∧
      ε = -a * (e + t * f) ∧ ζ = -b * (t * e + f)) ↔
    (β ≠ 0 ∨ γ = 0 ∨ ζ = 0) ∧ (γ ≠ 0 ∨ β = 0 ∨ ε = 0) := by
  constructor
  · rintro ⟨a, b, d, e, f, rfl, rfl, rfl, rfl⟩
    by_cases hd : d = 0
    · simp [hd]
    · by_cases hb : b = 0
      · simp [hb]
      · have hβ : -b * d * t ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hb) hd) ht
        by_cases hh : e + t * f = 0
        · exact ⟨Or.inl hβ, Or.inr (Or.inr (by rw [hh, mul_zero]))⟩
        · exact ⟨Or.inl hβ, Or.inl (mul_ne_zero (neg_ne_zero.mpr hd) hh)⟩
  · rintro ⟨left, right⟩
    -- Choose weights on the path k—b—d—h—a before recovering e and f.
    have weights : ∃ a b d h k : K,
        β = -b * d * t ∧ γ = -d * h ∧ ε = -a * h ∧ ζ = -b * k := by
      by_cases hβ : β = 0
      · by_cases hγ : γ = 0
        · exact ⟨-ε, 1, 0, 1, -ζ, by simp [hβ, hγ]⟩
        · have hζ : ζ = 0 := (left.resolve_left (fun h => h hβ)).resolve_left hγ
          exact ⟨-ε, 0, -γ, 1, 0, by simp [hβ, hζ]⟩
      · let b := -β / t
        have hb : b ≠ 0 := div_ne_zero (neg_ne_zero.mpr hβ) ht
        have hbβ : β = -b * 1 * t := by
          rw [mul_one, neg_mul]
          change β = -((-β / t) * t)
          rw [div_mul_cancel₀ _ ht, neg_neg]
        have hbζ : ζ = -b * (-ζ / b) := by
          rw [neg_mul, mul_comm b, div_mul_cancel₀ _ hb, neg_neg]
        by_cases hγ : γ = 0
        · have hε : ε = 0 := (right.resolve_left (fun h => h hγ)).resolve_left hβ
          exact ⟨0, b, 1, 0, -ζ / b, hbβ, by simp [hγ], by simp [hε], hbζ⟩
        · refine ⟨ε / γ, b, 1, -γ, -ζ / b, hbβ, by simp, ?_, hbζ⟩
          rw [neg_mul_neg, div_mul_cancel₀ _ hγ]
    obtain ⟨a, b, d, h, k, hβ, hγ, hε, hζ⟩ := weights
    have hden : 1 - t * t ≠ 0 := sub_ne_zero.mpr (Ne.symm hdet)
    let e := (h - t * k) / (1 - t * t)
    let f := k - t * e
    have he : e + t * f = h := calc
      e + t * f = e * (1 - t * t) + t * k := by dsimp only [f]; ring
      _ = h := by rw [div_mul_cancel₀ _ hden, sub_add_cancel]
    have hf : t * e + f = k := by dsimp only [f]; ring
    exact ⟨a, b, d, e, f, hβ, by rw [he]; exact hγ, by rw [he]; exact hε,
      by rw [hf]; exact hζ⟩

/-- A set of nonsingular mixing parameters realizes exactly the union of the zero and
nonzero mixing strata that it contains. -/
public theorem response_iff (T : Set K) (nonsingular : ∀ t ∈ T, t * t ≠ 1)
    (β γ ε ζ : K) :
    (∃ t ∈ T, ∃ a b d e f : K,
      β = -b * d * t ∧ γ = -d * (e + t * f) ∧
      ε = -a * (e + t * f) ∧ ζ = -b * (t * e + f)) ↔
    (0 ∈ T ∧ β = 0) ∨
    ((∃ t ∈ T, t ≠ 0) ∧
      (β ≠ 0 ∨ γ = 0 ∨ ζ = 0) ∧ (γ ≠ 0 ∨ β = 0 ∨ ε = 0)) := by
  constructor
  · rintro ⟨t, ht, a, b, d, e, f, hβ, hγ, hε, hζ⟩
    by_cases ht₀ : t = 0
    · exact Or.inl ⟨ht₀ ▸ ht, by simpa [ht₀] using hβ⟩
    · exact Or.inr ⟨⟨t, ht, ht₀⟩,
        (nonzero_response_iff t β γ ε ζ ht₀ (nonsingular t ht)).mp
          ⟨a, b, d, e, f, hβ, hγ, hε, hζ⟩⟩
  · rintro (⟨ht, hβ⟩ | ⟨⟨t, ht, ht₀⟩, hstrata⟩)
    · exact ⟨0, ht, -ε, 1, -γ, 1, -ζ, by simp [hβ]⟩
    · exact ⟨t, ht, (nonzero_response_iff t β γ ε ζ ht₀ (nonsingular t ht)).mpr hstrata⟩

#print axioms response_iff

end D5.S3.Quantum.Matrix.Schur.TwoHiddenScalarResponse
