import GRH.Lib.ClassField.Places.AdeleNorm
import GRH.Lib.ClassField.HeckeCharacter.CharacterDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Rational and tame-level points of U(1); finiteness of its ray class group. -/

noncomputable section

open Subgroup

variable {E : Type _} [Field E] [CMType E]
  (S : Finset (FinPlace E))

/-- The subgroup of rational points of U(1)(𝔸): the adeles u with uū = 1 that come from E. -/
def rationalU1 :=
  mk (.comap (unitary (𝔸 E)).subtype toAdele.range.1.1) (.imp' star (star_toAdele · ▸ congrArg _))

/-- For a set S of finite places, the subgroup of U(1)(𝔸) of elements whose finite part is
integral and congruent to 1 modulo every place of S. -/
def integralU1 {E : Type _} [Field E] [NumberField E] [NumberField.IsCMField E]
    (S : Finset (FinPlace E)) :=
  ofDiv {u : unitary (𝔸 E) | ∃ h, ∀ w ∈ S, reduceAt w ⟨u.1.2, h⟩ = 1} ⟨1,
  one_mem _, by tauto⟩ fun _ ⟨a, _⟩ v ⟨b, _⟩ ↦ have := mul_mem a (star_mem_Ô b)
  ⟨this, fun w _ ↦ by simpa [v.2.1, *, mul_assoc, ← Prod.snd_mul,
    ← Prod.snd_star] using! (map_mul (reduceAt w) ⟨_, this⟩ ⟨_, b⟩).symm⟩

lemma isOpen_integralU1 : (integralU1 S).IsOpen := by
  simp [integralU1, ← (reduceAt _).map_one, ← RingHom.sub_mem_ker_iff, ↓reduceAt_eq_zero, -map_one]
  exact (isOpen_Ô.inter ((isOpen_set_pi (by simp) fun _ _ ↦ isOpen_v_lt ..).preimage
    (.sub (by fun_prop) continuous_one))).preimage_of_continuous

lemma mem_integralU1_of_snd_eq_one (u : unitary (𝔸 E)) {S} : u.1.2 = 1 → u ∈ integralU1 S :=
  (⟨by simp [·], by aesop⟩)

open NumberField IsCMField

/-- Hilbert 90 for finite ideles: for every norm-one adele u of the CM field E there is a finite
idele y such that the finite part of u equals y/ȳ. -/
lemma exists_divStar (u : unitary (𝔸 E)) : ∃ y, (u / divStar (finIdeleIncl y)).1.2 = 1 :=
  have ⟨_, a, h⟩ := hilbert90_finite_idele (σ := complexConj E) (u := u.1.2) (by
    simpa [orderOf_complexConj, Finset.range, AlgEquiv.aut_one] using! congr($(u.2.1).2))
  ⟨a.unit, by erw [Prod.snd_mul, Prod.snd_star, star_mul', ← mul_assoc, h]; simp⟩

/-- Reduction modulo w: the homomorphism from the elements of U(1)(𝔸) with integral finite part
to the multiplicative group of the residue field at w. -/
def reduceU1 {E : Type _} [Field E] [NumberField E] [NumberField.IsCMField E] (w : FinPlace E) :=
  ((reduceAt w).1.comp ⟨⟨fun u : integralU1 ∅ ↦ ⟨_, u.2.1⟩, rfl⟩, by simp⟩).toHomUnits

/-- The class group of `U(1)` of tame level `S` is finite. -/
instance finite_u1_classGroup :
  Finite (_ ⧸ rationalU1 ⊔ integralU1 S) := let f := divStar.1.comp finIdeleIncl
  have := finiteIndex_idele_subgroup_of_isOpen ((rationalU1 ⊔ _).comap f) ((isOpen_mono le_sup_right
    (isOpen_integralU1 S)).preimage (divStar.2.comp (.units_map _ (.prodMk_right 1)))) fun x _ ↦
    mem_sup.2 ⟨divStar (x.map _), (RingHom.range _).mul_mem ⟨x, rfl⟩ (by simp), _,
    mem_integralU1_of_snd_eq_one _ (divStar _).2.2, mul_div_cancel ..⟩
  .of_surjective (QuotientGroup.map _ _ f le_rfl) (Quot.ind (exists_divStar · |>.imp' (↑) fun y h ↦
    (QuotientGroup.eq_iff_div_mem.2 (mem_sup_right (mem_integralU1_of_snd_eq_one _ h))).symm))
