import GRH.Lib.Adelic.Adeles.AdeleTopology
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus
(known result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Idempotents of sets of places, reduction maps, conjugation on integral finite adeles. -/

open NumberField RestrictedProduct Valued StarSubsemiring Ideal


variable {E : Type*} [Field E] [NumberField E] (S : Set (FinPlace E)) (x y : 𝔸f E) (w : FinPlace E)

@[simp] lemma finAdele_add_apply : (x + y) w = x w + y w := rfl

@[simp] lemma finAdele_sub_apply : (x - y) w = x w - y w := rfl

@[simp] lemma finAdele_neg_apply : (-x) w = -x w := rfl

@[simp] lemma finAdele_one_apply : (1 : 𝔸f E) w = 1 := rfl

@[simp] lemma finAdele_pow_apply k : (x ^ k) w = x w ^ k := rfl

@[simp] lemma finAdele_natCast_apply (k : ℕ) : (k : 𝔸f E) w = k := rfl

@[simp] lemma finAdele_zero_apply : (0 : 𝔸f E) w = 0 := rfl

lemma v_inv (x : (𝔸f E)ˣ) : x⁻¹.1 w = (x.1 w)⁻¹ ∧ x.1 w ≠ 0 := by
    simp [← evalAt_apply, x.isUnit.map _ |>.ne_zero]

/-- The finite adele with component 1 at the places in S and 0 at the other places. -/
noncomputable def idem : 𝔸f E := ⟨(if · ∈ S then 1 else 0), by simp [ite_mem]⟩

@[simp] lemma reduceAt_algebraMap x : reduceAt w (algebraMap (𝓞 E) _ x) = algebraMap _ _ x := rfl

@[local simp] lemma idem_apply : idem S w = ite (w ∈ S) 1 0 := rfl

@[simp] lemma idem_mem_Ô : idem S ∈ Ô E := by aesop_cat

@[simp] lemma reduceAt_idem : reduceAt w ⟨_, idem_mem_Ô S⟩ = ite (w ∈ S) 1 0 := by
  split <;> congrm ⟦⟨$(by simpa), _⟩⟧

lemma idem_mul_self : idem S * idem S = idem S := by aesop

lemma idem_compl : idem Sᶜ = 1 - idem S := by aesop

lemma exists_idele_eq_uniformizer_zpow (d : _ → ℤ) (hd : d.HasFiniteSupport) : ∃ x : (𝔸f E)ˣ, ∀ w,
  x.1 w = ↑((uniformizer w)⁻¹ ^ d w) := ⟨mkUnit _ (hd.subset (by aesop_cat)), fun _ ↦ rfl⟩

variable {S x w}

@[simp] lemma idem_of_mem : w ∈ S → idem S w = 1 := (ite_eq_left ·)

@[simp] lemma idem_of_notMem : w ∉ S → idem S w = 0 := (ite_eq_right ·)

lemma idem_mul_mem_Ô : idem S * x ∈ Ô E ↔ ∀ w ∈ S, v (x w) ≤ 1 := by simp [Ô, ite_mem]; rfl

@[simp] lemma reduceAt_eq_zero {x} : reduceAt w x = 0 ↔ v (x.1 w) < 1 :=
  sub_zero (x.1 w) ▸ residue_eq_iff_valuation_sub_lt_one

@[simp] lemma isUnit_Ô {x : Ô E} : IsUnit x ↔ ∀ w, v (x.1 w) = 1 := by simp [isUnit_iff_dvd_one,
  dvd_def, Subtype.ext_iff, exists_eq_mul_iff_v_le, le_antisymm_iff, mem_Ô.1]

variable [IsCMField E] (x : 𝔸f E) (w : FinPlace E)

noncomputable instance : StarRing (Ô E) := starRing ⟨_, star_mem_Ô⟩

@[simp, norm_cast] lemma coe_star_Ô x : (star x : Ô E) = star x.1 := rfl

@[simp] lemma v_star_apply : v (star x w) = v (x (star w)) := by simp

@[simp] lemma q_star : (star w).q = w.q :=
  Nat.card_congr (quotientEquiv _ _ _ (comap_symm starRingAut)).1.symm

lemma star_idem S : star (idem S : 𝔸f E) = idem (star ⁻¹' S) := by aesop

lemma star_singleAdele {u w : FinPlace E} h x : star (singleAdele u x) =
  singleAdele w (conjLoc h x) := by cases h ▸ star_star u; ext v; by_cases v = w <;> aesop
