/- GID: D5/S3/Geometry/KozakiKakeiConjecture13
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiConjecture13
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The allowable column permutations of the even frieze normal form are exactly the dihedral permutations outside order six. -/
import D5.S3.Geometry.KozakiKakeiFour
import D5.S3.Geometry.KozakiKakeiNormalization

namespace D5.S3.Geometry.KozakiKakei

/-- For each normalized input, the reordered columns have a unique matrix-equivalent
normalized representative exactly when the permutation preserves the written even-level locus. -/
theorem allowable_iff_preservesLevel {m : ℕ} (hm : 2 ≤ m) (σ : Equiv.Perm (Col m)) :
    Allowable hm σ ↔ PreservesLevel σ := by
  constructor
  · intro ha Z hZ hz
    obtain ⟨W, hW, hWZ⟩ := normalized_exists hm hZ hz
    have hpermW : evenProduct (reorder σ W) = oddProduct (reorder σ W) :=
      (normalized_representative_iff hm _ (reorder_admissible σ hW.1)).mp (ha W hW)
    exact (level_equiv (reorder_equiv σ hWZ)).mp hpermW
  · intro hp Z hZ
    exact (normalized_representative_iff hm _ (reorder_admissible σ hZ.1)).mpr
      (hp Z hZ.1 (normalized_level hZ))

/-- Kozaki–Kakei, *Coxeter Group Symmetries of Frieze Patterns*, arXiv:2611.25785v1,
§3, Conjecture 13, in the finite group of all column permutations. -/
theorem conjecture_13 {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3) (σ : Equiv.Perm (Col m)) :
    Allowable hm σ ↔ Dihedral σ := by
  rw [allowable_iff_preservesLevel hm σ]
  exact ⟨dihedral_of_preservesLevel hm hm3 σ, dihedral_preservesLevel hm σ⟩

theorem preservesLevel_iff_dihedral {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (σ : Equiv.Perm (Col m)) : PreservesLevel σ ↔ Dihedral σ :=
  (allowable_iff_preservesLevel hm σ).symm.trans (conjecture_13 hm hm3 σ)

noncomputable def fourNormal : Chart K 2 := !![0, 1, 1, 1; -1, 0, 1, 2]

theorem normalized_four_iff (Z : Chart K 2) :
    Normalized (by decide : 2 ≤ 2) Z ↔ Z = fourNormal := by
  constructor
  · rintro ⟨_, h₀₀, h₁₀, h₀₁, h₁₁, h₀₂, h₁₂, ha, hl⟩
    have htop : Z 0 (3 : Col 2) = 1 := by
      change minor Z (0 : Col 2) (3 : Col 2) = 1 at hl
      change Z 0 (0 : Col 2) = 0 at h₀₀
      change Z 1 (0 : Col 2) = -1 at h₁₀
      simpa [minor, h₀₀, h₁₀] using hl
    have hbot : Z 1 (3 : Col 2) = 2 := by
      have h := ha (2 : Col 2) (by decide)
      change minor Z (2 : Col 2) (3 : Col 2) = 1 at h
      change Z 0 (2 : Col 2) = 1 at h₀₂
      change Z 1 (2 : Col 2) = 1 at h₁₂
      rw [minor, h₀₂, h₁₂, htop, one_mul, one_mul, sub_eq_iff_eq_add] at h
      simpa only [one_add_one_eq_two] using h
    ext a i
    fin_cases a <;> fin_cases i
    all_goals
      first | exact h₀₀ | exact h₁₀ | exact h₀₁ | exact h₁₁ |
        exact h₀₂ | exact h₁₂ | exact htop | exact hbot
  · rintro rfl
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro i j h
      fin_cases i <;> fin_cases j
      all_goals
        first
        | exact (h rfl).elim
        | norm_num [fourNormal, minor, Matrix.cons_val', Matrix.empty_val']
    · intro i hi
      fin_cases i
      all_goals
        first
        | exact (Nat.lt_irrefl 4 hi).elim
        | norm_num [fourNormal, minor, Matrix.cons_val', Matrix.empty_val']
    · norm_num [fourNormal, minor, first, last, Matrix.cons_val', Matrix.empty_val']

private def fourPerm (reflect : Bool) (a : Col 2) : Equiv.Perm (Col 2) :=
  if reflect then
    { toFun := fun i => a - i
      invFun := fun i => a - i
      left_inv := fun i => by fin_cases a <;> fin_cases i <;> rfl
      right_inv := fun i => by fin_cases a <;> fin_cases i <;> rfl }
  else
    { toFun := fun i => a + i
      invFun := fun i => i - a
      left_inv := fun i => by fin_cases a <;> fin_cases i <;> rfl
      right_inv := fun i => by fin_cases a <;> fin_cases i <;> rfl }

private theorem fourPerm_dihedral (b : Bool) (a : Col 2) : Dihedral (fourPerm b a) := by
  refine ⟨a, ?_⟩
  cases b
  · exact Or.inl (fun _ => rfl)
  · exact Or.inr (fun _ => rfl)

private theorem fourPerm_zero (b : Bool) (a : Col 2) : fourPerm b a 0 = a := by
  cases b <;> simp [fourPerm]

/-- Eight permutations act on the four-column normal forms, even though their carrier is a
singleton. This cardinality counts permutations of the columns in (S_4). -/
theorem allowable_four_card :
    Nat.card {σ : Equiv.Perm (Col 2) // Allowable (by decide : 2 ≤ 2) σ} = 8 := by
  let hm : 2 ≤ 2 := le_rfl
  let f (p : Bool × Col 2) : {σ : Equiv.Perm (Col 2) // Allowable hm σ} :=
    ⟨fourPerm p.1 p.2, (conjecture_13 hm (by decide) _).mpr (fourPerm_dihedral p.1 p.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨b, a⟩ ⟨b', a'⟩ h
      have he : fourPerm b a = fourPerm b' a' := congrArg Subtype.val h
      have ha : a = a' := (fourPerm_zero b a).symm.trans
        ((congrArg (fun p : Equiv.Perm (Col 2) => p 0) he).trans (fourPerm_zero b' a'))
      subst a'
      have henne : a + (1 : Col 2) ≠ a - 1 := by
        rw [sub_eq_add_neg]
        exact fun hh => (by decide : (1 : Col 2) ≠ -(1 : Col 2)) (add_left_cancel hh)
      have h1 := congrArg (fun σ : Equiv.Perm (Col 2) => σ 1) he
      cases b <;> cases b'
      · rfl
      · exact (henne h1).elim
      · exact (henne h1.symm).elim
      · rfl
    · rintro ⟨σ, hσ⟩
      obtain ⟨a, ha | ha⟩ := (conjecture_13 hm (by decide) σ).mp hσ
      · exact ⟨(false, a), Subtype.ext (Equiv.ext (fun i => (ha i).symm))⟩
      · exact ⟨(true, a), Subtype.ext (Equiv.ext (fun i => (ha i).symm))⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  decide

#print axioms allowable_iff_preservesLevel
#print axioms conjecture_13
#print axioms preservesLevel_iff_dihedral
#print axioms normalized_four_iff
#print axioms allowable_four_card

end D5.S3.Geometry.KozakiKakei
