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

end D5.S3.Geometry.KozakiKakei
