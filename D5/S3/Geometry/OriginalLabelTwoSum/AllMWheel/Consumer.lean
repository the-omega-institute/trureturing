/- GID: D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/Consumer
   generality: G
   digest: Constructed all-width local fillings and Gamma run the existing
           original-label parent compiler and literal indexed row transport.
   SOURCE_ONLY_UNCOMPILED. No physical-graph or all-plane theorem is claimed. -/
import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.Core

noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
open OriginalLabelTwoSum FiniteElementaryCollapse FiniteRelativeSimplicialCollapse

variable {V : Type*} [Fintype V] [DecidableEq V]

private def retarget {W : Finset V} {A B : Family V} (g : Filling W A)
    (h : A = B) : Filling W B where
  empty_mem := h ▸ g.empty_mem
  collar := g.collar
  critical := g.critical
  contains := by rw [← h]; exact g.contains
  supported := g.supported
  critical_supported := g.critical_supported
  cells := g.cells
  main := g.main
  separate := g.separate.cast rfl (congrArg project h)

private theorem interfaces (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) :
    (tailGround m hm).image f = (ground m).image f \ (rim m hm).image f ∧
    renameFamily f (A0 m hm) = renameFamily f (pathRoot m hm) ⊓ delta ((tailGround m hm).image f) ∧
    renameFamily f (A1 m hm) = renameFamily f (pathRoot m hm) ⊔ delta ((tailGround m hm).image f) := by
  refine ⟨Finset.image_sdiff _ _ f.injective, ?_, ?_⟩
  · change renameFamily f (pathRoot m hm ⊓ delta (tailGround m hm)) = _
    rw [(rename_operations f (tailGround m hm) (pathRoot m hm)
      (delta (tailGround m hm)) ∅).2.2.1,
      (rename_operations f (tailGround m hm) (pathRoot m hm) (pathRoot m hm) ∅).1]
  · change renameFamily f (pathRoot m hm ⊔ delta (tailGround m hm)) = _
    rw [(rename_operations f (tailGround m hm) (pathRoot m hm)
      (delta (tailGround m hm)) ∅).2.1,
      (rename_operations f (tailGround m hm) (pathRoot m hm) (pathRoot m hm) ∅).1]

private theorem fresh_zero (m : Nat) (f : Label m ↪ V) : f 0 ∉ (ground m).image f := by
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hz : i = 0 := f.injective he
  subst i
  exact (Finset.mem_erase.mp hi).1 rfl

private theorem rim_subset (m : Nat) (hm : 3 ≤ m) : rim m hm ⊆ ground m := by
  intro x hx
  rcases (show x = firstLabel m hm ∨ x = secondLabel m hm by simpa [rim] using hx)
    with rfl | rfl <;> simp [ground, firstLabel, secondLabel]

/-- The actual original indexed wheel supplies the existing Rows.root
    certificate input. Its main and separate lists come from the constructed
    local filling and E-core collapse, with no certificate premise. -/
def rimRowCertificate (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :
    Certificate (rimRows m (by omega)).ground (rimRows m (by omega)).root := by
  change Certificate (ground m) (wheelRoot m (by omega))
  rw [wheelRoot_eq_A1 m hm]
  exact wheelCertificate m hm hg

/-- Run the existing parent compiler. The left certificate is its ORIGINAL
    legitimate input; neither local filling, Gamma, Cout nor the desired
    parent certificate is a premise. The e=current-core-vertex case is allowed. -/
def oneStep (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Label m ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f)) :
    Certificate (X ∪ (ground m).image f)
      (parentOf X ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) K) := by
  let g0 := retarget (renameFilling f (fill0 m hm)) (interfaces m hm f).2.1
  let g1 := retarget (renameFilling f (fill1 m hm)) (interfaces m hm f).2.2
  let G := (renameSequence f (gammaGood m hm hg)).cast
    (by rw [← project_rename,
      (rename_operations f (ground m) (pathRoot m hm) (pathRoot m hm) ∅).1])
    (project_rename f (pathRoot m hm)).symm
  have heY : e ∉ (ground m).image f := hf0 ▸ fresh_zero m f
  have hR := Finset.image_subset_image (f := (f : Label m → V)) (rim_subset m hm)
  have hRne : ((rim m hm).image f).Nonempty :=
    Finset.image_nonempty.mpr ⟨firstLabel m hm, by simp [rim]⟩
  have hE : Supported ((ground m).image f) (renameFamily f (pathRoot m hm)) := by
    rintro s ⟨t, ht, rfl⟩
    exact Finset.image_subset_image
      (((rimRows m (by omega)).without (interfaceRow m hm)).root_supported t ht)
  exact compileParent c g0 g1 heX heY hXY hR hRne (interfaces m hm f).1 hE (Or.inl ⟨G⟩)

theorem oneStep_critical (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Label m ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hXY : Disjoint X ((ground m).image f)) :
    (oneStep m hm hg c f hf0 heX hXY).critical = parentCritical e c.critical
      ((fill0 m hm).critical.image (fun s => s.image f))
      ((fill1 m hm).critical.image (fun s => s.image f)) := by
  rfl

/-- Actual indexed row substitution, with m=wheel width and no history-length
    parameter conflated with it. All retained original labels and ghosts stay. -/
def appendRimRows (r : Rows V) (e : V) (he : e ∈ r.ground)
    (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) (hf0 : f 0 = e) : Rows V :=
  transportedRows (r.ground.erase e) ((ground m).image f) e ((rim m hm).image f)
    r (renameRows f (rimRows m (by omega))) (interfaceRow m hm)
    (Finset.insert_erase he).symm rfl (by simp) (hf0 ▸ fresh_zero m f)
    (Finset.image_subset_image (rim_subset m hm))

private theorem append_root (r : Rows V) (e : V) (he : e ∈ r.ground)
    (m : Nat) (hm : 3 ≤ m) (f : Label m ↪ V) (hf0 : f 0 = e)
    (hnew : Disjoint r.ground ((ground m).image f)) :
    (appendRimRows r e he m hm f hf0).root =
      parentOf (r.ground.erase e) ((ground m).image f) ((tailGround m hm).image f) e
        (renameFamily f (pathRoot m hm)) r.root := by
  have hdisj : Disjoint (r.ground.erase e) ((ground m).image f) :=
    Finset.disjoint_left.mpr (fun x hx hy => Finset.disjoint_left.mp hnew
      (Finset.mem_erase.mp hx).2 hy)
  have hrow : (renameRows f (rimRows m (by omega))).row (interfaceRow m hm) =
      (rim m hm).image f := by
    change (rimEdge m (by omega) (interfaceRow m hm)).image f = _
    congr 1
    simp only [rimEdge, interfaceRow, label, rimIndex,
      Nat.mod_eq_of_lt (by omega : 1 < m), rim, firstLabel, secondLabel]
  have hE : ((renameRows f (rimRows m (by omega))).without (interfaceRow m hm)).root =
      renameFamily f (pathRoot m hm) := by
    exact renameRows_root f ((rimRows m (by omega)).without (interfaceRow m hm))
  have h := row_transport (r.ground.erase e) ((ground m).image f) e ((rim m hm).image f)
    r (renameRows f (rimRows m (by omega))) (interfaceRow m hm)
    (Finset.insert_erase he).symm rfl (by simp) (hf0 ▸ fresh_zero m f) hdisj
    (Finset.image_subset_image (rim_subset m hm)) hrow
  simpa only [appendRimRows, hE, ← (interfaces m hm f).1, parentOf] using h

/-- A real existing Rows.root consumer of the constructed local theorems.
    Its output certificate is obtained by running oneStep and the proved row
    identity; no resulting input record is assumed. -/
def rowStep (r : Rows V) (c : Certificate r.ground r.root)
    (e : V) (he : e ∈ r.ground) (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m)
    (f : Label m ↪ V) (hf0 : f 0 = e) (hnew : Disjoint r.ground ((ground m).image f)) :
    Certificate (appendRimRows r e he m hm f hf0).ground
      (appendRimRows r e he m hm f hf0).root := by
  let c' : Certificate (insert e (r.ground.erase e)) r.root := by
    rw [Finset.insert_erase he]
    exact c
  have hXY : Disjoint (r.ground.erase e) ((ground m).image f) :=
    Finset.disjoint_left.mpr (fun x hx hy => Finset.disjoint_left.mp hnew
      (Finset.mem_erase.mp hx).2 hy)
  let out := oneStep m hm hg c' f hf0 (by simp) hXY
  rw [append_root r e he m hm f hf0 hnew]
  exact out

end D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
