import OmegaMath.NumberTheory.GRH.Lib.Cohomology.Etale.RelativeChains
import OmegaMath.NumberTheory.GRH.Lib.General.Geometry.OpenSubfunctors
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Compatible classes with supports glue when lower degrees vanish. -/


open CategoryTheory Subfunctor CartesianMonoidalCategory Fin Comparison LongExactSeq
variable {C} [Category C] {V X : C ⥤ Type 1} (U : Subfunctor V) {A B : Subfunctor V} (h : A ≤ B)

/-- For subfunctors U and W' ⊂ W of V, the map ℤ[W']/ℤ[U ∩ W'] → ℤ[W]/ℤ[U ∩ W]. -/
abbrev relFreeAb.restrict : relFreeAb (U.preimage A.ι) ⟶ relFreeAb (U.preimage B.ι) :=
  map (homOfLe h) (id le_rfl)

attribute [local simp ←] H.map_comp
attribute [local simp] contravariant exists_fin_succ

/-- Gluing: let finitely many W_i ⊂ V lie in an intersection-closed class whose members A have
H^n(A, U ∩ A) = 0 for n < d, with U ∪ ⋃ W_i dense. Then classes in H^d(W_i, U ∩ W_i)
agreeing on overlaps come from H^d(V,U). -/
lemma relFreeAb.exists_glued_class {r F d} S (hS : InfClosed S) (h : ∀ A ∈ S, ∀ n < d,
  Subsingleton (H (relFreeAb (U.preimage A.ι)) F n)) (W : Fin r → _) (hW : ∀ i, W i ∈ S) (hd :
  IsCohomDense F (iSup W ⊔ U)) (x : ∀ _, _) (hx : ∀ i j, .map F (restrict U inf_le_left) d (x i) =
  H.map F (restrict U inf_le_right) d (x j)) : ∃ y, ∀ i, .map F (map (W i).ι le_rfl) d y = x i :=
  have t {A B D : Subfunctor V} (e : A ⊓ B = D) : ∃ w,
    ShortComplex.ShortExact ⟨restrict U _, _, w⟩ := (by
   delta toFunctor homOfLe; aesop : range (homOfLe (e ▸ inf_le_right)) =
    A.preimage B.ι) ▸ shortExact_triple ..
  have : (∀ n ≤ d, ∀ {z}, (∀ i, H.map F (restrict U (le_iSup W i)) n z = 0) → z = 0) ∧
      ∃ y, ∀ i, .map F (restrict U (le_iSup ..)) d y = x i := by
    clear hd; induction' r with _ ih
    simp; intros; apply (H.subsingleton_of_id_eq_zero (hom_ext nofun) ..).1
    obtain ⟨J, I, y, hy⟩ := (ih (W ·.succ ⊓ W 0) (by tauto) 0 (by simp)).1,
      ih _ (by tauto) _ (hx ·.succ ·.succ)
    have m := by simpa [-contravariant] using (pull_hom_contravariant (t (inf_of_le_left
      (iSup_comp_le W succ))).2 (t (iSup_min ..)).2 (.id F) ⟨restrict U (iSup_mono (by simp)),
      restrict U (le_iSup W 0), map (homOfLe (le_iSup ..)) le_rfl, hom_ext, hom_ext⟩)
    exact have := excision _ (.of_top_le fun _ x _ ↦
        (by simpa using x.2 :).imp (⟨⟨_, ·⟩, rfl⟩) (by aesop)) rfl
      ⟨fun n hn z hz ↦ m.rotate.eq_zero_of_delta_eq_zero (fun _ ↦ ⟨0, sub_eq_zero.1 (by
      cases n; exacts [rfl, J _ (by lia) fun _ ↦ (h _ (by tauto) _ hn).1 ..])⟩) (this n).1 z (hz
      0) (I n hn (by simpa +instances using! hz ·.succ)), (m.exists_preimage (this d).2 (this _).1 _
        y (sub_eq_zero.1 (J d .refl (by simpa +instances [← hy] using! hx ·.succ 0)))).imp
      fun _ ⟨hz, rfl⟩ ↦ cases hz (by simpa +instances using! hy)⟩
  by simpa using (excision _ (by simpa) rfl d).2.exists.1 this.2

/-- For subfunctors U ⊂ V and W ⊂ X, the map ℤ[V × X]/ℤ[U × X ∪ V × W] → ℤ[V]/ℤ[U] ⊗ ℤ[X]/ℤ[W]
sending [(x,y)] to [x] ⊗ [y]. -/
def relFreeAb.prod W : relFreeAb (U.preimage (fst _ X) ⊔ preimage W (snd ..)) ⟶ abTensor
  (relFreeAb U) (relFreeAb W) := abCoker.desc
  (freeAb.prod .. ≫ abTensor.map (π U) _ ≫ (abTensor _).map (π W)) (freeAb.hom_ext fun _ x ↦
  show mk .. ⊗ₜ mk .. = 0 by cases x.2 <;> [rw [mk_eq_zero]; nth_rw 2 [mk_eq_zero]] <;> aesop)
