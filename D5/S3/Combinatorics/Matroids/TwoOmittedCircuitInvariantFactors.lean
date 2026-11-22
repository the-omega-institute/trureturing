/- GID: D5/S3/Combinatorics/Matroids/TwoOmittedCircuitInvariantFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/TwoOmittedCircuitInvariantFactors
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Cyclic factors of the joint lifting obstruction after two separated omissions. -/

import D5.S3.Combinatorics.Matroids.SparsePavingCircuitProduct
import D5.S3.Combinatorics.Matroids.PuncturedCircuitInvariantFactors
import D5.S3.Combinatorics.Matroids.UniformCircuitInvariantFactors
import D5.S3.FiniteGroups.Modules.FiniteModuleProductCancellation

/-! Cancelling the uniform factors against the two single omissions. -/

namespace D5.S3.Combinatorics.Matroids.TwoOmittedCircuitInvariantFactors

open D5.S3.FiniteGroups.FiniteModuleProductCancellation (finite_prod_cancel)
open Finset
open scoped Matroid
open PuncturedCircuitCoordinates (uniformCore)
open PuncturedCircuitInvariantFactors UniformCircuitInvariantFactors
open SparsePavingCircuitCoordinates (exists_sparse_paving_core indep_iff_card_and_allowed)
open SparsePavingCircuitProduct (sparse_paving_residue_product)
open ParallelCircuitObstruction (parallel_lifting_obstruction weightedCircuitResidues)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)

set_option autoImplicit false

private def addFamily (X : Type*) [AddCommGroup X] (a b : ℕ) :
    ((Fin a → X) × (Fin b → X)) ≃ₗ[ℤ] (Fin (a + b) → X) :=
  (LinearEquiv.sumPiEquivProdPi ℤ (Fin a) (Fin b) (fun _ => X)).symm.trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : Fin a ⊕ Fin b => X) finSumFinEquiv)

private abbrev Families (X Y : Type*) (a b : ℕ) := (Fin a → X) × (Fin b → Y)

private def addFamilies {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (a b c d : ℕ) :
    (Families X Y a b × Families X Y c d) ≃ₗ[ℤ] Families X Y (a + c) (b + d) :=
  (LinearEquiv.prodProdProdComm ℤ (Fin a → X) (Fin b → Y) (Fin c → X) (Fin d → Y)).trans
    ((addFamily X a c).prodCongr (addFamily Y b d))

private theorem cancel_factors {X Y Q₁ Q₂ T : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Q₁] [AddCommGroup Q₂] [AddCommGroup T]
    [Finite X] [Finite Y] [Finite Q₁] [Finite Q₂] {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (e : (Families X Y a b × T) ≃ₗ[ℤ]
      ((Families X Y (a - 1) (b - 1) × Q₁) × (Families X Y (a - 1) (b - 1) × Q₂))) :
    Nonempty (T ≃ₗ[ℤ] (Families X Y (a - 2) (b - 2) × (Q₁ × Q₂))) := by
  let _ : Finite T := Finite.of_injective (fun t : T => e (0, t))
    (fun _ _ h => (Prod.mk.inj (e.injective h)).2)
  have hA : (a - 1) + (a - 1) = (a - 2) + a := by omega
  have hB : (b - 1) + (b - 1) = (b - 2) + b := by omega
  let ex := LinearEquiv.refl ℤ (Q₁ × Q₂)
  let singles := (LinearEquiv.prodProdProdComm ℤ _ _ _ _).trans
    ((addFamilies (X := X) (Y := Y) (a - 1) (b - 1) (a - 1) (b - 1)).prodCongr ex)
  let reorder : ((Families X Y (a - 2) (b - 2) × (Q₁ × Q₂)) × Families X Y a b) ≃ₗ[ℤ]
      ((Families X Y (a - 2) (b - 2) × Families X Y a b) × (Q₁ × Q₂)) :=
    (LinearEquiv.prodAssoc ℤ _ _ _).trans
      (((LinearEquiv.refl ℤ _).prodCongr (LinearEquiv.prodComm ℤ _ _)).trans
        (LinearEquiv.prodAssoc ℤ _ _ _).symm)
  let doubles := reorder.trans
    ((addFamilies (X := X) (Y := Y) (a - 2) (b - 2) a b).prodCongr ex)
  let ix := LinearEquiv.piCongrLeft' ℤ (fun _ : Fin ((a - 1) + (a - 1)) => X) (finCongr hA)
  let iy := LinearEquiv.piCongrLeft' ℤ (fun _ : Fin ((b - 1) + (b - 1)) => Y) (finCongr hB)
  let indices := (ix.prodCongr iy).prodCongr ex
  exact finite_prod_cancel ((LinearEquiv.prodComm ℤ T _).trans
    (e.trans (singles.trans (indices.trans doubles.symm))))

private theorem two_le_choose {k r : ℕ} (hr : 1 ≤ r) (hk : r < k) : 2 ≤ k.choose r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [Nat.choose_succ_succ]
  have h₁ := Nat.choose_pos (show r ≤ k by omega)
  have h₂ := Nat.choose_pos (show r.succ ≤ k by omega)
  omega

/-- In rank at least three and corank at least two, two omitted bases
with sparse intersection exchange two factors of each uniform order for
the two separate gcds of the total size with the weights outside a basis. -/
theorem two_omitted_lifting_obstruction_invariant_factors {V : Type*} [Fintype V] [LinearOrder V]
    {k d : ℕ} {S : Matroid (Fin (k + 2))} (hd : 1 ≤ d)
    (H J : Finset (Fin (k + 2))) (hH : H.card = d + 2) (hJ : J.card = d + 2)
    (hsparse : (H ∩ J).card ≤ d) (hground : S.E = Set.univ)
    (hbases : ∀ B : Finset (Fin (k + 2)), S.IsBase (B : Set (Fin (k + 2))) ↔
      B.card = d + 2 ∧ B ≠ H ∧ B ≠ J)
    (p : V → Fin (k + 2)) (hsurj : Function.Surjective p) (horder : ∀ ⦃a b⦄, p a < p b → a < b) :
    let n := Fintype.card V
    let weight := fun i => (univ.filter fun x => p x = i).card
    let g := univ.gcd weight
    let q₁ := n.gcd ((univ \ H).gcd weight)
    let q₂ := n.gcd ((univ \ J).gcd weight)
    Nonempty ((JointSaturatedImage (S.comap p) ⧸ JointImageInSaturation (S.comap p)) ≃ₗ[ℤ]
      ((Fin ((k.choose d) - 2) → ZMod g) × (Fin ((k.choose (d + 1)) - 2) → ZMod n) ×
        ZMod q₁ × ZMod q₂)) := by
  classical
  intro n weight g q₁ q₂
  let I := Fin (k + 2)
  have hcodim : d + 2 ≤ k := by
    have hUnion := card_union_add_card_inter H J
    have hBound := (H ∪ J).card_le_univ
    rw [Fintype.card_fin] at hBound
    omega
  have hr : d + 2 < Fintype.card I := by simp [I]; omega
  have one (F : Finset I) : ∃ N : Matroid I, N.E = Set.univ ∧
      ∀ B : Finset I, N.IsBase (B : Set I) ↔ B.card = d + 2 ∧ B ≠ F := by
    simpa only [Set.mem_singleton_iff] using
      exists_sparse_paving_core (holes := {F}) hr (by omega) (by simp)
  obtain ⟨MH, hMHground, hMHbase⟩ := one H
  obtain ⟨MJ, hMJground, hMJbase⟩ := one J
  let M (i j : Bool) : Matroid I :=
    match i, j with
    | false, false => uniformCore hH
    | true, false => MH
    | false, true => MJ
    | true, true => S
  have hMground (i j : Bool) : (M i j).E = Set.univ := by
    cases i <;> cases j <;> simp [M, uniformCore, hground, hMHground, hMJground]
    rfl
  have hMbase (i j : Bool) (B : Finset I) : (M i j).IsBase (B : Set I) ↔
      B.card = d + 2 ∧ (i = true → B ≠ H) ∧ (j = true → B ≠ J) := by
    cases i <;> cases j <;> simp [M, hMHbase, hMJbase, hbases]
    change (B : Set I).ncard = d + 2 ↔ B.card = d + 2
    rw [Set.ncard_coe_finset]
  let _ : Nonempty V := ⟨(hsurj 0).choose⟩
  let obs (i j : Bool) := JointSaturatedImage ((M i j).comap p) ⧸ JointImageInSaturation ((M i j).comap p)
  have lift (i j : Bool) : Nonempty (obs i j ≃ₗ[ℤ] weightedCircuitResidues (M i j) p) := by
    let holes : Set (Finset I) := {F | (i = true ∧ F = H) ∨ (j = true ∧ F = J)}
    have hsize (F : Finset I) (hF : F ∈ holes) : F.card = d + 2 := by
      rcases hF with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hH
      · exact hJ
    have hPair : holes.Pairwise (fun F G => (F ∩ G).card + 2 ≤ d + 2) := by
      intro F hF G hG hne
      rcases hF with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rcases hG with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact (hne rfl).elim
      · omega
      · rw [inter_comm]; omega
      · exact (hne rfl).elim
    have hB (B : Finset I) : (M i j).IsBase (B : Set I) ↔ B.card = d + 2 ∧ B ∉ holes := by
      rw [hMbase]; simp only [holes, Set.mem_ofPred_eq, not_or, not_and]
    have nonloop (a : I) : (M i j).IsNonloop a := by
      apply Matroid.indep_singleton.mp
      rw [← coe_singleton, indep_iff_card_and_allowed hr hsize hPair hB]
      have hc : ({a} : Finset I).card < d + 2 := by simp
      exact ⟨hc.le, fun h => (hsize _ h).not_lt hc⟩
    obtain ⟨e, _⟩ := parallel_lifting_obstruction hsurj horder (fun a => nonloop (p a))
    exact ⟨e⟩
  obtain ⟨square⟩ := sparse_paving_residue_product p hsurj H J hd hH hJ hsparse M hMground hMbase
  obtain ⟨u⟩ := lift false false
  obtain ⟨t⟩ := lift true true
  obtain ⟨oneH⟩ := lift true false
  obtain ⟨oneJ⟩ := lift false true
  let joint := (u.prodCongr t).trans (square.trans (oneH.symm.prodCongr oneJ.symm))
  obtain ⟨full⟩ := uniform_lifting_obstruction_invariant_factors
    (fun B => by simpa using hMbase false false B) p hsurj horder
  obtain ⟨singleH⟩ := punctured_lifting_obstruction_invariant_factors hH hr (hMground true false)
    (fun B => by simpa using hMbase true false B) p hsurj horder
  obtain ⟨singleJ⟩ := punctured_lifting_obstruction_invariant_factors hJ hr (hMground false true)
    (fun B => by simpa using hMbase false true B) p hsurj horder
  have hn : 0 < n := Fintype.card_pos
  have hg : 0 < g := by
    obtain ⟨v, hv⟩ := hsurj 0
    have hweight : 0 < weight 0 := card_pos.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩
    exact Nat.pos_of_ne_zero fun h => hweight.ne' (Nat.zero_dvd.mp (h ▸ gcd_dvd (f := weight) (mem_univ 0)))
  let _ : NeZero n := ⟨hn.ne'⟩
  let _ : NeZero g := ⟨hg.ne'⟩
  let _ : NeZero q₁ := ⟨(Nat.gcd_pos_of_pos_left _ hn).ne'⟩
  let _ : NeZero q₂ := ⟨(Nat.gcd_pos_of_pos_left _ hn).ne'⟩
  have full' : obs false false ≃ₗ[ℤ] Families (ZMod g) (ZMod n) (k.choose d) (k.choose (d + 1)) := full
  let X := Fin (k.choose d - 1) → ZMod g
  let Y := Fin (k.choose (d + 1) - 1) → ZMod n
  have hCard : Fintype.card I - 2 = k := by simp [I]
  let ix := LinearEquiv.piCongrLeft' ℤ (fun _ : Fin ((Fintype.card I - 2).choose d - 1) => ZMod g)
    (finCongr (congrArg (fun j => j.choose d - 1) hCard))
  let iy := LinearEquiv.piCongrLeft' ℤ (fun _ : Fin ((Fintype.card I - 2).choose (d + 1) - 1) => ZMod n)
    (finCongr (congrArg (fun j => j.choose (d + 1) - 1) hCard))
  have singleH' : obs true false ≃ₗ[ℤ] (X × (Y × ZMod q₁)) :=
    singleH.trans (ix.prodCongr (iy.prodCongr (LinearEquiv.refl ℤ _)))
  have singleJ' : obs false true ≃ₗ[ℤ] (X × (Y × ZMod q₂)) :=
    singleJ.trans (ix.prodCongr (iy.prodCongr (LinearEquiv.refl ℤ _)))
  let eH := singleH'.trans (LinearEquiv.prodAssoc ℤ X Y (ZMod q₁)).symm
  let eJ := singleJ'.trans (LinearEquiv.prodAssoc ℤ X Y (ZMod q₂)).symm
  obtain ⟨e⟩ := cancel_factors (two_le_choose hd (by omega)) (two_le_choose (by omega : 1 ≤ d + 1) (by omega))
    ((full'.symm.prodCongr (LinearEquiv.refl ℤ _)).trans (joint.trans (eH.prodCongr eJ)))
  exact ⟨e.trans (LinearEquiv.prodAssoc ℤ _ _ _)⟩

end D5.S3.Combinatorics.Matroids.TwoOmittedCircuitInvariantFactors
