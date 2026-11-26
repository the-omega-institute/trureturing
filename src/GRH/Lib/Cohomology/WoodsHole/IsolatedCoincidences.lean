import GRH.Lib.Cohomology.PointClass.LocusEquations
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Half of the holomorphic Lefschetz (Woods Hole) formula for h-forms and correspondences
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Reduced coincidences of two maps are finitely many; local Jacobian terms. -/


open CategoryTheory Ideal CommAlgCat Algebra TrivSqZeroExt Matrix Set SqZeroExt NatTrans DualNumber
  Module
variable {k E d} [Field k] {W X : CommAlg k ⥤ Type 1} (u c : W ⟶ X) [Field E] [Algebra E k]

/-- For a k[ε]-point x of W: if c(x) = u(x), then x is constant, that is, comes from the k-point
below it. -/
abbrev ConstIfCoincident x := c (of k k[ε]) x = u _ x → x = W.map (fst ≫ structureMap) x

/-- The finite set s of k-points of W consists of coincidences of u and c, every field-valued
coincidence comes from s, and every k[ε]-valued coincidence is constant. -/
def IsCoincidenceSet (s : Finset _) := (∀ x, ConstIfCoincident u c x) ∧ (∀ w ∈ s, c _ w = u _ w) ∧
  ∀ K, IsField K.1 → ∀ x, c K x = u K x → ∃ w ∈ s, x = W.map structureMap w

/-- Let k be algebraically closed, X separated, u, c: W → X with every k[ε]-valued coincidence
constant and all field-valued coincidences in finitely many charts of W. Then the
coincidences form a finite set of k-points. -/
lemma exists_isCoincidenceSet [IsAlgClosed k] [hX : IsSepFunctor X] (h : ∀ x,
  ConstIfCoincident u c x) {ι} [Finite ι] (a : ι → EtaleChart d W) (ha : ∀ K, IsField K.1 → ∀ x,
  c K x = u K x → ∃ i, x ∈ (a i).locus K) : ∃ s, IsCoincidenceSet u c s := by
  choose J hJ using fun {A} y ↦ by simpa [← naturality_apply] using hX.1 A (c _ y) (u A y)
  choose o j using @nullstellensatz_exists_le_ker k
  use (finite_iUnion fun i ↦ .dependent_image (@finite_minimalPrimes_of_isNoetherianRing _ _
    (FiniteType.isNoetherianRing k _) (J (a i).point)) fun p m ↦ W.2 (ofHom (o m.isPrime.1))
    (a i).point).toFinset, h
  simp
  use fun _ _ _ m ↦ (· ▸ (hJ ..).2 (m.le.trans (j _)))
  peel ha
  obtain ⟨⟨_, ⟨⟩⟩, _⟩ := this, IsField.isDomain ‹_›
  exact (exists_minimalPrimes_le (J := comap ..) ((hJ ..).1 ‹_›)).imp fun p ⟨m, q⟩ ↦
   (exists_mem_colon_of_tangent rfl (j _) fun v _ l
    r ↦ congr(($((a _).eq_comp_of_map_point_eq _ (h _ ((hJ ..).2
   (m.le.trans l)))) r).2)).elim fun _ l ↦ ⟨m, W.map_comp_apply .. ▸ eq_comp_structureMap_of_ker_le
    (l.1 ⟨·, ·, rfl⟩ |> m.isPrime.2 |>.resolve_left (by tauto) |> q) ▸ rfl⟩

/-- In every chart of X with d coordinates containing c(w), some matrix N of determinant n has
t·du − dc = N(du − dc) on all tangent vectors of W at w. -/
def HasJacobianRatio {X} (u c : W ⟶ restrictAlg E k ⋙ X) d (t n : k) w := ∀ A : EtaleChart d X,
  c _ w ∈ A.locus _ → let ξ (γ : _ ⟶ (restrictAlg ..) (.of k k[ε])) i := (γ (A.coordinate i)).snd
      ∃ N, N.det = n ∧ ∀ v α γ, W.map fst v = w → X.map α A.point = u _ v →
        X.map γ A.point = c _ v → t • ξ α - ξ γ = N *ᵥ (ξ α - ξ γ)

/-- Let v be a (k ⊕ k^d)-point of X based in a chart with d coordinates, whose k[ε]-points φ(v),
φ linear forms on k^d, are distinct. Then their chart coordinates are those of φ in some
basis, and they exhaust the tangent vectors at the base point. -/
lemma EtaleChart.tangent_mem_range_of_jet {X} (A : EtaleChart d X) {T : FGModuleCat k} (hT : finrank
  k T = d) v : let Y := restrictAlg E k ⋙ X; let f φ := Y.map (ofHom (map (Dual.eval k T φ))) v
    Y.map fst v ∈ A.locus _ → f.Injective → (∀ w, Y.map fst w = Y.map fst v → w ∈ range f) ∧ ∃ D :
      T ≃ₗ[k] _, ∀ φ α, X.map α A.point = f φ → (A.coordinate · |> α |>.snd) = D φ := fun hv h ↦ by
  obtain ⟨⟨⟨γ⟩, ⟨⟩⟩, S : IsSquareZero ((restrictAlg E k).map fst)⟩ :=
    (A.isOpenSub.mem_of_isSquareZero _ · _ hv) (fst_surjective_and_kerIdeal_sq (k := k)),
    fst_surjective_and_kerIdeal_sq (k := k) (M := k)
  have U {α β} a b := (A.injective _).eq_iff.2 (A.lift_unique S a (ext congr($a _) <|
    congrFun b ·) : α = β)
  erw [← funext fun _ ↦ X.map_comp_apply ..] at *
  let B := (0 + LinearMap.pi fun i ↦ (γ.1 _).2).linearEquivOfInjective (by tauto) (by simpa)
  use fun w H ↦ ?_, B, fun _ _ ↦ (A.injective _ · ▸ rfl)
  obtain ⟨_, ⟨⟩⟩ := A.isOpenSub.mem_of_isSquareZero _ S w (H ▸ hv)
  refine (B.surjective _).imp fun φ ↦ U (A.injective _ ?_)
  simpa [SqZeroExt.fst, ← fstHom_comp_map (.applyₗ φ), -fstHom_comp_map] using! H.symm

/-- Let W have an atlas of dimension d and P be a tangent polynomial of c, u at w with P(1) ≠ 0.
Then `HasJacobianRatio` holds at w with determinant P(t)/P(1) for all t, and every k[ε]-valued
coincidence above w is constant. -/
lemma IsTangentPoly.hasJacobianRatio {X} {c u : W ⟶ restrictAlg E k ⋙ X} {w P} (hW :
  IsChartCovered d W) (hP : IsTangentPoly d c u w P) (h₁ : P.eval 1 ≠ 0) : (∀ t, HasJacobianRatio u
  c d t (P.eval t / P.eval 1) w) ∧ ∀ v, W.map fst v = w → ConstIfCoincident u c v := by
  obtain ⟨_, v, T, hT, ⟨⟩, h, hu, p⟩ := hP
  obtain ⟨⟨S, ⟨⟩⟩, V, _⟩ := (⟨(1 - T).equivOfDetNeZero (by grind [one_smul]), by simp⟩ : T ∈ range
    (1 - ·.1)),
    EtaleChart.tangent_mem_range_of_jet _ hT v (hW.1 _ (Field.toIsField k) _).choose_spec h.of_comp
  use fun t A hw ↦ ?_, (V · · |>.elim fun | φ, rfl, e => ((by simpa using h (e.trans (hu φ)).symm)
    ▸ .symm (W.map_comp_apply .. ▸ by congr with _ <;> simp)))
  obtain ⟨_, D, G⟩ :=
    (by simpa only [← naturality_apply] using A.tangent_mem_range_of_jet hT (c _ v) :) hw h
  use (D ∘ₗ ((1 - t • (1 - S.1)) * S.symm.1) ∘ₗ D.symm).toMatrix', by
    simp [S.det_coe_symm]; grind [one_smul, sub_sub_cancel], fun v _ _ ↦ by
    rintro ⟨φ, ⟨⟩⟩ a b; simp [G φ _ b, G _ _ (hu φ ▸ a), ↓map_neg] ∘ V v
