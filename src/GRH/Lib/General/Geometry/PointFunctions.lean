import GRH.Lib.General.Geometry.ReducedClosure
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Regular functions via functor of points: evaluation, gluing, fpqc descent of
functions. -/


open CategoryTheory AlgebraicGeometry TopologicalSpace.Opens Scheme TopCat.Presheaf Hom Spec
  Limits.pullback EffectiveEpi Category IsLocalRing IsOpenImmersion
variable {X Y κ U A B x} {f g : PointFn X} {t : Spec A ⟶ X} {V : κ → X.Opens} (hU :
  IsAffineOpen U) (p : Y ⟶ X) (s : Γ(X, U)) (hf : f.IsRegularOn U) (hg : g.IsRegularOn U) (M :
  LineBundle Y κ) {z : Spec B ⟶ X} [IsLocalRing B]

lemma LandsIn.mono {t V} : @LandsIn X Y t U → U ≤ V → LandsIn t V := by tauto

lemma landsIn_iff_mem : LandsIn z U ↔ z (closedPoint B) ∈ U :=
  top_le_iff.trans closed_point_mem_iff.symm

lemma LineBundle.exists_landsIn t : ∃ i,
  @LandsIn Y (Spec B) t (M.opens i) := by simp [landsIn_iff_mem, ← mem_iSup, M.3]

lemma landsIn_fromSpec t : @LandsIn X Y (t ≫ hU.fromSpec) U := by aesop_cat

lemma landsIn_opensRange {R c} [@IsOpenImmersion (Spec R) X c] : LandsIn t c.opensRange ↔ ∃ φ,
  map φ ≫ c = t := ⟨fun h ↦ ⟨preimage (lift c t (by aesop)), by simp⟩, by aesop_cat⟩

lemma landsIn_comp_incl {t} : @LandsIn X Y (t ≫ U.ι) U := by aesop_cat

lemma landsIn_iInf [Finite κ] : LandsIn p (iInf V) ↔ ∀ a,
  LandsIn p (V a) := by simp [LandsIn, ← coe_inj, coe_iInf]

lemma hom_ext_of_cover {f g : Y ⟶ X} (h : ∀ i A t, @LandsIn Y (Spec A) t (M.opens i) → t ≫ f =
  t ≫ g) : f = g := (Y.openCoverOfIsOpenCover _ M.3).affineRefinement.openCover.hom_ext _ _ fun _ ↦
  h _ _ _ landsIn_comp_incl

/-- Gluing: let U_i be the cover of a line bundle M on Y, and F_i(t): Spec A → X be given for
each t: Spec A → Y landing in U_i, compatibly with ring maps and change of i. Then some f: Y
→ X has f∘t = F_i(t) always. -/
lemma exists_hom_of_cover (F : ∀ i _ t, LandsIn t (M.opens i) → (_ ⟶ X)) (h : ∀ i j A B φ t hi hj,
  F j B (@map A B φ ≫ t) hj = map φ ≫ F i A t hi) : ∃ f, ∀ i A t hi, t ≫ f = F i A t hi :=
  have K {i j A B t s} hi hj : fst t s ≫ F i A t hi = snd .. ≫ F j B s hj := hom_ext_of_cover
    .one (by simp_all [homEquiv.surjective.forall]; grind [LandsIn.comp, condition, =_ h _ j])
  ⟨_, fun _ _ t _ ↦ Cover.hom_ext (.pullback₁ t _) _ _ fun _ ↦ by
    erw [condition_assoc, (Y.openCoverOfIsOpenCover _
      M.3).affineRefinement.openCover.ι_glueMorphisms _ fun _ _ ↦ K landsIn_comp_incl _, K]; rfl⟩

lemma le_of_cover {U W} (h : ∀ i A t, @LandsIn Y (Spec A) t (M.opens i) → LandsIn t U →
  LandsIn t W) : U ≤ W := fun
  x ↦ (M.exists_landsIn (fromSpecStalk ..)).rec (by simpa [landsIn_iff_mem] using h · _ _ ·)

instance [EffectiveEpi p] [QuasiCompact p] : IsSchemeTheoreticallyDominant p :=
  ⟨by simpa using @ker_eq_bot_of_isIso _ _ _ (ExtremalEpi.isIso _ _ _ p.toImage_imageι)⟩

namespace PointFn

lemma ofSection_eq h s : @ofSection X U s A t = evalSection t h s := dite_eq_left h

lemma ofSection_appLE {W} e s (h : LandsIn x W) : ofSection (p.appLE U W e s) A x = ofSection s A (x
  ≫ p) := by rw [ofSection_eq, ofSection_eq, evalSection, evalSection, ← appLE_comp_appLE] <;> tauto

lemma isRegularOn_ofSection : (ofSection s).IsRegularOn U := by (repeat intro); erw
  [← ofSection_appLE, ofSection_eq, evalSection, ΓSpecIso_naturality, ofSection_eq] <;> tauto

lemma ofSection_map {V} i : LandsIn t V → @ofSection X V (X.presheaf.map i s) A t =
  ofSection s A t := ofSection_appLE (𝟙 X) _ s

lemma landsIn_fromSpecStalk : x ∈ U → LandsIn (X.fromSpecStalk x) U := by simp [landsIn_iff_mem]

lemma map_evalSection_fromSpec h : map (evalSection t h) ≫ hU.fromSpec = t := by
  simp [evalSection, hU.SpecMap_appLE_fromSpec t (isAffineOpen_top _) h, IsAffineOpen.fromSpec_top]

include hU in lemma point_eq_of_ofSection_eq (h : LandsIn t U) (k : LandsIn x U) (e : ∀ s,
  @ofSection X U s A t = ofSection s A x) : t = x := map_evalSection_fromSpec hU h ▸
  map_evalSection_fromSpec hU k ▸ by congr 2 with; simp [← ofSection_eq, e]

@[simp] lemma ofSection_map_fromSpec φ : ofSection s A (map φ ≫ hU.fromSpec) = φ s := by
  rw [ofSection_eq, map_injective ((cancel_mono _).1 (map_evalSection_fromSpec ..))]; aesop_cat

lemma ofSection_fromSpecStalk hx s : ofSection s _ (X.fromSpecStalk x) =
  X.presheaf.germ U x hx s := by erw [ofSection_eq (landsIn_fromSpecStalk hx), evalSection, appLE,
  fromSpecStalk_app, (ΓSpecIso _).inv_hom_id_apply] <;> tauto

lemma landsIn_basicOpen (h : LandsIn t U) s : LandsIn t (X.basicOpen s) ↔
  IsUnit (@ofSection X U s A t) := by
  rw [LandsIn, ← inf_eq_left, ← basicOpen_appLE, ofSection_eq h]
  simpa using! PrimeSpectrum.iSup_basicOpen_eq_top_iff (f := ![_])

lemma ofSection_appTop c A t : ofSection (p.appTop c) A t = ofSection c A (t ≫ p) := rfl

/-- Descent of functions: for p: Y → X flat, surjective, quasi-compact and V_a the cover of M on
Y, regular f_a on p⁻¹U ∩ V_a agreeing at points with the same image in X are pull-backs of
one section over U. -/
lemma exists_ofSection_glue [Flat p] [Surjective p] [QuasiCompact p] (f : _ → _) (hf : ∀ a,
  IsRegularOn (f a) (p ⁻¹ᵁ U ⊓ M.opens a)) (h : ∀ a b A t s, t ≫ p = s ≫ p → LandsIn (t ≫ p) U →
  LandsIn t (M.opens a) → LandsIn s (M.opens b) → f a A t = f b A s) : ∃ s, ∀ a A t, LandsIn (t ≫ p)
  U → LandsIn t (M.opens a) → @ofSection X U s A (t ≫ p) = f a A t := (exists_hom_of_cover
  (M.pull (fst ..)) (fun a A t _ ↦ specMap (FreeCommRing.lift ![f a A (t ≫ fst ..)]))
  (by simp_rw [← map_comp]; congr!; ext; simp; rw [← hf, h] <;> simp_all [LandsIn.comp, condition,
  landsIn_comp_incl])).elim fun q e ↦ ⟨inv (appLE ..) (appTop (desc (snd p U.ι) q fun a b E ↦
  hom_ext_of_cover ((M.pull (a ≫ fst ..)).mul (M.pull (b ≫ fst ..))) (by simp_all [← assoc]; grind
  [condition, landsIn_comp_incl])) ((ΓSpecIso _).2 (.of 0))), fun a A t _ _ ↦ by erw [← lift_fac U.ι
  (t ≫ p) (by aesop), ← ofSection_appLE, IsIso.inv_hom_id_apply, ofSection_appTop, ← lift_snd_assoc
  (f := p) t, fac, e a, ofSection_eq, evalSection, ΓSpecIso_naturality] <;> simp [lift_fst, *]⟩

include hf

namespace IsRegularOn

lemma exists_ofSection : ∃ s, ∀ A t, LandsIn t U → @ofSection X U s A t = f A t := by
  simpa using exists_ofSection_glue (𝟙 X) .one (fun _ ↦ f) (by simpa [IsRegularOn])

lemma pull : (f.pull p).IsRegularOn (p ⁻¹ᵁ U) := by aesop_cat

lemma mono {V} : V ≤ U → f.IsRegularOn V := by aesop_cat

lemma mul {V} : g.IsRegularOn V → (f * g).IsRegularOn (U ⊓ V) := by simp_all [IsRegularOn]

include hg

/-- Let p: Y → X be quasi-compact and scheme-theoretically dominant, V_a the cover of M on Y.
Functions f, g regular on U agree on U if their pull-backs agree on each p⁻¹U ∩ V_a. -/
lemma ext_of_dominant [IsSchemeTheoreticallyDominant p] [QuasiCompact p] (h : ∀ a A t, LandsIn (t ≫
  p) U → LandsIn t (M.opens a) → f A (t ≫ p) = g A (t ≫ p)) A t : LandsIn t U → f A t = g A t := by
  grind [(p.app_injective _ (section_ext Y.sheaf _ _ _ fun x k ↦ have := landsIn_fromSpecStalk k
    by repeat erw [← ofSection_fromSpecStalk]; simp_all [app_eq_appLE, ofSection_appLE]
       grind [M.exists_landsIn (Y.fromSpecStalk x)]) : hf.exists_ofSection.choose =
    hg.exists_ofSection.choose)]
