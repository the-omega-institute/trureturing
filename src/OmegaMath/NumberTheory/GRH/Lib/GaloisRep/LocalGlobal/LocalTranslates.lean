import OmegaMath.NumberTheory.GRH.Lib.LocalGL.Iwahori.SortedExponents
import OmegaMath.NumberTheory.GRH.Lib.Adelic.CuspForms.FormRepresentation
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Local-global compatibility at tame level, away from and at l (known result; see
Lib.GaloisRep.LocalGlobal.LabelCompatibility).

Part of: Congruence subgroups and level structures of adelic groups (known result; see
Lib.Adelic.Unitary.CongruenceLevel).

Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms (known
result; see Lib.Adelic.CuspForms.Petersson).

This file: Forms spherical off S; simultaneous diagonalisation of Hecke operators; levels off finite
sets. Local component of a form: smooth, admissible, translates keep the Hecke eigensystem. -/

variable {E n : Type} [Field E] [CMType E] [Fintype n] {V : Space E n 1} {κ : Weight E}
  {w : FinPlace E} (hw : _ ≠ w)

lemma exists_inf_trivialOn_le {H} (hH : H.IsOpen) : ∃ S : Finset _,
  (∀ w, maxCompactAt n w ≤ H → w ∉ S ∧ star w ∉ S)
  ∧ Kf E n ⊓ Gf.trivialOn n S ≤ H := (exists_minimal_of_wellFoundedLT _ ((isCompact_Kf.diff
  hH).elim_finite_subcover _ (isOpen_ne_fun continuous_one <| Gf.continuous_atPlace ·) fun g h ↦ by
    simpa using mt Gf.ext (H.one_mem.ne_of_notMem h.2))).imp fun S ⟨_, m⟩ ↦ by
  simp_all [Set.subset_def]
  use fun w _ ↦ (?_ ∘ @m (S \ {w, star w}) (Gf.exists_supportedOn_mul_trivialOn
    {w} · |>.rec ?_)) ?_ <;> grind [Gf.mem_trivialOn, Gf.mem_supportedOn,
    Gf.atPlace_star_eq_one_iff, star_star, Subgroup.mem_inf, mul_mem, IsConcreteLE.le_iff]

/-- A form f has Hecke polynomial P at a split place w if and only if K_w fixes f and there are
scalars t_j with T_{w,j} f = t_j f for all j and P = Σ(−1)^j q_w^{j(j−1)/2} t_j X^{n−j}. -/
lemma hasHeckePolyAt_iff {f w} hw {P} : HasHeckePolyAt f.1 w hw P ↔
  f ∈ sphericalAt (V.formTranslation κ) w ∧ ∃ t, P
  = heckePoly w.q (Fintype.card n) t ∧ ∀ j, heckeSplit (V.formTranslation κ) hw j f = t j • f := by
  simp [HasHeckePolyAt, Subtype.ext_iff]
  congr!; exact .symm (map_heckeSplit _ _ (V.forms κ).subtype)

/-- For a split place w, the open subgroup of the g in G_f that lie in H once their components
at w and w̄ are replaced by 1. -/
noncomputable def offPartComap (H : OpenSubgroup (Gf E n)) := H.comap
    (.mk' (fun g ↦ g * (atSplit hw (g.atPlace w))⁻¹) (by simp [(Gf.commute_supportedOn_trivialOn
  (atSplit_mem_supportedOn _ _) _).inv_left.eq, mul_assoc])) (by simp; fun_prop)

/-- A finite-dimensional space M of forms fixed by the integral points trivial at S, and stable
under all T_{w,j} at split w with w, w̄ ∉ S, is spanned by its elements that are Hecke
eigenvectors off S (`IsSphericalOff`). -/
lemma le_span_isSphericalOff {S : Finset _} M (h : M ≤ levelSpace (V.formTranslation κ) (Kf .. ⊓
  Gf.trivialOn n S)) [Module.Finite ℂ M] (T : ∀ w hw, w ∉ S → star w ∉ S → ∀ j, ∀ f ∈ M, heckeSplit
  (V.formTranslation κ) (w := w) hw j f ∈ M) : M ≤ .span ℂ {f ∈ M | ∃ P, IsSphericalOff S f.1 P} :=
  ((V.exists_isUnitary_formTranslation κ).choose_spec.le_span_hecke_eigenvectors (by grind
  [star_star]) (fun w (o : w.IsSplit ∧ _) ↦ h.trans (And.elim levelSpace_le_sphericalAt o.2)) (by
  tauto)).trans (Submodule.span_le.2 fun _ ⟨m, c, _⟩ ↦ by_cases (by aesop) (Submodule.subset_span
  ⟨m, _, ·, by simpa [Subtype.ext_iff] using h m, fun w _ a b ↦ (hasHeckePolyAt_iff _).2
  ⟨levelSpace_le_sphericalAt a b (h m), dite _ (c ⟨⟨w, ·⟩, ·⟩) default, rfl, by aesop⟩⟩))

variable {E n : _} [Field E] [CMType E] [Fintype n]
  (V : Space E n 1) (κ : Weight E) {w : FinPlace E} (hw : _ ≠ w)

/-- For a split place w, the homomorphism GL_N(E_w) → G_f, N the cardinality of n, given by a
chosen numbering of n followed by `atSplit`. -/
noncomputable abbrev embedAtSplit {E : _} {n : _} [Field E] [NumberField E]
    [NumberField.IsCMField E] [Fintype n] {w : FinPlace E} (hw : _ ≠ w) :=
  (atSplit hw).comp (reindexGL (Fintype.equivFin n)).symm.toMonoidHom

/-- The representation of GL_N(E_w), N the cardinality of n, on forms of weight κ on V at a
split place w, through a chosen numbering of n. -/
noncomputable abbrev localFormRep := Rep.of ((V.formTranslation κ).comp (embedAtSplit hw))

open Set Fintype Submodule Module End Gf

attribute [local simp] atPlace_atSplit_of_ne mem_intGL

variable {V} {κ} {hw} {x : ↑(localFormRep V κ hw)}

instance : IsSmoothRep (localFormRep V κ hw).ρ := ⟨fun x ↦ .mono ((((continuous_atSplit hw).comp
  (.units_map _ (by simp; fun_prop))).1 _ x.2.1).mem_nhds (by simp)) fun _ ↦ Subtype.ext ∘ funext⟩

instance : Module.Finite ℂ ((cyclicSpan (localFormRep V κ hw).ρ x).submoduleOf (levelSpace
  (localFormRep V κ hw).ρ proIwahori)) := .of_fg (fg_of_fg_map _ (by simp) ((Finite.iff_fg.1
  (V.finite_formTranslation_levelSpace κ (offPartComap hw ⟨_, x.2.1⟩ ⊓ .comap _ (continuous_atPlace
  w) (.comap (reindexGL (equivFin n)).toMonoidHom (.units_map _ (by simp; fun_prop)) ⟨_,
  isOpen_proIwahori⟩)).2)).of_le (image_subset_iff.2 fun z h ⟨_, a, b⟩ ↦ (LinearMap.eqOn_span
  (eqOn_range.2 (by ext : 3; exact .trans (by simp [(commute_supportedOn_trivialOn
  (atSplit_mem_supportedOn _ _) _).right_comm, ← mul_assoc]) (a _))) h).trans (z.2 ⟨_, b⟩))))

lemma isUnitary_localFormRep : IsUnitary (localFormRep V κ hw).ρ (V.exists_isUnitary_formTranslation
  κ).choose := (V.exists_isUnitary_formTranslation κ).choose_spec.imp id (by tauto)

/-- If a form x on V is an eigenform for the system P of Hecke polynomials, then so is every
non-zero y in the span of the translates of x under the local group GL_n(E_w) at a split
place w. -/
lemma IsEigenform.of_mem_cyclicSpan {y P} (h : IsEigenform x.1 P) (hy :
  y ∈ cyclicSpan (localFormRep V κ hw).ρ x) (_ : y ≠ 0) : IsEigenform
  y.1 P := ⟨by simpa, h.2.mp (.mono ((toFinite {w}).star.insert w).compl_mem_cofinite fun _ _ ↦ (by
  peel ·; rw [hasHeckePolyAt_iff, mem_span] at *
  use hy _ (by simp [-mem_supportedOn]; intros; rw [← mul_apply, ← map_mul,
    commute_supportedOn_trivialOn ‹_›] <;> aesop)
  peel this.2; simpa using hy (eigenspace ..) (by simp_all [← heckeSplit_comm_of_trivialOn])))⟩

/-- At a split place w, a form x has Hecke polynomial P if and only if, in the local
representation of GL_n(E_w) on forms, GL_n(O_w) fixes x, the j-th Hecke operator scales x by
t_j, and P = Σ (−1)^j q_w^{j(j−1)/2} t_j X^{n−j}. -/
lemma hasHeckePolyAt_iff_localFormRep {P} : HasHeckePolyAt x.1 w hw P ↔
  x ∈ levelSpace (localFormRep V κ hw).ρ (Kw ..) ∧
  ∃ t, P = heckePoly w.q (card n) t ∧ ∀ j, heckeGL (localFormRep V κ hw).ρ j x = t j • x := by
  rw [hasHeckePolyAt_iff, mem_sphericalAt_iff, and_congr_left', and_congr_right]
  congr! 5
  apply heckeFun_comp (reindexGL (equivFin n)).toMonoidHom _ ‹_›
  all_goals clear * -; simp_all [reindex_equiv (reindexGL (equivFin _)), indicator,
    basicDoubleCoset,
    Function.Surjective, reindex_equiv (equivFin n).symm, ↓isBiInvariant_basicDoubleCoset]
