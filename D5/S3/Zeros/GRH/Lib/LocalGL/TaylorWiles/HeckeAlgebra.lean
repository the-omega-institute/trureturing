/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/TaylorWiles/HeckeAlgebra
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/TaylorWiles/HeckeAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.TaylorWiles.HeckeAlgebra. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/TaylorWiles/HeckeAlgebra.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.BaseLevel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Taylor–Wiles freeness at auxiliary primes, up to the orders of the stabilisers (known
result; see Lib.LocalGL.TaylorWiles.AuxPlaceOperators).

This file: Algebra of scalar systems preserving integral forms, its action and closedness. -/

open Gf LinearMap Module Submodule

variable {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [CMType E]
  {n} [Fintype n] {V κ c} {D : BaseLevel (n := n) V κ c} {J} [Finite J] {L : J →
  FinPlace E} (t : D.Eigensystem L → PadicAlgCl ℓ)

namespace BaseLevel

instance : FiniteDimensional ℂ (D.formsOfLevel L) := have ⟨_, χ, o, H⟩ := D.exists_level
  .of_fg ((Finite.iff_fg.1 (V.finite_formTranslation_levelSpace κ (o.and isOpen_levelOf)
    (χ.comp (Subgroup.inclusion (inf_le_left (b := levelOf L ⊥)))))).of_le fun f h ⟨k,
    a⟩ ↦ congr(V.formTranslation κ $(k.ext (k := componentOn n D.S k
    * componentOn n (.conjClosure D.S)ᶜ k) (by simp; grind)) f).trans (.trans (by aesop) (H h.1 _)))

noncomputable instance : Fintype (D.Eigensystem L) := Set.Finite.fintype
    (LinearIndependent.of_comp (formsOfLevel L).subtype (v := (⟨_, ·.2.choose_spec.1.2⟩))
    (Isotypic.iSupIndep_val.linearIndependent _ (·.2.choose_spec.1.1) (·.2.choose_spec.2))).finite

omit [PadicIso ℓ] in
/-- For a finite family L, all but finitely many places w satisfy `BaseLevel.IsOffLevel`: w, w̄ ∉ S,
w ∤ ℓ, and, if w splits, each isotypic form of level L is spherical at w with the chosen
eigenvalues of its system. -/
lemma eventually_isOffLevel : ∀ᶠ w in .cofinite, D.IsOffLevel L w := by
  simpa [IsOffLevel, Set.toFinite, FG.of_finite, fun x : Isotypic V κ ↦ fg_induction (motive :=
    fun U _ ↦ U ≤ x.1 → ∀ᶠ w in Filter.cofinite, U ≤ eigenformsAt V κ w (x.heckeEigenvalues w))
    (by simp [Isotypic.mem_iff_eventually]) (by simp_all [-Filter.eventually_cofinite]),
    -Filter.eventually_cofinite] using eventually_notMem_star_notMem ..

lemma formsOfLevel_le_levelSpace : D.formsOfLevel L ≤ levelSpace (V.formTranslation κ)
  (Kf .. ⊓ trivialOn n ↑((Set.finite_range L).toFinset ∪ D.S)) := fun _ h ⟨k, _⟩ ↦
  D.repOff_eq_of_mem_trivialOn k (by aesop) ▸ h.2 ⟨k, inf_trivialOn_le_levelOf (by aesop)⟩

/-- For a function t from systems to Q̄_ℓ, a chosen endomorphism of the space of forms acting on
the isotypic space of each system x by the scalar ι⁻¹(t(x)). -/
@[irreducible] noncomputable def diagOp : End ℂ (V.forms κ) := DFinsupp.lsum ℕ
    (fun x ↦ ιℓ.symm (t x) • x.1.1.subtype) ∘ₗ (DFinsupp.lsum ℕ (·.1.1.subtype)).leftInverse

omit [Finite J] in
lemma diagOp_apply x {f} (m : f ∈ x.1.1) : diagOp t f =
  ιℓ.symm (t x) • f := by simp [diagOp, by simpa using (leftInverse_apply_of_inj
  (ker_eq_bot.2 Isotypic.iSupIndep_val.dfinsupp_lsum_injective) (.single x ⟨f, m⟩))]

/-- The space `BaseLevel.formsOfLevel` is spanned by its eigenforms: a subspace N containing its
intersection with every isotypic space of level L contains all of it. -/
lemma formsOfLevel_le_of_eigensystem {N} (H : ∀ x : D.Eigensystem L, x.1.1 ⊓ D.formsOfLevel L ≤ N) :
  D.formsOfLevel L ≤ N := (le_span_isSphericalOff _ formsOfLevel_le_levelSpace fun w _ a b _ _ h ↦
  ⟨D.map_mem_Y _ (fun _ ↦ by ext; simp_all [heckeSplit_comm_of_trivialOn]) h.1, fun k ↦ by
  simp_all [mem_Kf_iff.1 (levelOf_le_Kf k.2), ← heckeSplit_comm_of_atPlace_mem,
    levelSpace_le_sphericalAt a b (formsOfLevel_le_levelSpace h)]⟩).trans (span_le.2 fun _ ⟨a, _,
  h⟩ ↦ (exists_isotypic_of_isSphericalOff h).elim (H ⟨·, _, by tauto⟩ ⟨·.1, a⟩))

lemma formEnd_ext {a b : D.FormEnd L} (H : ∀ (x : D.Eigensystem L) y, ↑y ∈ x.1.1 → a y = b y) : a =
  b := a.ext fun y ↦ by simpa using formsOfLevel_le_of_eigensystem (N :=
  (eqLocus ..).map (formsOfLevel L).subtype) (fun x _ ⟨p, q⟩ ↦ ⟨_, H x ⟨_, q⟩ p, rfl⟩) y.2

/-- The O-algebra map sending a function t from systems to Q̄_ℓ to the operator on
`BaseLevel.formsOfLevel` L that multiplies forms of the system x by ι⁻¹(t(x)). -/
noncomputable def systemAction : (D.Eigensystem L → PadicAlgCl ℓ) →ₐ[EllAdicIntegers] D.FormEnd
  L := by use! fun t ↦ (diagOp t).restrict (formsOfLevel_le_of_eigensystem fun x f ⟨p, q⟩ ↦
  mem_comap.2 (diagOp_apply t x p ▸ smul_mem _ _ q)) <;> intros <;> exact formEnd_ext fun x f m ↦ by
            ext; simp [diagOp_apply _ x m, ← iota_ell_algebraMap] <;> ring

/-- The Hecke algebra: functions t from systems to Q̄_ℓ such that scaling the x-component by
ι⁻¹(t(x)), for each system x, keeps integral forms of `BaseLevel.formsOfLevel` integral. -/
noncomputable def heckeAlgebra L := (D.integralEnd (J := J) L).comap systemAction

/-- The O-algebra homomorphism sending t in the Hecke algebra to the lattice-preserving operator
that multiplies forms of the system x by ι⁻¹(t(x)). -/
noncomputable def heckeAction : D.heckeAlgebra L →ₐ[EllAdicIntegers] D.integralEnd L :=
  (systemAction.comp (heckeAlgebra L).val).codRestrict _ (·.2)

/-- The Hecke algebra is closed in the space of Q̄_ℓ-valued functions on systems. -/
lemma isClosed_heckeAlgebra :
  IsClosed (SetLike.coe (D.heckeAlgebra L)) := show IsClosed {t | ∀ f _ g _ i, (_ : NNReal) ≤ _} by
  simp [systemAction, diagOp, ↓Set.ofPred_forall, DFinsupp.sumAddHom_apply]; repeat'
      first | apply isClosed_iInter | apply isClosed_le | fun_prop | intro
