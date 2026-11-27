/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/TaylorWiles/AuxPlaceOperators
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/TaylorWiles/AuxPlaceOperators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.TaylorWiles.AuxPlaceOperators. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/TaylorWiles/AuxPlaceOperators.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.TaylorWiles.HeckeAlgebra
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Taylor–Wiles freeness at auxiliary primes, up to the orders of the stabilisers.
This file treats integral forms of principal level on a definite unitary group, for any finite
subgroup of the product of the finite general linear groups at the auxiliary places. Freeness is
obtained only up to a fixed integer and is expressed as one Higman operator. Source: Taylor–Wiles,
Ann. Math. 141 (1995); Clozel–Harris–Taylor, Publ. IHES 108 (2008).

This file: Finite groups at auxiliary places act on forms; Higman operator up to stabiliser
orders. -/

noncomputable section

attribute [-simp] mul_apply one_apply

namespace BaseLevel

open Pi Fintype Polynomial Algebra Gf Kf MonoidHom Subgroup MulAction Module
variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E : Type} [Field E] [CMType E]
  {n : Type} [Fintype n] {V : Space E n 1} {κ : Weight E}
  {J : Type} [Fintype J] {ν : ℕ} {c : ℕ} (D : BaseLevel V κ c) [Algebra E Ω]
  (Q : TaylorWilesPlaces E J (ℓ ^ ν)) (j : J)

/-- The isomorphism ∏_j GL_N(k_{w_j}) ≅ ∏_j GL_n(k_{w_j}), N = |n|, that relabels rows and
columns along a chosen ordering of the index set n. -/
abbrev reindexAux {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : Type}
    [Fintype n] {J : Type} {ν : ℕ} [Algebra E Ω] (Q : TaylorWilesPlaces E J (ℓ ^ ν)) :=
  MulEquiv.piCongrRight fun j ↦
  (reindexGL (R := ResField (Q.w j)) (equivFin n)).symm

/-- The lattice-preserving operators on forms of principal level that are restrictions of
O-combinations of translations by elements of G_f supported at w_j and its conjugate. -/
def localOps : Subalgebra EllAdicIntegers (D.integralEnd Q.w) := ⟨⟨⟨⟨{a | ∃ b : localGroupAlgebra
  (Q.w j), ∀ y, (a.1 y).1 = b.1 y}, by
    rintro _ _ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simp [ha, hb]⟩⟩, 1, by simp⟩,
  by
    rintro _ _ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simp [ha, hb]⟩, 0, by simp⟩, (⟨· • 1, by simp⟩)⟩

/-- The action of ∏_j GL_n(k_{w_j}) on forms of principal level at the auxiliary places by
translation through lifts; it preserves the integral forms. -/
def residueRep : (∀ j, GL (Fin (card n)) (ResField (Q.w j))) →* D.integralEnd Q.w := by
  let R := levelRep (H := ⊥) D.repOff 1 (reindexAux Q).toMonoidHom (by simp)
  use! fun g ↦ ⟨(D.repOff _).restrict fun y h ↦ ⟨D.map_mem_Y _ (fun _ ↦ .map (Gf.ext (by aesop)) _)
    h.1, (R g ⟨y, h.2⟩).2⟩, fun y h _ m ↦
    h _ (mul_mem m (Kf_le_localLevel (componentOn_mem_Kf (by simp))))⟩ <;> intros <;> ext y : 3
  exacts [congr($R.map_one ⟨_, y.2.2⟩), congr($(map_mul R ..) ⟨_, y.2.2⟩)]

variable {D Q j} (hQ : ∀ j, D.IsOffLevel ![] (Q.w j))

/-- A form of principal level at the auxiliary places has level K exactly when it is fixed by
the group ∏_j GL_n(k_{w_j}). -/
lemma mem_baseLevel_iff_residueRep_fixed {y} : ↑y ∈ D.formsOfLevel ![] ↔ ∀ g,
  (D.residueRep Q g).1 y = y := ⟨fun h g ↦ Subtype.ext ((h.2
  ⟨_, _, funext nofun, rfl⟩).trans (by simp)), (⟨y.2.1, fun ⟨_, k, _, rfl⟩ ↦ apply_liftResidue_eq
  (χ := 1) ⟨_, y.2.2⟩ k ((reindexAux Q).right_inv _).symm ▸ congr($(· _).1).trans (by simp)⟩)⟩

lemma localOps.commute_heckeAction {a} (ha : a ∈ D.localOps Q j) t :
  Commute (BaseLevel.heckeAction t) a := ha.elim fun b h ↦ Subtype.ext <| formEnd_ext fun x _
  _ ↦ by ext; simp [BaseLevel.heckeAction, systemAction, diagOp_apply _ x, Isotypic.map_mem b.2, *]

include hQ

lemma residueRep_mulSingle (k : Kw _ _) y : ((D.residueRep Q (mulSingle j (reduceGL k))).1 y).1 =
  localFormRep V κ (Q.apart.2 j j) k y := .trans (apply_liftResidue_eq (χ := 1) ⟨_,
  y.2.2⟩ _ ((reduceFamily_atSplit j ⟨_, k.2.elim (⟨reindexGL (equivFin n).symm ·, · ▸ rfl⟩)⟩).trans
  (Function.update_eq_iff.2 (by aesop)))) congr($(repOff_eq_of_mem_trivialOn _ (supportedOn_compl.le
  (supportedOn_mono (by simp_all [IsOffLevel]) (atSplit_mem_supportedOn _ _)))) y)

lemma residueRep_mem_localOps : ∀ g, D.residueRep Q (mulSingle j g) ∈ D.localOps Q j :=
  reduceGL_surjective.forall.2 (⟨⟨_, subset_adjoin ⟨_, by simp, rfl⟩⟩, residueRep_mulSingle hQ ·⟩)

omit [Fintype J] in
/-- A polynomial in the Hecke operator of IgI, I the pro-Iwahori, after an operator in
`BaseLevel.localOps` with values in pro-Iwahori-fixed forms, is again in `BaseLevel.localOps`. -/
lemma exists_localOps_aeval_hecke {a} (ha : a ∈ D.localOps Q j) g (G : EllAdicIntegers[X]) :
  let ρ := localFormRep V κ (Q.apart.2 j j); (∀ y, (a.1 y).1 ∈ levelSpace ρ.ρ proIwahori) →
    ∃ b ∈ D.localOps Q j, ∀ y, (b.1 y).1 = aeval (heckeCoset ρ.ρ proIwahori g) G (a.1 y).1 := by
  intro ρ h; obtain ⟨⟨p, q, l, _⟩, c, t⟩ := hQ j, adjoin_singleton_le (S := _ ⊓ endPreserving
    (.restrictScalars EllAdicIntegers (levelSpace ρ.ρ proIwahori))) ⟨heckeFun_mem_localGroupAlgebra
    _ _, fun _ ↦ (isBiInvariant_doubleCoset isOpen_proIwahori g).heckeFun_mem⟩
    (G.aeval_mem_adjoin_singleton EllAdicIntegers (heckeCoset ..))
  generalize aeval (heckeCoset ρ.ρ proIwahori g) G = T at *
  use ⟨(T ∘ₗ _ ∘ₗ a.1).codRestrict _ fun y ↦
    ⟨D.map_mem_Y _ (fun _ ↦ commute_of_mem_localGroupAlgebra c (by simp [*])) (a.1
    y).2.1, fun k ↦ ?_⟩, (localGroupAlgebra_le_endPreserving l c _ <| a.2 · ·)⟩,
    ha.imp' (⟨T, c⟩ * ·) fun _ e y ↦ congr(T $(e y)), fun _ ↦ rfl
  -- `k` is an element of the Iwahori subgroup at `w j` times an element off `w j`
  have e := commute_of_mem_localGroupAlgebra c (y :=
    componentOn n (.conjClosure D.S)ᶜ k * atSplit (Q.apart.2 j j) (k.1⁻¹.atPlace _)) (by simp [*])
  simpa [by simpa [ρ, -Representation.inv_apply_eq_iff] using And.intro (a.1 y).2.2 (forall_and.2
    ⟨h y, t _ (h y)⟩ ⟨reindexGL (equivFin n) (k.1.atPlace _),
    (mem_Kf_iff.1 (levelOf_le_Kf k.2) _).elim (⟨reindexGL _ ·, ·.rec rfl⟩), by
    have := fun a b ↦ reduceAt_eq_zero.1 ((map_eq_one n).1 (congrFun (mem_levelOf.1 k.2).2 j) a b)
    clear * - this
    simp [reindex_equiv (equivFin n), Gf.atPlace, apply_ite, ite_apply] at *
    grind⟩⁻¹)] using congr($e (a.1 y).1)

/-- Higman's criterion up to c: for a finite group Δ embedded by φ in ∏_j GL_n(k_{w_j}), some
lattice-preserving operator Ψ on forms of principal level has ∑_{g∈Δ} g⁻¹Ψg = c, a common multiple
of the stabiliser orders.

Known result: Taylor–Wiles freeness at auxiliary primes, up to the orders of the stabilisers. -/
lemma exists_higman_operator {Δ} [Group Δ] [Fintype Δ] (φ : Δ →* _) (hφ : (⇑φ).Injective) :
    ∃ Ψ, ∑ g, D.residueRep Q (φ g⁻¹) * Ψ * D.residueRep Q (φ g) = c := by
  let π := reduceFamily (n := n) Q.w
  let ψ := (reindexAux Q).toMonoidHom.comp φ
  let s := orbitRel (ψ.range.comap π) (_ ⧸ V.Γf)
  let o q := (Quotient.mk s q).out.out
  -- a weight that adds up to `c` along `Δ`, as the orders of all stabilisers divide `c`
  choose w a using fun g ↦ ((card_comap_dvd_of_injective _ ψ (by simpa [ψ])).trans
    (card_map_dvd _ π)).trans (.trans (card_comap_dvd_of_injective _
    (.comp (MulAut.conj g⁻¹) (Kf ..).subtype) (by simp)) (D.card_aut_dvd g⁻¹))
  let u q d := if ∃ k, o q = k • q ∧ π k = ψ d then w (o q) else 0
  have t q y d (m : π y = ψ d⁻¹) : u (y⁻¹ • q) 1 = u q d := by
    unfold u; rw [(mul_right_surjective y).exists]
    simp [m, mul_smul, mul_inv_eq_one, o, @Quotient.sound _ s (y⁻¹ • q) q ⟨⟨y, _, m.symm⟩⁻¹, rfl⟩]
  have c q : c = ∑ d, u q d := by
    obtain ⟨⟨x, k, e⟩, f : x • q = _⟩ : s (o q) q := by simp [o, Quotient.mk_out]
    unfold u; simp +singlePass [reindex_equiv (Equiv.mulRight k), reindex_equiv (Equiv.mulRight x)]
    simpa [Finset.sum_ite, Fintype.card_subtype, *, mul_smul, -Subtype.exists, mul_assoc,
      ← QuotientGroup.eq (s := V.Γf)] using! a _
  have r x : π ⟨_, componentOn_mem_Kf (S := (.conjClosure D.S)ᶜ) x.2⟩ = π x :=
    funext fun j ↦ (div_mem_ker_iff _).1 (reduceAt_eq_one_of_atPlace (by simp [forall_and.1 hQ]))
  have b q x m := t q ⟨x, _⟩ 1 (by simpa using (mem_levelOf (H := ⊥).1 m).2)
  let T : End ℂ (V.forms κ) := .restrict ((u ⟦·⁻¹⟧ 1) • 1) fun f m ↦
    ⟨(rightStab _ ⊓ levelOf ..).isOpen_mono (fun x m g ↦ congr($(b ↑g⁻¹ x m.2) • $(m.1 g)))
    (.and m.1 isOpen_levelOf), by simp [m.2 _, -nsmul_eq_mul]⟩
  have C k m : Commute (V.formTranslation κ k) T :=
    LinearMap.ext (Subtype.ext <| funext fun g ↦ congr($(b ↑g⁻¹ k m) • ·.1 _))
  use! T.restrict fun f m ↦ ⟨D.map_mem_Y T (C _ <| inf_trivialOn_le_levelOf
    ⟨componentOn_mem_Kf ·.2, by simp_all [IsOffLevel]⟩) m.1, map_mem_levelSpace_of_commute m.2
    fun ⟨_, x, e, rfl⟩ ↦ C _ ⟨_, (r x).trans e, rfl⟩⟩, fun _ ↦ (nsmul_mem · _ ·)
  ext y g i
  simp [-map_inv, c ↑g⁻¹, -nsmul_eq_mul]
  exact congr(∑ d, $(t ↑g⁻¹ _ d ((r _).trans (reduceFamily_liftResidue _))) •
    ($(map_mul_eq_one (D.residueRep Q) (by simp)).1 y).1.1 ..)
