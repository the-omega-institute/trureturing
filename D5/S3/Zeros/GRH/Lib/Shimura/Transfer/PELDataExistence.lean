/- GID: D5/S3/Zeros/GRH/Lib/Shimura/Transfer/PELDataExistence
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Shimura/Transfer/PELDataExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Shimura.Transfer.PELDataExistence. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Shimura/Transfer/PELDataExistence.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Geometry.Lefschetz
import D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori.ExponentOfLabel
import D5.S3.Zeros.GRH.Lib.GaloisRep.Main.SplitPlaceCount
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Character.WeylTrace
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Transfer of eigensystems between inner forms of a unitary group differing at a
real place. It is shown here only that the Hecke eigensystem of a definite form occurs, in each
Hodge weight, on the variety for signature (1, n-1), for n odd and with a cuspidal type at one split
place. The proof compares two finite counts, without stabilisation. Source: Harris and Labesse,
Conditional base change for unitary groups, Asian J. Math. 8 (2004), Thm 2.1.2; Labesse, Changement
de base CM et séries discrètes (2011), Thm 5.4; count as in Goresky and MacPherson, The topological
trace formula (2003), and Shimura, On the trace formula for Hecke operators, Acta Math. 132 (1974).

Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation (known
result; see Lib.Shimura.IntegralModel.ModelExistence).

Part of: Simple trace formula: Hecke trace on a definite group; non-elliptic terms vanish (known
result; see Lib.Shimura.TraceFormula.MarkedEqDefinite).

This file: Regular test function with cuspidal type that does not kill the given vector. Eigensystem
of a definite form occurs in each Hodge weight for signature (1,n-1). Lagrangians exist; PEL data
with odd theta group, good at the safe places. -/
seal Finset.univ Finset.sum Finset.prod

section

open NumberField Matrix Polynomial Submodule Set Subgroup Valued Fin Finset Fintype LinearMap
variable {E} [Field E] [NumberField E] [IsCMField E] {a 𝔑 W} [AddCommGroup.{0} W] [Module ℂ W]

/-- w₀ ≠ w₁, w₁ ∣ 𝔑, w̄₀, w̄₁ ∤ 𝔑; through `conjAtSplit`, K(𝔑) at w₀ lies in J ≤ GL_n(O_w₀),
at w₁ in I₁; χ satisfies `IsCuspidalType`; J acts on v ≠ 0 by χ, GL_n(O_w₁) trivially. -/
structure IsTestVector 𝔑 (π : Representation ℂ (GL (Fin a) (𝔸f E)) W) (v : W) (w₀ w₁ :
  SplitFinPlace E) {J} χ where
  places : w₀ ≠ w₁.1 ∧ 𝔑 ∉ (star w₀.1).1 ∧ 𝔑 ∈ w₁.1.1 ∧ 𝔑 ∉ (star w₁.1).1
  level₀ : (levelGU (Fin a) 𝔑).comap (conjAtSplit w₀) ≤ J ∧ J ≤ Kw _ _
  isCuspidalType : IsCuspidalType J χ
  level₁ : (levelGU (Fin a) 𝔑).comap (conjAtSplit w₁) ≤ proIwahori
  ne_zero : v ≠ 0
  mem_levelSpace : v ∈ levelSpace (π.comp (conjAtSplit _)) J χ
  fixed : v ∈ levelSpace (π.comp (conjAtSplit w₁)) (Kw ..)

/-- Let 𝔑 ≠ 0, w̄ ∤ 𝔑, K(𝔑) ∩ GL(E_w) ≤ ker χ ≤ J ≤ GL(O_w), z central, zt in `GUPlus`.
Some Hecke element b supported on Jzt sends K(𝔑)-fixed vectors to χ-eigenvectors, and Tz⁻¹bx
= y whenever T(jt·x) = χ(j)y for all j in J. -/
lemma exists_local_hecke_element (π : Representation ℂ _ W) {w J z} (c : J ≤ Kw ..) (χ :
  J →* ℂ) (hχ : ∀ g, conjAtSplit w g ∈ levelGU (Fin a) 𝔑 → ∃ h, χ ⟨g, h⟩ = 1) (hw :
  𝔑 ∉ (star w.1).1) t (cz : ∀ g, Commute g z)
  (o : z * conjAtSplit w t ∈ GUPlus E _) : let r (j : J) := conjAtSplit w j * (z * conjAtSplit w t)
  ∃ b : heckeAlgebra _ ℂ 𝔑, b.1 ∈ spanOn ℂ (Set.range r) ∧
    b.1 ∈ fixedToEigen (levelGU _ 𝔑) (conjAtSplit w) J χ ∧ ∀ {x} T y,
    (∀ j, T (π (conjAtSplit w (↑j * t)) x) = χ j • y) → (T * π z⁻¹) (π.asAlgebraHom b x) = y := by
  intro r; simp_rw [Subtype.exists, bex_def]; have n j : χ j ≠ 0 := (χ.toHomUnits j).ne_zero
  let L : OpenSubgroup (type_of% t) := ⟨_, isOpen_comap_conjAtSplit (by bound : 𝔑 ≠ 0)⟩
  let U := (L ⊓ L.comap (MulAut.conj t⁻¹) (IsTopologicalGroup.continuous_conj _)).subgroupOf J
  have := U.fintypeOfIndexNeZero ((isCompact_Kw _).relIndex_ne_zero
    (L ⊓ _).2 ∘ relIndex_eq_zero_of_le_right c); let f j := (χ j * this.card)⁻¹
  refine ⟨∑ q : _ ⧸ U, f q.out • .single (r q.out) 1, (fun H ↦ .symm ⟨H, mem_heckeAlgebra hw H.1
    (fun | _, ⟨j, rfl⟩ => ⟨mul_mem ⟨by simp, (conjAtSplit_mem_intGL_iff.2 (c j.2)).isIntMatrix_inv⟩
    o, by simp_all [r]⟩) fun _ _ _ _ _ x l ↦ ((hχ _ l.2).2 ▸ H.2.1 x _ :)⟩) ⟨sum_smul_mem _ _ (by
    aesop (add simp spanOn)),
    fun _ _ _ π _ h ↦ ?_, by simp_all [f, r, ← smul_assoc, (cz _).left_comm]⟩⟩
  simpa [r, heckeFun] using heckeFun_mem_levelSpace (χ' := χ.domRestrict ⊤) (π := π.comp
    (.domRestrict ..)) (toFinite _) (fun _ k ↦ by simp [f, (hχ k k.2.1).2]) (by simp [*, field])
    (map_mem_levelSpace_of_commute (fun k : U ↦ by simpa using h ⟨_, k.2.2⟩) fun _ ↦ (cz _).map π)

/-- Let φ be K(𝔑)-fixed with `IsTestVector`, c a Hecke element supported on similitudes trivial at
w₁, cφ = φ. For some Hecke element b and all m ≥ 1: (bc)^m φ ≠ 0, (bc)^m is regular, and sends
K(𝔑)-fixed vectors to χ-eigenvectors of J at w₀. -/
lemma exists_test_function {w₀ w₁ J χ π} {φ : W} (h₂ : φ ∈ levelSpace π (levelGU (Fin a) 𝔑)) :
  IsTestVector 𝔑 π φ _ w₁ χ → ∀ {c : heckeAlgebra _ ℂ 𝔑}, c.1 ∈ spanOn ℂ (GU E _ ⊓ (dualComponent
  w₁).ker).carrier → π.asAlgebraHom c φ = φ → ∃ b, ∀ m, π.asAlgebraHom ((b * c) ^ m).1
  φ ≠ 0 ∧ let f := (b * c) ^ (m + 1); IsRegularHecke f ∧ ↑f ∈ fixedToEigen (levelGU _ 𝔑)
    (conjAtSplit w₀) J χ := fun ⟨⟨h, n₀, n₁, hw₁'⟩, ⟨hK, hJ⟩, _, M, h₁, h₃, h₄⟩ c hc hv ↦ by
  let ρ := Rep.of (smoothVectorRep (π.comp (conjAtSplit w₁))); have ⟨t, ht, I⟩ :=
    exists_iwahoriHeckeHom_injective ρ (v_uniformizer _)
  have ⟨N, n, hz⟩ := exists_forall_mul_mem_Ô (conjAtSplit _ (diagGL t)).2.uncurry
  have ⟨b₀, u₀, a₀⟩ := exists_local_hecke_element π hJ χ (fun g hg ↦
    ⟨hK hg, smul_left_injective _ h₁ ((h₃ _).symm.trans (h₂ ⟨_, hg⟩))⟩) n₀ 1 .one_right (by simp)
  obtain ⟨b₁, u₁, a₁⟩ := exists_local_hecke_element π (z :=
    (.scalar _ (principalIdele (.mk0 N (mod_cast n))))⁻¹) (sep_subset ..) 1 (by simpa) hw₁' _
    (by simp [commute_scalar_GL]) ⟨mul_mem ⟨N * N, by simpa, 1, gram_inv_of_gram_eq (by
    simp [smul_one_eq_diagonal, -map_natCast])⟩ (by simp), by simpa [← nsmul_eq_mul'] using! hz⟩
  have o := spanOn.mul u₀ hc (forall_mem_range.2 fun _ _ ↦ Subgroup.mul_mem _ (by
    simp [dualComponent, evalAt_conjAtSplit_of_ne _ h.symm (by grind [star_star])]))
  have C : Commute (b₀ * c) _ := Subtype.ext (Commute.span_left (Set.forall_mem_image.2 fun _ h ↦
    .span_right (by simp (maxDischargeDepth := 3) [commute_conjAtSplit h, commute_scalar_GL]) _ u₁)
    _ o)
  have d := spanOn.mul (D'' := {g | ∃ s, StrictMono (v <| s · |>.1) ∧ ∃ k l : proIwahori, dualComponent _ g = k.1 *
    diagGL s * l.1}) u₁ o (fun | _, ⟨j, rfl⟩, g, p => ⟨(.mk0 N (mod_cast n) * t ·), by
       simpa [StrictMono, zero_lt_iff, n], j, 1, by simp [↓map_mul, ↓dualComponent_conjAtSplit, ↓MonoidHom.mem_ker.1 p.2,
       dualComponent, invTransposeGL, Equiv.symm, Units.ext_iff, Matrix.map_natCast, map_zero]⟩)
  use b₁ * b₀, mul_assoc b₁ .. ▸ fun m ↦ ⟨(?_ : _ ∈ (levelSpace (π.comp (conjAtSplit w₁))
    proIwahori).carrier \ {0}).2, fun y x hy ↦ ?_, fun _ _ _ _ _ h ↦ ?_⟩
  induction' m with m ih; simpa [*] using (h₄ ⟨·, ·.1⟩)
  simpa [pow_succ', ((C.mul_right rfl).pow_right _).right_comm, hv, -SubmonoidClass.coe_pow,
    -mem_levelSpace, by simpa using a₀.2 1 φ (by simpa using h₃)] using (Submodule.subtype _ ∘ₗ
    compactMean ρ.ρ proIwahori).exists_extend.elim fun T e ↦ ⟨a₁.1 ((_ : heckeAlgebra ..).2.2 h₂),
    ne_zero_of_map ((a₁.2 T _ fun j ↦ by simpa using! congr($e (ρ (j * _) ⟨_, _⟩))).trans_ne (mt
    ((injective_iff_map_eq_zero _).1 I ⟨⟨_, .mono (residuePreimage ..).mem_nhds_one (by simpa using!
    ih.1)⟩, (Subtype.ext <| ih.1 ·)⟩ ∘ Subtype.ext ∘ Submodule.coe_eq_zero.1) (ih.2 congr($(·)))))⟩
  obtain ⟨g, ⟨t, ht, k, l, h⟩, e⟩ := spanOn.exists_mem_of_cosetFn_ne_zero (m.rec (by simpa) fun _ ↦
    (spanOn.mul · d (by exact fun _ ⟨t, ht, k, l, h⟩ _ ⟨s, hs, k', l', _⟩ ↦
    (exists_unipotent_conj_mem_proIwahori hs.monotone (l * k').2).elim fun x ⟨hx, H⟩ ↦
    ⟨t * s, by simpa using! ht.mul hs, k * ⟨_, conj_unitriangular_mem_proIwahori ht.monotone hx⟩,
    ⟨_, H⟩ * l', by simp [*, mul_assoc]⟩)) : _ ^ (m + 1) ∈ _) hy
  choose c _ d hd e using exists_twisted_conj_diag ht 1 (by simp) continuous_id (⟨·,
    rfl⟩) (Set.mul_mem_mul (Set.mul_mem_mul k.2 rfl) (mul_mem l.2
    (M (conjAtSplit_dualComponent hw₁' (QuotientGroup.eq.1 e)).1)))
  erw [← separable_map (algebraMap _ (LocField w₁.1)), ← charpoly_map, ← charpoly_transpose,
    ← charpoly_units_conj' (_ * c), show _ * (dualComponent _ (toFinGL y⁻¹)).1 * _ =
    _ by simpa [mul_assoc, h] using congr($e.1), charpoly_diagonal, separable_prod_X_sub_C_iff]
  exact .of_comp (f :=
    v) (.subst (by simpa [funext_iff] using v_diag_eq_one_of_mem_proIwahori hd) ht.injective)
  erw [pow_succ', ← C, mul_assoc, mul_assoc, map_mul]; use a₀.1 ((c * _).2.2 h)

attribute [-simp] univ_val_map

/-- For a odd and E⁺ ≠ ℚ, the weight κ extends to ξ on GL_a(E), with x̄ ∈ ℚ(√−d₀)^× acting by
s₀(x)^{−μ} s̄₀(x)^{−A}. For σ over s₀, a CM type with Φ(v₀) = σ alone over s₀ and neat
level, eigenvalues of test vectors in `definiteForms` occur in weights z + μ ≥ 0, z the
jumps of κ at σ.

Known result: Transfer of eigensystems between inner forms of a unitary group differing at a real
place. -/
lemma exists_occursInWeight {E} [Field E] [CMType E] {a d₀} [HasQuadSubfield d₀ E] (ha : Odd a) (i :
  QuadField d₀ →+* E) s₀ (κ : Weight E) : ∃ (ξ : Representation ℂ (GL (Fin a) E) _) (μ N : ℕ) (A : _
  → ℤ), A s₀ = μ ∧ (∀ y, (stdSpace E _).weightRep κ.1 κ.2 (entryConj y) = ξ y.1) ∧ (∀ x : (QuadField
  d₀)ˣ, ξ (.scalar _ (star (x.map i))) = (∏ s, s x ^ (-A s)) • 1) ∧ ∀ σ, σ.comp i = s₀ → ∀ z ∈ jumps
  κ a σ, 0 ≤ z + μ ∧ ∀ [Ψ : CMBase E] {𝔑 w₀ w₁ J χ φ} {θ : SafePlace 𝔑 → ℕ → ℂ}, Ψ.Φ v₀ = σ →
  (∀ v ≠ v₀, (Ψ.Φ v).comp i ≠ (Ψ.Φ v₀).comp i) → IsNeat (Fin a) 𝔑 → IsTestVector 𝔑 (rightRegular ..)
  φ w₀ w₁ (J := J) χ → φ ∈ definiteForms 𝔑 ξ → (∀ w j, (rightRegular ..).asAlgebraHom (heckeSum _ ℂ
  w.1 j) φ = θ w j • φ) → OccursInWeight a N.succ θ (z + μ).toNat := have := NeZero.of_pos ha.pos
  have hu :=
    eq_univ_of_card {star s₀, s₀} (by simp [NumberField.Embeddings.card, QuadField.finrank_K])
  let p := (.comp · i = s₀)
  have hs σ : (∀ x, σ (i x) = ite (p σ) (s₀ x) (star s₀ x)) ∧ (p (star σ) ↔ ¬p σ) := show _ ∧
    (star (σ.comp _) = _ ↔ _) by grind [Finset.mem_univ (σ.comp i), RingHom.comp_apply, star_star]
  let θ := MonoidHom.mk' (fun (z : GL (Fin a) E) σ ↦ ite (p σ) (z.map σ)
    (transposeGL (z⁻¹.map (star σ)))) (by simp +contextual [funext_iff, apply_ite, Units.ext_iff])
  let u σ (j : Fin a) := κ.2 (.mk σ) + (diagramWeight (rankAt (Fin a)) κ.1 (.mk σ, j.rev) + j)
  let k σ j := ite (σ = Φ (.mk σ)) (a - 1 - u σ j.rev) (u σ j)
  (Finite.exists_le (Int.natAbs ∘ k.uncurry)).elim fun m hm ↦ by
  choose l hm using fun σ j ↦ CanLift.prf (β := ℕ) (m + k σ j) (by grind [hm (σ, j)])
  let q σ := ite (p σ) (genericSchur (l σ)) ((-.X 0) ^ m)
  have hl {R} [CommRing R] (r : Fin a → R) : @rootCoeffEval a _ _ (Finset.univ.1.map r) (.X 0) =
    -Finset.univ.prod r := by simp [*, rootCoeffEval, coeff_zero_eq_eval_zero, eval_prod, prod_neg]
  let ξ : _ →* _ := ⟨⟨fun z ↦ ((∏ σ : _ →+* ℂ, σ z⁻¹.1.det) ^ m • weylRep κ.1 κ.2
    (θ z ∘ Φ)).toLinAlgEquiv', by simp⟩, by simp [smul_smul, mul_pow, Pi.mul_comp]⟩
  have V y (h : y.1.charpoly.Separable) :
      (ξ y⁻¹).trace ℂ _ = ∏ σ, rootCoeffEval (y.1.charpoly.map σ).roots (q σ)
  let r σ : Fin a ↪ _ := numberedRoots σ y.1.charpoly
  have hP := isRoot_numberedRoots h
  let x σ : _ ↪ ℂ := ⟨fun i ↦ ite (p σ) (r σ i.rev)⁻¹ (r (star σ) i), fun _ ↦ by grind⟩
  erw [← mul_left_inj' (prod_ne_zero_iff.2 fun v _ ↦ det_vandermonde_ne_zero_iff'.2 (x (Φ v)).2),
    trace_toLin'_eq, trace_smul, smul_mul_assoc, trace_weylRep _ _ (by simp_all [θ, x, r,
       apply_ite, -coe_units_inv, -IsRoot.def, ← mem_spectrum_iff_isRoot_charpoly])]
  simp [RingHom.map_det, (y.1.map _).det_eq_prod_roots_charpoly, charpoly_map,
    prod_embeddings_eq_prod_pairs, ← Finset.prod_pow, ← prod_mul_distrib]
  congr with v
  have (w : Fin a → ℤ) := by
    simpa [← add_sub_assoc, submatrix] using (det_submatrix_equiv_self (revPerm (n := a)) _).trans
      (det_zpow_add (hP (Φ v)) (1 - a) (a - 1 - w ·.rev))
  have S := (fun σ ↦ rootCoeffEval_genericSchur_mul_det (l σ) (r σ)) (ite (p (Φ v)) id star (Φ v))
  split at S <;> simp [k, u, r, roots_eq_map_numberedRoots, x, *, ← zpow_natCast, mul_zpow, q,
    vandermonde, det_zpow_add (hP _), -_root_.inv_zpow', _root_.inv_zpow] at S ⊢ <;> grind
  refine ⟨ξ, a * numInfPlaces E * m, ∑ σ, (q σ).totalDegree, (if · = s₀ then _ else -_),
    ite_eq_left rfl, fun y ↦ LinearMap.ext fun _ ↦ (stdSpace_weightRep_apply ..).trans ?_,
      fun x ↦ by
    simp +contextual [-prod_mul_distrib, -pow_ite, ξ, weylRep, fun v ↦ (by split <;> simp [θ, *,
      smul_one_eq_diagonal, ← map_inv] : (θ (.scalar _ (star (x.map i))) v).1 = star s₀ x ^ ite (p
      v) 1 (-1 : ℤ) • 1), prod_embeddings_eq_prod_pairs, mul_comm (starRingEnd ℂ _ ^ (a : ℤ)), hs,
      schur_smul, Units.smul_def, smul_smul, ← zpow_natCast, ← _root_.zpow_mul, ← hu,
      ← zpow_sum_of_ne_zero, mul_zpow, ← zpow_add₀, -_root_.zpow_neg, mul_assoc]
    ring, fun σ ↦ Multiset.forall_mem_map_iff.2 ∘ ?_⟩
  simp [-prod_mul_distrib, ξ, prod_embeddings_eq_prod_pairs,
    fun v ↦ by simpa [mul_comm] using congr(Φ v (det $(y.2)))]
  rcongr; simp [θ, entryConj, invTransposeGL, transposeGL, @starRingEnd_apply E, apply_ite,
    Matrix.ite_apply, ← map_inv, inv_eq_left_inv y.2]
  rintro rfl n o; let j := ite (σ = Φ (.mk σ)) id rev ⟨n, Finset.mem_range.1 o⟩
  let d := m * (a - 1 + a * (numInfPlaces E - 1)) + l σ j
  rw [show _ + _ =
    ↑d by simp [d, hm, k, u, diagramWeight_apply, Fintype.card_pos]; clear * - o; grind]
  clear_value ξ; clear * - ha V hl d
  use by simp, @fun Ψ 𝔑 _ w₁ _ _ φ θ h hΨ hN hs hφ _ s c e H ↦ ?_
  have A L := List.prod_hom_rel L (f := tauHecke) (g := ↿θ) (r := fun x t ↦
    ↑x ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier ∧
    (rightRegular ℂ ..).asAlgebraHom x.1 φ = t • φ) ⟨subset_span ⟨1, by bound⟩, by simp⟩
    fun p _ _ h ↦ ⟨spanOn.mul tau_mem_spanOn h.1 fun _ ⟨U, Q⟩ ↦ Q ▸ fun _ ↦ Subgroup.mul_mem _
    ⟨(heckeIsogeny_mem_GUPlus ..).1, by clear * - hs; simp [heckeIsogeny, dualComponent]; erw
    [evalAt_centralScalar_of_ne, evalAt_conjAtSplit_of_ne] <;> simp <;> grind only [IsSafe,
    below_star, star_star, hs.places]⟩, by simp [tauHecke, *, smul_smul, mul_comm]; rfl⟩
  obtain ⟨b, hb⟩ :=
    And.elim (exists_test_function hφ.2 hs (c := ∑ L ∈ s, c L • (L.map tauHecke).prod)) (by
    simp [*, sum_mem, smul_mem, smul_smul, ← sum_smul, -SubmonoidClass.coe_list_prod])
  have T := trace_definiteForms ξ hN; cases T 1 1
  refine ((definiteForms.rep 𝔑 ξ _).isNilpotent_iff_charpoly.2
    ((charpoly_eq_mul_of_trace_pow_add _ ∅ (·) ?_).trans
    (by simp; exact charpoly_zero))).elim fun _ k ↦ (hb _).1 congr($((map_pow ..).trans k) ⟨_, hφ⟩)
  rintro ⟨⟩ <;> simp [↓toMatrix_pow, ← trace_eq_matrix_trace, ← map_pow, -map_mul]
  cases (hb ‹_›).2; rw [pow_succ, ← mul_assoc] at *; choose K L using H _ ‹_›
  let w P (k : Fin a) :=
    ((Lagrange.basis Finset.univ (numberedRoots σ P) k).comp (X * C (numberedRoots σ P k)) * ∏ s,
    rootCoeffEval (lieRoots P (numberedRoots σ P k) s) (q s)).lcoeff ℂ d / #{i | l σ j = l σ i}
  rw [(T _ w).2.2 ‹_› fun y _ ↦ ?_, ← sum_countTerm_marked_eq_definite hN (by simpa) ‹_›
    hs.isCuspidalType ‹_› _ (by simp [Prop.forall_iff, T, K 1])]
  simp_rw [finsum_countTerm_eq_sum _ (K 1), ← (K 1).toFinset.sum_coe_sort, w, ← h, mul_div,
    ← sum_div, div_eq_zero_iff] at *
  exact .inl (map_prod_rootCoeffEval_eq_zero (by simp [sum_eq_add_sum_subtype_ne _ ·, add_assoc])
    algebraicIndependent_emb (by simp [lieRoots, IsAlgClosed.card_roots_eq_natDegree])
    (dotProductBilin ℂ ℂ _ ∘ₗ (lcoeff ..).compLeft _ ∘ₗ mulLeft ..) L)
  rw [← sum_div, ← map_sum, (?_ : Finset.univ.sum _ = C ((ξ y⁻¹).trace ℂ _) *
    ∑ i, X ^ (d - l σ j + l σ i))] <;> simp [d]
  have := sum_lagrange_smul_rootCoeffEval (l σ) (numberedRoots σ y.1.charpoly); subst h
  simp [*, p, roots_eq_map_numberedRoots, ↓@prod_embeddings_eq_prod_pairs _ _ _ _
    Ψ.toPlaceEmbedding, prod_eq_mul_prod_subtype_ne _ v₀, q,
    lieRoots, ↓roots_map_conjugate, @Subtype.prop _ (· ≠ _), ← rootCoeffEval_map, -ite_mul, pow_add,
    (RingHom.injective _).eq_iff, comp_eq_aeval, mul_pow, ← mul_assoc, ← mul_sum,
    ← sum_mul, prod_ite, filter_ne', IsLieRoot] at this ⊢; rw [this]; ring

end

open NumberField InfinitePlace FractionalIdeal Algebra Ideal Nat AddSubgroup QuadField Quotient

attribute [local simp] xiForm map_ofNat RingOfIntegers.ext_iff mul_sub AddChar.map_sub_eq_div

/-- Existence of Lagrangians. For an alternating bimultiplicative pairing `e` on an abelian
group, every isotropic set lies in a subgroup equal to its own annihilator. -/
lemma exists_lagrangian {V G} [AddCommGroup V] [CommGroup G] (e : V → V → G) (l : ∀ x y z, e (x -
  y) z = e x z / e y z ∧ e z (x - y) = e z x / e z y) (h : ∀ x, e x x = 1) S (i : IsChain (e · · =
  1) S) : ∃ Λ : AddSubgroup V, S ⊆ Λ ∧ ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, e x y = 1 := i.exists_maxChain.rec
  fun M ⟨hM, k⟩ ↦ have H x : x ∈ M ↔ ∀ y ∈ M, e x y = 1 := ⟨fun hx y ↦ by grind [hM.1 hx,
    h (x - y), div_eq_one], fun H ↦ hM.2 (hM.1.insert (by tauto)) (by simp) ▸ by simp⟩
  ⟨.ofSub M (hM.nonempty_iff.1 ⟨0⟩) (by grind [=_ sub_eq_add_neg, div_self']), k, H⟩

/-- For E ⊇ ℚ(√−d) stably unramified, σ: E → ℂ, finitely many places B: some CM type with Φ_{v₀}
= σ, other Φ_v ≠ σ on ℚ(√−d), and N prime to B give at each level 0 ≠ 𝔑 ∈ (N) PEL data with
signs, β = (1 + √−d)/2, good at safe places.

Known result: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation. -/
lemma exists_pel n {d E} [Field E] [NumberField E] [IsCMField E] [HasQuadSubfield d E] [NeZero n] [StablyUnram E]
    σ (B : Finset (FinPlace E)) : ∃ Ψ : CMBase E, (Ψ.Φ v₀ = σ ∧ ∀ v ≠ v₀, (Φ v).comp (algebraMap (QuadField d)
    E) ≠ (Ψ.Φ v₀).comp (algebraMap ..)) ∧ ∃ N : ℕ+, (∀ w ∈ B, ↑N ∉ w.1) ∧ ∀ 𝔑 ≠ 0, ↑N ∣ 𝔑 → ∃ D :
    PEL E, D.rank = n ∧ D.𝔑 = 𝔑 ∧ D.β = algebraMap _ _ (c₀ d) ∧ ∀ w, IsSafe 𝔑 w → D.IsGoodAt w.1 :=
  have P c : ∀ᶠ r in .atTop, HasPadding E r c := open Filter Fin Finset in let b := Module.finBasis ℤ _
    let v := append ![c] b
    (b.equivFun.symm.surjective (univ.sum (1 - star v * v))).elim fun n h ↦ map_add_atTop_eq_nat
      (_ + 3) ▸ mem_map.2 (univ_mem' fun _ ↦ ⟨append 1 (append v (@append _
      (∑ i, ((n * n) i).natAbs).succ _ (⇑b + n • 1) 0)), top_unique (b.span_eq ▸ Submodule.span_mono
      fun _ ⟨i, e⟩ ↦ ⟨natAdd _ (castAdd _ (natAdd _ i)), by simp [v, e]⟩), by
    erw [sum_univ_add]; have := congr(star $h)
    simp [v, sum_univ_add, mul_add, add_mul, mul_comm] at *; grind⟩)
  let i := algebraMap (QuadField d) E; .imp (fun c hΨ ↦ ⟨hΨ, by
  let β := algebraMap _ (𝓞 E) (c₀ d)
  obtain ⟨hβ : β = i (c₀ d), r, hr⟩ := rfl, ((P 1).and (P β)).exists_forall_of_atTop
  let s := (r + B.sup FinPlace.q + 2)!
  obtain ⟨_ : _ ≤ s, ha : star β = 1 - β⟩ := self_le_factorial _, by simp [*, ← map_star_CM]; ring
  obtain ⟨ξ, c, h₁, h₂, h₃, m, hm, e⟩ : ∃ ξ c, star ξ = -ξ ∧ (∀ v, 0 < (Φ v ξ).im) ∧ (∀ u ∈ Ô E,
      ψf E (u * (ξ : E)) = 1) ∧ ∃ m ∈ differentIdeal ℤ _, (s * c - 1 : 𝓞 E) = m • ξ := by
    let F := maximalRealSubfield E
    obtain ⟨⟨C, p, -, _, b, -, -, h⟩, ⟨γ, -, i, k, -⟩, μ, e⟩ :=
      exists_hasFundDomain_toAdele (E := E), ‹StablyUnram E›.exists_i_c₀,
      IsDedekindDomain.exists_add_spanSingleton_mul_eq (@coeIdeal_le_one (𝓞 F) _ _ F _ _ (span
      {↑s})) (by simp [spanSingleton_eq_zero_iff, s]) (dual_ne_zero ℤ ℚ one_ne_zero)
    choose c a o e' using by simpa [mem_add, mem_singleton_mul, -Subtype.exists] using one_le.1 e.ge
    obtain ⟨⟨μ, hμ, rfl⟩, y, h, -⟩ := (coeIdeal_differentIdeal ..).ge (spanSingleton_le_iff_mem.1 ((
      le_div_iff_mul_le (by simp)).2 (e ▸ le_add_self))), h ((Φ · (a * γ / 2 / s) - ⟨0, C + C⟩), 0)
    let z : 𝓞 E := ⟨y, by simpa using! (b h).2⟩
    exact ⟨a * γ + ↑(s * (z - star z)), μ • γ * (z - star z) +
      c • 1, by simp [← coe_star_ringOfIntegers, k, mem_maximalRealSubfield_iff_star_eq.1,
      add_comm], fun v ↦ by simp; linarith! [by simpa [field] using (lt_add_of_le_of_pos
      ((Complex.im_le_norm _).trans (dist_pi_le_iff'.1 (b h).1 v)) p)], forall_ψf_mul_eq_one.2 fun e
      h ↦ (map_mul ..).subst (algebraMap_mem_Ô.2 (((mem_inv_iff (by simp)).1 ((
      coeIdeal_differentIdeal ..).le ⟨e, h, rfl⟩) _ (by apply_rules [smul_mem_dual_one (hx := o) ..,
      Submodule.add_mem, coe_mem_one, one_le_dual_one])).choose_spec.2.subst (Subtype.prop _))),
      γ * _, (differentIdeal_eq_differentIdeal_mul_differentIdeal ..).ge (mul_mem_mul (by simp [F])
      (mem_map_of_mem _ hμ)), by
      linear_combination (norm := (simp [smul_def]; ring!)) congr($e'.1 - μ • a * $i)⟩
  let R := s.succ
  have ⟨Λ, hM, hΛ⟩ := exists_lagrangian (ψf E <| xiForm (R ^ 2 * ξ) · ·) (by simp) (by
    simp [← ψf_half, *, ← Matrix.star_dotProduct]) {x : Fin n → _ | torsionClass (R • x) = 0} fun x
    a y b _ ↦ .inl (h₃ (star (R • y) ⬝ᵥ R • x) (sum_mem (by grind [mul_mem, star_mem_Ô,
    torsionClass_eq_zero, Pi.star_apply])) ▸ by simp [star_trivial, -nsmul_eq_mul]; ring_nf)
  rw [← Λ.comap_map_eq_self (f := torsionClass.toAddMonoidHom) (@hM · <| nsmul_mem · _)] at hΛ
  let T := (ofSub {x | ∀ y : Fin n → _, torsionClass y = 0 → ψf E (xiForm (R ^ 2 * ξ) x y) = 1}
    ⟨0, by simp⟩ (by simp_all [← sub_eq_add_neg])).map torsionClass.toAddMonoidHom
  have hc : s.Coprime (.card T) := coprime_of_dvd fun p h hs H ↦ by
    have ⟨P, _, e, l⟩ := exists_isMaximal_dvd_of_dvd_absNorm' h (span {(s * c - 1) * R ^ 2})
     (by_cases (by simp [·]) fun c ↦
      h.dvd_of_dvd_pow (H.trans ((card_torsionBySet_adelicTorsion c).subst
     (T.card_dvd_of_le (K := (Submodule.torsionBySet (𝓞 E) ..).toAddSubgroup) (map_le_iff_le_comap.2
     fun x H ↦ (Submodule.torsionBySet_span_singleton_eq _).ge (torsionClass_eq_zero.2 fun i ↦ by
      simp_rw [mul_smul, ← algebraMap_smul E (_ - _), e, smul_assoc]
      exact forall_ψf_mul_eq_one.1 (fun u h ↦ by simpa [smul_def, mul_left_comm, mul_assoc] using (H
        (Pi.single i (star u)) (by grind [star_mem_Ô, Subring.zero_mem, torsionClass_eq_zero]))) m
        hm))))))
    revert hs l; simp +contextual [R, ← Int.ofNat_dvd, ← @mem_span_singleton ℤ, ← e,
      ← @eq_zero_iff_mem (𝓞 E)]
  have ho := (hc.of_dvd_left (dvd_factorial two_pos le_add_self)).odd_of_left
  refine (@eventually_isCutDegree T (card_pos_iff.1 ho.pos).2 ..).exists.elim fun i hi ↦
    ⟨⟨R ^ i.succ * .card T, by bound [ho.pos]⟩, fun w h ↦ w.2.notMem_of_isCoprime_of_mem
    ((Coprime.mul_right (by simp [R]) hc).of_dvd_left (dvd_factorial w.one_lt_q.le (by grind
    [Finset.le_sup]))).cast w.1.absNorm_mem, fun 𝔑 h0 hN ↦ ⟨⟨β, 𝔑, _, n, _, i, T, Λ.map _, ha, by
    omega, h0, ⟨hi, fun _ l t h ↦ Submodule.torsionBy_le_torsionBy_of_dvd _ _ ((mul_dvd_mul_right
    (pow_dvd_pow _ l.step) _).natCast.trans hN) (by simpa [-cast_mul, cast_smul_eq_nsmul,
    mul_nsmul] using (nsmul_relIndex_mem ⊥ h))⟩, ho, SetLike.ext_iff.1 (comap_map_eq_self (by
    exact fun x a z b ↦ (hΛ x).1 (ker_le_comap _ _ a) z (by simp [b]))), hΛ, Quot.ind (⟨·, hM ·,
    rfl⟩), hr _ (by omega), ⟨0⟩, fun v ↦ by simpa [sq, h₂, self_eq_neg] using
    congr((Φ v $h₁).re), fun v h ↦ by simpa [*] using congr(star ($((mk_eq_iff.1 (by
    subsingleton)).resolve_left (hΨ.2 v h)) (sqrtNegD d))), by simp [*, ← map_star_CM, neg_eq_self,
           Subtype.ext_iff, NeZero.ne]⟩, rfl, rfl, rfl, fun w ⟨k@⟨b, hb, t⟩, hw, h'⟩ ↦ ?_⟩⟩
  obtain ⟨⟨v, e, n, _⟩, -, q, H⟩ := k.exists_place_above_ne w w, k.star_ne_and_prime_norm
  refine ⟨by simpa [← eq_zero_iff_mem] using hw ∘ w.1.mem_of_dvd hN, _, b, q, by
    simpa using H (w.below _), by simpa using! hb, by simpa [*] using t.map (algebraMap _ (𝓞 E)),
    (coprime_of_no_prime_ge fun P c l o ↦ ?_).sup_eq, v, mt v.ext n, by
    simpa [← e] using! And.intro (H (w.below _)) hb⟩
  simp [o.mul_le, span_insert] at c l
  exact l.elim (hw <| w.isMaximal.eq_of_le o.1 · ▸ c) fun ⟨_, h⟩ ↦ h' ⟨P, o, (h0 <| ·.le c)⟩
    (((H _).2 (by simpa)).resolve_left (IsPrime.notMem_of_isCoprime_of_mem t hb <|
    · ▸ by simpa [ha] using! h)) c⟩) (by use {v₀ := mk σ, mk_Φ := ?_, Φ v := (ite (v.embedding.comp
    i = σ.comp i ↔ v ≠ mk σ) star id v.embedding)} <;> dsimp +instances <;> grind [mk_embedding,
    mk_eq_iff, ComplexEmbedding.conjugate_comp])
