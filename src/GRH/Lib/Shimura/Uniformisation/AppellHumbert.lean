import GRH.Lib.Shimura.AbelianScheme.ThetaFamily
import GRH.Lib.General.Geometry.SerreSaturation
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: complex uniformisation of PEL abelian varieties, Appell–Humbert and finite class
number. Here the signature is (1,n-1) at one place and definite elsewhere. The torus comes from the
exponential of a compact commutative complex Lie group, and Appell–Humbert is proved only for a very
ample class obeying the parallelogram law. Source: J. S. Milne, Introduction to Shimura Varieties
(2005/2017), Theorem 8.17 and Lemma 5.12; R. Kottwitz, Points on some Shimura varieties over finite
fields, J. AMS 5 (1992) §8; G. Shimura, On analytic families of polarized abelian varieties and
automorphic functions, Ann. Math. 78 (1963); A. Borel, Some finiteness properties of adele groups
over number fields, Publ. IHES 16 (1963); D. Mumford, Abelian Varieties §§1–2; L. Breen, Fonctions
thêta et théorème du cube, LNM 980 (1983). -/
seal Finset.univ Finset.sum Finset.prod

open CategoryTheory CartesianMonoidalCategory Complex Over LineBundle PointFn NormedAddGroup
attribute [-simp] lift_left fst_left snd_left
attribute [local simp] fieldEq DFunLike.ext_iff funext_iff exp_add norm_smul pow
attribute [local simp ←] comp_left exp_nat_mul Pic.pull_picClass

/-- Appell–Humbert theorem: if V/L ≅ A(ℂ) is a uniformisation and N a projective embedding of A
whose class is symmetric and satisfies the parallelogram law `Pic.ParallelogramLaw`, the coordinates
of N are theta functions for L of some type (B, χ) with positive Riemann form.

Known result: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class
number. -/
lemma Uniformisation.appell_humbert {A} [AddObj A] {ι V} [Finite ι] [FinComplexSpace V] (u :
  Uniformisation (O := ℂ) A V) {N} (hN :
  @IsProjEmbedding _ _ ι N A.hom) (c : N.picClass.ParallelogramLaw) : ∃ B χ θ,
  HasThetaCoords u.L (atGeneric u.expMap) N B χ θ ∧ IsPosRiemann B := by
  obtain ⟨e, L, s, hL, O⟩ := u; dsimp at O ⊢
  let X := (((N.pull (fst A A).1).mul (N.pull (snd A A).1)).pow 2).mul
    ((N.pull (fst A A + snd A A).1).mul (N.pull (fst A A - snd A A).1)).inv
  have ⟨w, (⟨o, n⟩ : X.IsFrame w)⟩ := picClass_eq_iff.1 (by simpa using! (c _ _).symm)
  choose J K using fun x : ComplexPoint A ↦ N.exists_landsIn x.1; have T {x} := hN.1.2 (K x)
  have h0 {x y} : LandsIn (lift x y).1 (X.opens (fun _ ↦ (J x, J y), J (x + y), J (x - y))) := by
    simp [X, K]
  let Φ z w := N.transition (J (e w)) (J (e z)) _ (e w).1
  have {z} : Φ z z = 1 := N.5 _ _ _ (K _)
  have Z {z} : ∀ᶠ w in _, Φ z w ≠ 0 :=
    ((O z).1 (isRegularOn_ofSection 0) (K _)).1.mono (by simp [Φ, T _])
  have hf j {z} := ((O z).1 (hN.1.1 ..).1 (K _)).2.congr (Z.mono fun _ ↦ ((T _).2 j ·.isUnit))
  choose C h using (n _ _ _ <| @h0 · ·)
  replace h {a b} : AnalyticAt ℂ (fun (x, y) ↦ C (e x) (e y) * Φ (a - b) (x - y) *
      Φ (a + b) (x + y) / (Φ a x * Φ b y) ^ 2 / C 0 0) (a, b) := .div_const ((((O _).1.comp
    analyticAt_fst).lift hN ((O _).1.comp analyticAt_snd) (o.1 _) h0).elim (·.mono (fun z
    hz ↦ by simp +zetaDelta [o.2 _ _ _ _ hz h0, eq_inv_of_mul_eq_one_left ((N.transition_trans _ _ _
    _ _ _ (K _) _).trans (N.transition_self ..)), by simpa [X] using hz, *]) |> ·.congr))
  let d : V →L[ℂ] V := (⅟2 : ℂ) • 1
  have hh z : d z + d z = z := by simp [d]; module
  have ⟨P, hP⟩ := (h.comp₂ analyticAt_id analyticAt_id).clog (x := 0) (by simp [*])
  let G : FormalMultilinearSeries .. := fun n ↦ (2 ^ n - 4 : ℝ)⁻¹ • P n
  let q := (-P 2).curryRight.curryRight 0
  choose r _ R S H using nhds_zero_basis_norm_lt.eventually_iff.1 (Z.and (hP.eventually_hasSum.and
    (Metric.eball_mem_nhds _ (hP.radius_pos.trans_le (G.radius_le_of_le fun n ↦ by simpa [G] using
    (mul_le_of_le_one_left (norm_nonneg _) (2 ^ n - 4 : ℤ).natAbs.cast_inv_le_one))))))
  have w := (@measure V (⌊‖·‖ / r⌋₊)).2
  have lt {z} (h : ¬‖z‖ < r) : ⌊‖d z‖ / r⌋₊ < ⌊‖z‖ / r⌋₊ := by
    grw [Nat.floor_lt, ← Nat.div_two_lt_floor] <;> simp_all [d, field]
  let c z := (q z z).exp * C (e z) (e z) / C 0 0
  have F := w.fix_eq fun z f ↦ if h : _ then (G.sum z).exp / Φ 0 z else f _ (lt h) ^ 4 * c (d z)
  set σ := w.fix _
  have hd z : σ (z + z) = σ z ^ 4 * c z := (F _).trans (dite_eq_iff'.2 ⟨fun h ↦ by
    have a : ‖z‖ < r := by bound [(SameRay.refl z).norm_add]
    simp [exp_log, q, eq_add_of_sub_eq (((G.hasSum (H h)).sub (((G.hasSum (H a)).mul_left 4).add
      (S a))).unique (hasSum_single 2 fun n k ↦ by
      have : (2 : ℂ) ^ n ≠ 4 := mod_cast (Nat.pow_right_injective le_rfl).ne k
      simp [← two_smul ℂ, (P _).map_smul_univ, G, *])), *]
    norm_num [G, Matrix.cons_fin_one, Matrix.vecCons_const], by simp [hh]⟩)
  choose h0 hP using @id (∀ {z}, σ z ≠ 0 ∧ AnalyticAt ℂ (σ * Φ z) z) @(w.fix fun z ih ↦
    if k : _ < r then ⟨by simp [*], ((G.analyticOnNhd _ (H k)).cexp.div (hf _) (by
    simpa [transition_self, K] using R k)).congr (.mono (tendsto_norm (gt_mem_nhds k))
    (by simp +contextual [F, Φ]))⟩ else (ih _ (lt k)).imp (by simp [F z, k]) fun a ↦
    (((a.pow 4).mul ((h.mul (q.analyticAt_bilinear _).cexp).comp₂ analyticAt_id analyticAt_id)).comp
    (d.analyticAt z)).congr (.mono (d.2.tendsto z Z) (by simp +contextual [hh · ▸ hd _, *, -F])))
  replace F := (hL · |>.1)
  let W := fun (x, y) ↦ (σ x * σ y) ^ 2 * C (e x) (e y) / σ (x - y) / σ (x + y) / C 0 0
  have hW {u} : AnalyticAt ℂ W u := by
    apply ((h.mul (((hP.comp analyticAt_fst).mul (hP.comp analyticAt_snd)).pow 2)).div ((hP.comp
      (analyticAt_fst.sub analyticAt_snd)).mul (hP.comp (analyticAt_fst.add analyticAt_snd))) _
      ).congr ((h.continuousAt.eventually_ne (y := 0) _).mono _) <;> simp +contextual [*]
  let P w := (W w)⁻¹ • fderiv ℂ W w ∘L .inr ..
  have E x {y} := hW.differentiableAt.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  have := eq_fderiv_of_double P (by fun_prop (disch := simp [*])) fun (x, y) ↦ by
    have D y := (((hasFDerivAt_inv (by simp [*])).comp y (E x)).pow 4).mul
      ((E (x + x)).comp y (1 + 1 : V →L[ℂ] V).hasFDerivAt)
    have := funext ((by simp [isAppellHumbert_iff] : @IsAppellHumbert V _ L 0 1).eq_exp_of_ne_zero
      ⟨(⟨_, D ·⟩), by simp +contextual [add_add_add_comm x x, add_sub_add_comm, exp_sub, *]⟩
      (by simp [*])).2.2 ▸ (D y).fderiv
    simp [P, *] at this ⊢; clear * - this; grind
  have ⟨B, hB, hs⟩ := exists_factor_of_automorphy (L := L) @h0 (by
    rintro ⟨l⟩ g
    use (g 0)⁻¹ • fderiv ℂ g 0 + -P (l, 0), (hh · ▸ (hasFDerivAt_comp_add_left _).1 ?_)
    set x := d _; convert! ((E x).mul ((hasFDerivAt_inv _).comp x ((E (l + x)).mul (.comp x ((((@hP
      (l + (x - x))).comp (by fun_prop)).div hP _).congr (g := g) (Z.mono _)
      ).differentiableAt.hasFDerivAt (by fun_prop))))).mul_const (g x ^ 2) using 1 <;>
      simp [g, Φ, transition_self, add_assoc, ← add_sub, (inv_smul_eq_iff₀ _).1 (this _),
      by simpa using map_add (fderiv ℂ P 0) (l, 0) (x, x), *, -hL])
  refine ⟨B, fun l ↦ σ l / σ 0 / (B l l / 2).exp, _, (fun h ↦ ⟨h, ⟨fun v ↦ not_le.1 ∘ mt fun k ↦
    ContinuousLinearMap.toSpanSingletonCLE.map_eq_zero_iff.1 (linear_ext ⟨e, L, s, hL, O, ‹_›⟩ fun
    t ↦ OverMorphism.ext
    (hN.eq_of_isHomogCoords ?_ (funext (h.2.apply_smul_of_nonpos (hf := h.3 ·) v k t) ▸ h.4 _) ((h.4
    0).smul ?_)))⟩⟩) ⟨hN.1, ⟨hs, fun l _ ↦ have := congr($(hd (l + l)) * $(hd 0) ^ 3 / $(hd l) ^ 4)
    norm_eq_one_of_pow_eq_one ?_ four_ne_zero, ?_⟩, fun i ↦ ⟨fun _ ↦ ((hP.mul (hf i)).congr (Z.mono
    (by simp +contextual))).differentiableAt, by simp +contextual [*]⟩, fun _ ↦ T.smul ?_⟩⟩
    <;> simp +contextual [← exp_add, by simpa [add_mem, *, -hd, -hL] using this, *] <;> congr! 1 <;>
    apply ext <;> simp [riemannForm, *, -ofReal_div] <;> ring
