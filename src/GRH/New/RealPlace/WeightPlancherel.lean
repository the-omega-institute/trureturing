import GRH.New.RealPlace.FloorKernels
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Tower method: pairings of kernels bounded floor by floor (see
New.RealPlace.LocalTheorem).

This file: Three weight integrals and sliced Plancherel bounds on quadrics and Heisenberg
radicals. -/

open ENNReal FI Fintype Level Matrix MeasureTheory Place ProbabilityTheory Set Size U

attribute [-simp] conjTranspose_fromRows_eq_fromCols_conjTranspose

attribute [local simp] AddChar.map_add_eq_mul IsHermUnit.conjTranspose_eq mulVec_neg
  indicator_apply_le' ascConv heisenbergElem_mulVec mul_add mul_assoc star_mulVec_dotProduct

variable {A ι} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {𝔰 : Shape} [Fintype ι] {m j} {T : 𝔰.Form A} [IsHermUnit T.splitGram] {F : Level ι T m} (Γ :
  Gauge F) {x t q : T.G} {b : Fin 𝔰.n} (a : Fin 𝔰.ϱ) {k d p}

lemma Gauge.floorMassLe_of_chart {f K} (hi : (unitriGroup (b + 1)).FixesLeft f) (h : ∀ g ∈ F.boxSet,
  ∃ Ψ, ∫⁻ v in Γ.vecsOfSize 7, Ψ v ∂F.floorQuadric b ≤ K ∧ Measurable Ψ ∧ ∀ σ ∈ GT b, f (σ * g) ≤
  Ψ (orbitPoint b σ)) (hf : Measurable f := by fun_prop) : F.FloorMassLe b K f :=
  fun g ↦ have := measurable_mul_const g measurableSet_isNear
  lintegral_indicator this _ ▸ by
    obtain n | ⟨ξ, c, k⟩ := em' (F.IsNear b g)
    simp +contextual [mt (IsNear.of_floorGroup_mul · _ le_self_add) n]
    obtain ⟨φ, l, n, h⟩ := h _ k
    grw [← l, ← (measurePreserving_orbitPoint b).setLIntegral_comp_preimage measurableSet_vecsOfSize
      n, ← lintegral_indicator_le, ← lintegral_floorMeasure_mul_right le_top
      (by simp +contextual [indicator, hi]) ⟨c, ⟨⟩⟩, lintegral_le_of_ae_imp ae_floorMeasure_mem]
    grind [orbitPoint_mem_vecsOfSize, hasMatSize_box, indicator, zero_le]

/-- In a gauge of exponent s, for a position x, a < ϱ and any g, the θ_a-integral of
vol(𝔤_{a+1}(σg, σgx))^{−s} over the σ with σg near at a+1 is at most Λ^{10⁴(ϱ+1)}. -/
lemma Gauge.floorMassLe_floorWeight_div (hx : x ∈ F.positions) :
  F.FloorMassLe a (Γ.Λ ^ (10 ^ 4 * 𝔰.n)) fun g ↦ F.floorWeight a g x / F.floorWeight
  (a + 1) g x := Γ.floorMassLe_of_chart (b := a.castSucc) (by grind [floorWeight_mul_left])
  (Γ.com · · x hx 0 |>.elim fun φ ⟨_, k, e⟩ ↦ ⟨_, (setLIntegral_orthonormalPart_le
  hasFibreBound_floorQuadric (e _)).trans (by rw [← pow_add]; bound), by fun_prop, fun σ l ↦ by
  simp [floorWeight_succ, division_def, ENNReal.mul_inv, ENNReal.mul_inv_cancel_left,
    ENNReal.inv_pow]
  grw [← (k _).1, image_subset_iff.2 fun w h ↦ ?_]
  use σ *ᵥ F.orthonormalPart *ᵥ w, by simpa +contextual [↓mem_ofPred, ↓unitriGroup_mulVec_dual
                                        (mem_unitriGroup_of_mem_floorGroup l)] using h.2
  simp [← mulVec_mulVec, ← form_mulVec_mulVec σ, orbitPoint_eq_iff.1 rfl]⟩)

/-- If δ^(b) satisfies the fibre bound `Gauge.HasFibreBound` at size 7 with constant M, then floor
b has mass at most M·vol(size 11)^{|ι|}: this bounds θ_b{σ : σg near at b+1} for all g. -/
lemma Gauge.floorMassLe_one b {M} (e : Γ.HasFibreBound b (F.floorQuadric b) 7 M) :
  F.FloorMassLe b (M * ℙ (Γ.ofSize 11) ^ card ι) 1 := Γ.floorMassLe_of_chart (by simp) fun _ _ ↦
  ⟨1, by simpa [vecsOfSize, measurable_one, ← mem_univ_pi, volume_pi_pi, -mem_pi] using
  (setLIntegral_orthonormalPart_le e le_rfl measurable_one)⟩

/-- The constant K_l = fl_l · c^{|ι|} · Λ^{4600(ϱ+1)} of floor l, where fl_l = `Level.floorModulus`
at the unit of the level and c is the Plancherel constant of the place. -/
noncomputable abbrev Gauge.floorConst l := F.floorModulus l * P.c ^ card ι * Γ.Λ ^ (4600 * 𝔰.n)

attribute [-simp] InvMemClass.coe_inv Subgroup.coe_inv in
/-- In a gauge, let j ≤ ϱ and g be near at j. The η_{<j}-integral of the weight ℘_j of the pair
(g, νy), over the ν with g⁻¹νy in `Gauge.positionsOfSize`, is at most ∏_{l<j} K_l, where K_l =
`Gauge.floorConst`. -/
lemma Gauge.lintegral_floorWeight_le (hj : j ≤ 𝔰.ϱ) g y : F.IsNear j g → ∫⁻ ν,
  Γ.positionsOfSize.indicator (F.floorWeight j g) (g⁻¹ * (ν * y))
  ∂ascConv heisenbergMeasure j ≤ ∏ l ∈ .range j, Γ.floorConst l := fun ⟨ξ, h, hg⟩ ↦ by
  obtain ⟨⟨γ, k, n, l, rfl⟩, _⟩ :=
    exists_floorGroup_mul_unipotentBelow h, Γ.measurableSet_positionsOfSize
  rw [← indicator_congr fun _ _ ↦ floorWeight_mul_left h,
    ← (ascConv_heisenbergMeasure_invariant (inv_mem l)).2, lintegral_dirac_mconv,
    lintegral_eq_of_dirac_mconv_eq (ascConv_heisenbergMeasure_dirac_comm _
    k)]; simp [-Finset.prod_mul_distrib]; grw [← Γ.one_le_c_and_ne_top.1]
  refine j.rec (by simp [floorWeight]) (fun j ih hj y ↦ le_of_not_gt fun c ↦ c.not_ge ?_) hj (γ * y)
  lift j to Fin 𝔰.ϱ using hj
  obtain ⟨τ, _, hτ, z⟩ := by simpa using exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow c.ne_bot
  obtain ⟨φ, _, k, e⟩ := Γ.com _ hg _ z.1 0
  rw [← (ascConv_heisenbergMeasure_invariant hτ).1, lintegral_mconv_dirac, ascConv,
    lintegral_mconv_symm, Finset.prod_range_succ]
  refine lintegral_heisenbergMeasure_le _ (setLIntegral_orthonormalPart_le hasFibreBound_floorVolume
    (e _)) fun t n ↦ have ⟨ν, a, b⟩ := exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow n
    ⟨⟨_, conj_mem_unipotentBelow (inv_mem (heisenbergElem_mem_floorUnipotent j t).1) (inv_mem a),
      (conj_mul_inv_close_to_one hg z (by simpa using b) (by simp) · _)⟩, ?_⟩
  grw [← ih j.2.le, ← lintegral_mul_const,
    lintegral_le_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν a ↦ ?_]
  simp [-mulVec_smul, ← indicator_mul_const]; gcongr; grw [floorWeight_succ, ← (k _).2,
    measure_mono]
  rintro _ ⟨w, ⟨hw, o⟩, rfl⟩ u hu; exists _, hw, _, hu.2
  rw [← mulVec_smul, star_mulVec_dotProduct]
  simp [-mulVec_smul, ← mulVec_mulVec, form_mulVec_mulVec, heisenbergElem_inv, ← inverse_star_unit,
    star_g, -star_mulVec_dotProduct]
  simp [dotProduct, unipotentBelow_mulVec_apply (inv_mem a) o, j.2.le.trans]; ring
  repeat fun_prop

/-- The constant Λ^{10⁶(ϱ+1)³} of a gauge. -/
noncomputable abbrev Gauge.globalConst := Γ.Λ ^ (10 ^ 6 * 𝔰.n ^ 3)

/-- Let p be a head of length j ≤ ϱ, x a position, b ≥ j, ρ an s-finite measure, Φ ≥ 0
measurable, left Q_b-invariant, zero off points near at b. Over g with w_p g near at j,
∫Φ(g)/℘_j(w_p g, w_p gx) d(η_{<j} ∗ ρ) ≤ Λ^{10⁶(ϱ+1)³} ∏_{a<j} fl_a(p_{a+1}⁻¹) ∫Φ dρ. -/
lemma Gauge.lintegral_mul_invWeight_le {b Φ ρ} [SFinite ρ] (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p) (o :
  x ∈ F.positions) (n : j ≤ b) (k : (unitriGroup b).FixesLeft Φ ∧ ∀ g, ¬F.IsNear b g → Φ g = 0) (l :
  Measurable Φ) : ∫⁻ g, Φ g * F.invWeight j x (weylElem j p * g) ∂ascConv heisenbergMeasure j ∗ₘ ρ ≤
  (∏ a ∈ .range j, F.floorModulus a (p a)⁻¹) * Γ.globalConst * ∫⁻ g, Φ g ∂ρ := by
  rw [lintegral_mconv_symm, mul_comm, ← lintegral_mul_const]; gcongr
  rw [lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν
    e ↦ by rw [k.1 ν (unipotentBelow_le_unitriGroup e)], lintegral_const_mul]
  obtain z | ⟨_, hξ, hg⟩ := em' (F.IsNear b y); simp_all
  obtain ⟨γ, k, u, l, rfl⟩ := exists_floorGroup_mul_unipotentBelow (unitriGroup_anti n hξ); gcongr
  grw [← (ascConv_heisenbergMeasure_invariant l).1, lintegral_mconv_dirac,
    lintegral_eq_of_dirac_mconv_eq (ascConv_heisenbergMeasure_dirac_comm _ k), globalConst,
    pow_three, ← Nat.mul_le_mul_left _ hj.step]
  simp [weylElem_mul_left_comm, k, pow_mul]
  refine j.rec (by simp [invWeight, floorWeight]) (fun a ih hj hp ↦ ?_) hj hp
  lift a to Fin 𝔰.ϱ using hj
  grw [ascConv_heisenbergMeasure_succ, lintegral_mconv_symm, Finset.prod_range_succ, pow_succ,
    mul_mul_mul_comm, ← ih _ (hp · ·.step), ← lintegral_mul_const,
    lintegral_le_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν l ↦ ?_]
  refine (Γ.com _ hg x o (ν.1.1 * F.orthonormalPart).toRows₁).elim fun φ ⟨_, h, e⟩ ↦
    lintegral_heisenbergMeasure_le (-star p a)⁻¹
    (setLIntegral_orthonormalPart_le hasFibreBound_floorVolume (e _)) fun t n ↦ ⟨⟨_, inv_mem l,
    (head_entries_mem_ofSize Γ.hasMatSize_box a.2 (by simpa [IsNear, invWeight] using
    n) ⟨inv_mem (mul_mem (unipotentBelow_le_unitriGroup (heisenbergElem_mem_floorUnipotent a t).2)
    (unipotentBelow_le_unitriGroup l)), by simpa using hg⟩ hp.star_head .refl).elim fun L k
    i ↦ by simpa [Γ.neg_star_mem_ofSize] using
    Γ.mul_mem_ofSize L (sub_mem_ofSize (k.2 i) (HasMatSize.one ..))⟩, ?_⟩
  grw [invWeight, indicator_le_self .., floorWeight_succ, ENNReal.mul_inv, ENNReal.inv_pow, ← (h
    _).1, ← show invWeight .. = (floorWeight ..)⁻¹ from ite_eq_left
      ((mem_of_indicator_ne_zero n).imp (by grind))]; gcongr
  simp [weylElem_succ, weylElem_mul_left_comm,
    Subgroup.mem_inf.1 (heisenbergElem_mem_floorUnipotent ..)]
  rintro _ ⟨u, ⟨k, c⟩, rfl⟩
  use (weylElem a.succ p * (P.heisenbergElem a t * ν)).1.1 *ᵥ F.orthonormalPart *ᵥ u,
    ⟨by simpa using c, ?_⟩ <;> simp [-mulVec_add, ← mulVec_mulVec, -fromRows_mulVec, funext (g :=
    F.orthonormalPart *ᵥ u) (Sum.rec (by simpa [↓mulVec_mulVec] using! (congrFun k)) fun i ↦
    unipotentBelow_mulVec_apply l (by simp) _ (by
      revert i; simp [level]; lia))] <;> simp [mulVec_apply_eq_sum, weylElem, weylOn, level]; lia
  repeat first | fun_prop | simp

/-- Let t ∈ H_b, q ∈ t𝒩_{<b}, qx of size j, f(σ) = k_{b+1}(σx, σy), k a kernel
(`Level.IsPairingKernel`). Then tσ⁻¹f_{b+1} has size j+6 a.e. where f ≠ 0, and G(v) = ∫ψ(ξh(v+y',
tσ⁻¹f_{b+1}))f dθ_b has ∫_{size i}|G|² ≤ MΛ^{99(ϱ+1)(j+12)}(c/md ξ)^{|ι|}‖f‖² for
`Gauge.HasFibreBound` measures. -/
lemma Gauge.amplitude_support_and_plancherel (ht : t ∈ GT b) (h : Γ.HasMatSize j (q * x).1.1) (hk :
  F.IsPairingKernel b k d) y (hq : t⁻¹ * q ∈ unipotentBelow b
  := by simp) : let f σ := F.upperPairing (b + 1) k (σ * x) (σ * y); (∀ᵐ σ ∂F.floorMeasure b,
    f σ ≠ 0 → t.1.1 *ᵥ orbitPoint b σ ∈ Γ.vecsOfSize (j + 6)) ∧ ∀ (ξ : Aˣ) y {q i M},
    Γ.HasFibreBound b q i M → ∫⁻ v in Γ.vecsOfSize i, ‖∫ σ, ψ (ξ * star (v + y) ⬝ᵥ T.splitGram *ᵥ
    t *ᵥ orbitPoint b σ) * f σ ∂F.floorMeasure b‖ₑ ^ 2 ∂q ≤ M * (Γ.Λ ^ (99 * 𝔰.n * (j + 12)) *
    ((P.c / P.md ξ) ^ card ι * ∫⁻ σ, ‖f σ‖ₑ ^ 2 ∂F.floorMeasure b)) := by
  intro f
  refine (fun s ↦ ⟨s, fun ξ y _ _ _ k ↦ ?_⟩) (ae_floorMeasure_mem.mono fun σ l k ↦ by
    simpa [orbitPoint, -mulVec_single] using orbitPoint_mem_vecsOfSize (mul_mem l (inv_mem ht)) h
      (by simpa using (isNear_mul_iff (unipotentBelow_le_unitriGroup
      (conj_mem_unipotentBelow l hq))).2 (hk.isNear_of_upperPairing_ne_zero k)))
  obtain ⟨⟨Z, _, ζ, _, K, μ, _, ⟨_, rfl⟩, o, c, _, hμ, l⟩, A, _, e⟩ := Γ.hasFibreBound_floorQuadric,
    exists_factor_orbitPoint b (Φ :=
    f) (by fun_prop) (by simp +contextual [f, hk.upperPairing_invariant])
  let r v := (v, (Γ.vecsOfSize (j + 6)).indicator (A <| t⁻¹.1.1 *ᵥ ·) v)
  have : Measurable r := by fun_prop (disch := apply measurableSet_vecsOfSize)
  have H := (IdentDistrib.of_ae_eq (f := fun σ ↦ (t *ᵥ orbitPoint b σ, f σ)) (by fun_prop) (s.mp
    (ae_floorMeasure_mem.mono (by simp +contextual [r, indicator, not_imp_comm, *])))).trans
    (((measurePreserving_mulVec_orbitPoint b ht).hasLaw.identDistrib (.comp {map_eq := o} {map_eq :=
    rfl})).comp this)
  let g v (z : _ × _) := ψ (ξ * star (F.floorBasis b *ᵥ v + y) ⬝ᵥ T.splitGram *ᵥ z.1) * z.2
  have J v := H.comp (u := g v) (by fun_prop)
  have i v := (J v).integrable_snd
    (hk.upperPairing_eq_integral_succ.1.bdd_mul (c := 1) (by fun_prop) (by simp))
  let N (p x : _ × _) := ‖∫ w, P.ψ (ξ * star x.2 ⬝ᵥ w) * ∫ z, (g (![0, p.1] ⊕ᵥ (p.2 ⊕ᵥ 0)) ∘ r ∘
    (F.floorBasis b *ᵥ ·) ∘ K) ((x.1, w), z) ∂ζ‖ₑ
  refine setLIntegral_le_of_hasFibreBound k (G := fun p w ↦ (∫⁻ x, N p (x, w)) ^ 2) (fun p ↦
    ⟨by fun_prop, ?_⟩) fun v _ ↦ ?_
  · erw [funext fun _ ↦ (sq _).trans (lintegral_prod_mul ..).symm,
      (H.comp (u := (‖·.2‖ₑ ^ 2)) _).lintegral_eq, lintegral_prod, lintegral_lintegral_swap]
    apply (lintegral_mono fun _ ↦ lintegral_mul_le_Lp_mul_Lq _ .two_two ?_ ?_).trans
    grw [lintegral_prod, lintegral_prod, ← l, ← lintegral_const_mul, ← sq_lintegral_le _ _ fun _ ↦
      (rpow_inv_natCast_pow ..).le]; simp
    grw [lintegral_lintegral_mul, sq,
      lintegral_le_of_ae_imp (i _).integral_prod_left.prod_right_ae]; intro x i
    grw [plancherel_inequality ξ i, mul_left_comm, ← lintegral_const_mul (μ x)]; gcongr
    grw [← hμ x w, ← setLIntegral_le_lintegral, ← setLIntegral_one, ← sq_lintegral_le,
      setLIntegral_eq_of_support_subset, enorm_integral_le_lintegral_enorm]
    repeat first | fun_prop | simp +contextual [g, r, ← ofReal_norm,
      mem_vecsOfSize_of_floorBasis_mulVec]
  erw [(J _).integral_eq, integral_prod _ (i _), integral_prod _ (i _).integral_prod_left]
  grw [enorm_integral_le_lintegral_enorm]; gcongr
  rw [enorm_le_iff_norm_le, ← ge_iff_le, ← one_mul ‖_‖,
    ← norm_psi (ξ * star v ⬝ᵥ (![a.1, 0] ⊕ᵥ (0 ⊕ᵥ (0 ⊕ᵥ a.2)))), ← norm_mul]
  simp [← integral_const_mul]; congr! 5; generalize e : K _ = k; cases e ▸ c _
  simp [g, r, F.gram_floorBasis]
  simp [fromBlocks_mulVec, dotProduct]; grobner

/-- Plancherel on 𝒩_a. For a kernel k twisted by d with (fw(dsd⁻¹) − fw(s^ε))/g = ξ·fw(s) on
𝒩_a (fw = `simpleRootSum`), let Φ(n) ≤ C|k_{a+1}(n^ε x, ny)|² vanish off a set S centred
as in the hypothesis `h`. Then ∫Φ dη_a ≤
C(c/md(ξu))^{|ι|} fl_a(u) Λ^{100(ϱ+1)(i+j+31)} ∫|k_{a+2}(σx, σy)|² dθ_{a+1}. -/
lemma Gauge.parseval_heisenbergMeasure_of_box {S : Set _} {i} {Φ : _ → _} (ξ u : Aˣ) (ε : ℕ) C (hk :
  F.IsPairingKernel (a + 1) k d) x y (e : ∀ s ∈ floorUnipotent a, F.g⁻¹.1 * (simpleRootSum (d * s *
  d⁻¹) - simpleRootSum (s ^ ε)) = ξ * simpleRootSum s) (o : ∀ n ∈ floorUnipotent a, Φ n ≠ 0 → n ∈
  S ∧ Φ n ≤ C * ‖F.upperPairing (a + 1) k (n ^ ε * x) (n * y)‖ₑ ^ 2) (h : ∀ m ∈ S, ∃ t ∈ unitriGroup
  (a + 1) ⊓ GT a, ∃ q ∈ unipotentBelow (a + 1), Γ.HasMatSize i (t * q * x).1.1 ∧ ∀ n ∈ S, ∃ ν ∈
  unipotentBelow a, u⁻¹.1 • (((ν * (t * m * (t * n)⁻¹)).1.1 - 1) · (eStar a)) ∈ Γ.vecsOfSize j) : ∫⁻
  n, Φ n ∂heisenbergMeasure a ≤ C * ((P.c / P.md (ξ * u)) ^ card ι * F.floorModulus a u * Γ.Λ ^ (100
  * 𝔰.n * (i + j + 31)) * ∫⁻ σ, ‖F.upperPairing (a + 1 + 1) k (σ * x) (σ * y)‖ₑ ^ 2 ∂F.floorMeasure
  (a + 1)) := le_of_not_gt fun H ↦ H.not_ge <| (exists_ne_zero_of_ae ae_mem_floorUnipotent
  H.ne_bot).rec fun n ⟨hn, k⟩ ↦ (h n (by grind)).elim fun _ ⟨s, q, hq, h, hc⟩ ↦ by
  obtain ⟨t, ht, r, hr, rfl⟩ := exists_floorGroup_mul_floorUnipotent s
  obtain ⟨⟨_, rfl⟩, z, rfl⟩ := exists_eq_heisenbergElem_of_mem hr,
    exists_eq_heisenbergElem_of_mem hn
  rw [lintegral_eq_of_dirac_mconv_eq ((heisenbergMeasure_mconv_dirac hr).2.trans
    (heisenbergMeasure_mconv_dirac (mul_mem hr hn)).1.symm),
    lintegral_eq_of_dirac_mconv_eq (dirac_mconv_heisenbergMeasure_comm ht)]
  refine lintegral_heisenbergMeasure_le u ((Γ.amplitude_support_and_plancherel (b := a.succ) ht h hk
    y (by simpa using mul_mem hr.2 hq)).2 (-ξ * star u) (u⁻¹.1 • t.1.1 *ᵥ inclMatrix A (↑) *ᵥ z.1)
    hasFibreBound_floorVolume) fun v k ↦ (o _ ?N k).imp (by simpa using hc _ ·) (le_trans' ?_)
  any_goals rw [a.val_succ, hk.upperPairing_eq_integral_succ.2,
    integral_congr_ae (ae_floorMeasure_mem.mono fun σ l ↦ have c := conj_mem_floorUnipotent ?N σ l
    .trans (by simp [↓conj_pow]) ((hk.law (pow_mem c.2 ε) c.2 (σ * x) (σ * y)).trans ?_))]
  all_goals simp only [↓e _ ‹_›, mul_heisenbergElem (inv_mem ht), inv_mul_cancel_right,
    heisenbergElem_inv, ← add_assoc, heisenbergElem_mul, heisenbergElem_mem_floorUnipotent,
    simpleRootSum_conj_heisenbergElem, ← form_mulVec_mulVec t _ (orbitPoint _ _), mulVec_add,
    inclMatrix_mulVec_floor_block a.2, inv_mem, *]
  simp [← inverse_star_unit]; ring
