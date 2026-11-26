import OmegaMath.NumberTheory.GRH.Lib.PadicHodge.TateSen.DeRhamFiltration
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius (known
result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).

This file: Hodge–Tate maps of distinct weights are independent; jumps read from a basis of them.
Breuil–Kisin ring W[[z]] inside A_inf: definition, Frobenius, coordinates, Weierstrass division.
Hodge frame: invariant B_dR basis adapted to filtration, giving de Rham implies Hodge–Tate. -/

noncomputable section

section

open Filter Module Submodule LinearMap Fintype Finset Set RingHomClass FaithfulSMul Fint
variable {p} [ThePrime p] {Γ R T ι} [Group Γ] [CommRing R] [AddCommGroup T] [Module
  R T] [Algebra ℤ_[p] R] [OverGp Γ p] {ρ : Representation R Γ T} {γ : R →ₐ[ℤ_[p]] ℂ_[p]}
  [A : Algebra.IsAlgebraic ℤ_[p] R]

/-- For an R-basis b of T indexed by ι, the C_p-linear isomorphism from γ-semilinear maps f: T →
C_p to C_p^ι sending f to its values f(b_i). -/
def evalOnBasis (b : Basis ι R T) : (T →ₛₗ[toRingHom γ] ℂ_[p]) ≃ₗ[ℂ_[p]] ι → ℂ_[p] :=
  .ofBijective (pi (id.flip <| b ·)) ⟨fun _ _ ↦ b.ext ∘ congrFun, let := γ.toAlgebra
  fun c ↦ ⟨⟨_, (b.constr ℕ c).2⟩, funext (b.constr_basis ℕ c)⟩⟩

instance : Algebra.IsAlgebraic ℤ_[p] (PadicAlgCl p) :=
  IsFractionRing.comap_isAlgebraic_iff.2 (PadicAlgCl.isAlgebraic _)

variable (γ) in lemma exists_algHom_lift : ∃ δ : R →ₐ[ℤ_[p]] PadicAlgCl p, ∀ r, γ r = δ r :=
  ((AlgEquiv.arrowCongr .refl (.ofInjectiveField (Algebra.algHom _ (PadicAlgCl p) _))).surjective
  (γ.codRestrict _ fun r ↦ IsAIC.mem_range_of_isIntegralElem (((A.1 r).algHom γ).extendScalars
  (algebraMap_injective ..)).isIntegral)).imp fun _ h _ ↦ congr(($h _).1).symm

/-- Let R be algebraic over Z_p and let the s_i span T over R. If a γ-semilinear f: T → C_p
satisfies f(g s_i) = χ(g)^(−u)·g f(s_i) for g near 1, for each i, then f lies in
`hodgeTateMaps` for u. -/
lemma mem_hodgeTateMaps_of_span {s : ι → T} (hs : span R (range s) = ⊤) {f u} (h : ∀ i, ∀ᶠ g in
    nearOne Γ, f (ρ g (s i)) = (χ g ^ (-u)).1 • toGp g • f (s i)) : f ∈ hodgeTateMaps ρ γ u :=
  (exists_algHom_lift
  γ).rec fun δ _ x ↦ by refine span_induction ?_ ?_ (fun _ _ _ _ ↦ (·.mp <| ·.mp ?_)) (fun r _ _ ↦
  (·.mp ((eventually_nearOne_apply_eq Γ (δ r)).mp ?_))) (hs.ge ⟨⟩ : x ∈ _) <;> simp_all

omit A
variable [F : Module.Finite R T]

instance : Module.Finite ℂ_[p] (T →ₛₗ[toRingHom γ] ℂ_[p]) := let ⟨_, x, h⟩ := F.exists_fin
  .of_injective (pi (id.flip <| x ·)) fun _ _ ↦ ext_on_range h ∘ congrFun

lemma hodgeTateMaps.mem_span_same_weight {k : ι → ℤ} {f} (hf : ∀ i,
  f i ∈ hodgeTateMaps ρ γ (k i)) {u φ} (hφ : φ ∈ hodgeTateMaps ρ γ u) (h
  : φ ∈ span ℂ_[p] (range f)) : φ ∈ span (PadicAlgCl p) (f '' {i | k i = u}) := by
  obtain ⟨⟨_, x, hx⟩, _, a, _, e, hi⟩ := F.exists_fin, exists_linearIndependent' ℂ_[p] f
  have := hi.finite; obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun _).1 (e.ge h)
  have H : ∀ i, ∀ᶠ g in _, (cyclotomicGp g ^ (-u + k (a i))).1 • g • c i = _ := eventually_all.1
   (nhds_one_le_map_nearOne Γ ((Eventually.all fun l ↦ (hφ (x l)).and (.all (a · |> hf
   <| x l))).mono fun g H ↦ linearIndependent_iffₛ.1 hi _ _ ((cancel_right (ρ.apply_bijective
   g).2).1 (ext_on_range hx (by simpa [H, smul_sum, smul_smul, zpow_add] using (H · |>.1.symm))))))
  exact sum_mem fun i _ ↦ if e : u = k (a i) then (exists_algebraic_of_fixed_near_one
   (by simpa [e] using H i)).rec (by aesop (add simp PadicComplex.coe_eq))
   else by simp [tate_eq_zero_of_chi_twist (neg_add_eq_zero.1.mt e) (by simpa using H i)]

instance finite_hodgeTateMaps u : Module.Finite (PadicAlgCl p) (hodgeTateMaps ρ γ u) :=
  (exists_fun_fin_finrank_span_eq ..).elim fun _ ⟨h, e, _⟩ ↦ .of_fg ((fg_span (toFinite _)).of_le
  fun _ m ↦ hodgeTateMaps.mem_span_same_weight h m (e.ge (subset_span m)))

lemma hasJumps_of_basis [Fintype ι] {u} {b : Basis ι ℂ_[p] _} (h : ∀ i, b i ∈ hodgeTateMaps ρ γ
  (u i)) : HasJumps ρ γ (univ.1.map u) := fun v ↦ by erw [jump, ← span_eq_of_le _
  (by grind [SetLike.mem_coe]) fun _ ↦ (hodgeTateMaps.mem_span_same_weight h · (by simp)),
  image_eq_range, univ.1.count_map, finrank_span_eq_card
  ((b.linearIndependent.restrict_scalars' _).comp _ (by simp))]; simp [eq_comm, card_def]

end

attribute [-simp] IsUnit.dvd Algebra.mul_smul_comm Algebra.smul_mul_assoc

namespace Lift

open Ainf Set Ideal Fact NeZero IsLocalRing PowerSeries Witt WittVector WithIdeal
variable {p} [ThePrime p] (f : ℕ+)

attribute [local simp] image_pair Ideal.map_pow mem_span_singleton mul_sub
  PadicInt.maximalIdeal_eq_span_p IsUnit.map Ainf.isUnit_iff_isUnit_constantCoeff ne

/-- The subring of O^♭ of the x with x^{p^f} = x, a field with p^f elements. -/
def flatFq := (iterateFrobenius OFlat p f).eqLocus (.id _)

/-- The field of elements x of O^♭ with x^{p^f} = x has exactly p^f elements. -/
@[simp] lemma card_flatFq : .card (flatFq f) = p ^ f.val := open Polynomial in
  have h := (isMonicOfDegree_X_pow ..).sub (by simp [elim])
  (Nat.subtype_card ⟨_, nodup_roots (galois_poly_separable p _ (by simp))⟩
    (by aesop (add simp h.ne_zero))).trans (((IsAlgClosed.splits _).of_splits_map_of_injective
    (IsFractionRing.injective _ CFlat) fun _ _ ↦ OFlat.isAIC.mem_range_of_isIntegralElem ⟨_,
    h.2, by aesop⟩).natDegree_eq_card_roots.symm.trans h.1)

instance : Finite (flatFq f) := Nat.finite_of_card_ne_zero (by simp)

instance : Field (flatFq f) := (Finite.isField_of_domain _).toField

/-- The ring Λ = W(k) of p-typical Witt vectors over the field k of elements x of O^♭ with
x^{p^f} = x. -/
@[reducible] def WittFq := WittVector p (flatFq f) deriving CommRing

instance : Algebra (WittFq f) Ainf := inferInstance

deriving instance Algebra (WittFq f) for @WittCFlat p _

/-- A chart: a Λ-algebra map Λ[[X]] → A_inf, Λ = W(F_{p^f}), sending X to a non-unit Teichmüller
lift z = [u] and a series X^e A + p, A a unit, to ξ times a unit. -/
structure Chart where
  (f) (seriesMap : (WittFq f)⟦X⟧ →ₐ[WittFq f] Ainf) (unitSeries) not_isUnit_z :
    ¬IsUnit (seriesMap X)
  (varpiFlat e) associated_xi : Associated (seriesMap (X ^ e * Units.val unitSeries + p.cast)) xi
  seriesMap_X : seriesMap X = teichmuller p varpiFlat

variable {f} (c : Chart) {Γ : Type} [Group Γ] {g : Gp p}

lemma exists_algHom_X_eq Λ {R} [CommRing Λ] [CommRing R] [Algebra Λ R] {I} [h : IsAdicComplete I R]
    {z} (hz : z ∈ I) : ∃ e : Λ⟦X⟧ →ₐ[Λ] R, e X = z := let := mk I
  let : UniformSpace Λ := ⊥
  by obtain ⟨⟨⟩⟩ := (IsAdic.isAdicComplete_iff (by rfl)).1 h, DiscreteTopology.instContinuousSMul
     use aeval (isTopologicallyNilpotent_of_mem hz), by simp [coe_aeval]

lemma exists_chart_of_pow_mul_eq_neg f {x : OC} {e} (v : OCˣ) (h : x ^ e * v = -p) : ∃ ev :
  (WittFq f)⟦X⟧ →ₐ[WittFq f] _, theta (ev X) = x ∧ ∀ A : _ˣ, theta (ev A.1) = v → ∃ c : Chart, c.f =
  f ∧ c.seriesMap ≍ ev ∧ c.varpiFlat.untilt = x ∧ c.e = e ∧ c.unitSeries ≍ A :=
  (untilt_surjective_of_isAIC x).rec fun (u : OFlat) _ ↦ by
  refine (exists_algHom_X_eq _ (h := isAdicComplete_span_singleton ?_) (by bound)).imp fun _ hu ↦
    ⟨?_, fun A _ ↦ ⟨⟨_, _, A, ?_, u, e, associated_of_dvd_dvd ((theta_eq_zero_iff_dvd_of_untilt_dvd
    ?h ?_).1 ?_) (theta_eq_zero_iff_xi_dvd.1 ?h), hu⟩, ?_⟩⟩ <;>
    simp (maxDischargeDepth := 4) [*, -constantCoeff_apply, p_dvd_iff.1, @out ¬IsUnit _,
    mt ((IsUnit.mul · v.isUnit) ∘ .pow e ∘ .map theta)]; use -v, by aesop

instance : Module.Finite ℤ_[p] (WittFq f) := .of_surjective (Finsupp.lift _ _ _ (teichmuller
  p)) (@surjective_of_mkQ_comp_surjective _ _ (maximalIdeal _) _ _ _ _ _ _ _
  (by simp [(isAdicComplete_over_base
  _).1]) _ (Quot.ind (⟨fun₀ | ·.1 0 => 1, SModEq.sub_mem.2 (by simp [p_dvd_iff, map_sub])⟩)))

lemma WittFq.exists_smul_algebraMap_eq (m : FrobGal) c : ∃ b, m • algebraMap (WittFq f) Ainf c =
  algebraMap (WittFq f) _ b :=
  ⟨⟨(⟨_, (smul_pow' m ..).symm.trans <| congrArg _ <| c.1 · |>.2⟩)⟩, rfl⟩

lemma wittFq_map_residue_injective : (map ((residue _).comp (flatFq f).subtype) : WittFq f →
  _).Injective := map_injective _ (RingHom.injective _)

/-- The element g of G_p fixes the image of Λ = W(F_{p^𝔣}) in A_inf pointwise. -/
abbrev FixesLambda f (g : Gp p) := ∀ a, g • algebraMap (WittFq f) Ainf a = algebraMap _ _ a

namespace Chart

/-- For a chart, the Λ-subalgebra S of A_inf that is the image of the chart's map Λ[[X]] →
A_inf. -/
def S := c.seriesMap.range

/-- For a chart, the image z of the variable X, as an element of S. -/
def z : c.S := ⟨c.seriesMap X, _, rfl⟩

/-- For a chart, the ideal (p, z) of S, which is its maximal ideal. -/
abbrev maxIdeal := span {↑p, c.z}

/-- The element g of G_p fixes the image of Λ in A_inf pointwise and fixes θ(z), z the
coordinate of the chart c. -/
abbrev FixesThetaZ g := FixesLambda c.f g ∧ g • theta c.z = theta c.z

/-- The chart is a chart of the field fixed by j(Γ): every g in G_p fixing Λ and θ(z) lies
in the image of j. -/
def IsChartOf (j : Γ →* Gp p) := ∀ g, c.FixesThetaZ g → g ∈ j.range

lemma z_eq_teichmuller : c.z = teichmuller p c.varpiFlat := c.8

instance : NeZero c.e := ⟨(prime_xi.2.1 <| c.7.isUnit <| by
  simp [·, p_dvd_iff.1, -constantCoeff_apply])⟩

/-- For a chart, ξ lies in the ideal of A_inf generated by p and z. -/
lemma xi_mem_span_p_z : ∃ b, ↑c.z ∣ xi - p * b := c.7.rec (⟨·, by simp [← ·, add_mul, z]⟩)

lemma not_p_dvd_z : ¬↑p ∣ c.z.1 :=
  (·.trans c.xi_mem_span_p_z.choose_spec).mt (by simp [dvd_sub_left])

/-- For a chart, the Λ-algebra isomorphism from Λ[[X]] onto S given by the chart's map, which is
injective. -/
def seriesEquiv : (WittFq c.f)⟦X⟧ ≃ₐ[WittFq c.f] c.S := .ofInjective _ (.of_ker _
  fun f h ↦ constantCoeff_divXPowOrder_eq_zero_iff.1 (wittFq_map_residue_injective (by
  obtain _ := c.4, c.not_p_dvd_z, f.X_pow_order_mul_divXPowOrder ▸ h,
    congr(toWittResidue (c.seriesMap $f.divXPowOrder.eq_X_mul_shift_add_const))
  aesop (add simp [seriesMap_X, toWittResidue, z, C_eq_algebraMap, ((residue_eq_zero_iff _).2)]))))

/-- For a chart, the image E in S of the series X^e A + p; it equals ξ times a unit of A_inf. -/
@[irreducible, local simp] def E := c.z ^ c.e * c.seriesEquiv c.unitSeries + p

lemma associated_E_xi : Associated ↑c.E xi := by simpa using! c.7

lemma theta_E : theta c.E = 0 := theta_eq_zero_iff_xi_dvd.2 c.associated_E_xi.dvd'

lemma z_dvd_E_sub_p : c.z ∣ c.E - p := by simp

@[simp] lemma seriesEquiv_symm_z : c.seriesEquiv.symm c.z = X := c.seriesEquiv.left_inv X

lemma z_pow_mem_span : c.z ^ c.e ∈ span {c.E, ↑p} := by simp [span_insert (_ * _), mem_sup_left]

lemma exists_z_dvd_sub_const s : ∃ a t, s = algebraMap (WittFq c.f) _ a + c.z * t := by
  simp [← sub_eq_iff_eq_add', ← dvd_def, ← map_dvd_iff c.seriesEquiv.symm, X_dvd_iff]

instance : c.maxIdeal.IsMaximal := by
  simpa [eq_span_insert_X_of_X_mem_of_span_eq X_prime.2.1 ((map_maximalIdeal_of_surjective _
    (@constantCoeff_surj (WittFq c.f) _)).trans (irreducible p).maximalIdeal_eq).symm, pair_comm X]
    using! (maximalIdeal _).map_isMaximal_of_equiv c.seriesEquiv

instance : IsAdicComplete c.maxIdeal c.S := by
  simpa [isAdicComplete_iff, @IsHausdorff.of_isDomain _ _ c.maxIdeal (isNoetherianRing_range _),
    IsPrime.ne_top] using! (IsPrecomplete.congr_ringEquiv (span {↑p, X})
    c.seriesEquiv.toRingEquiv).2 (isPrecomplete_of_shiftDiff_surjective (fun b ↦ ((@out
    (shiftDiff _ (p : WittFq c.f)).Surjective).comp_left (coeff · <| b ·)).imp' (.mk ∘ flip ·) (by
    simp_all [funext_iff, PowerSeries.ext_iff, shiftDiff, flip, ← nsmul_eq_mul])) out)

lemma exists_maxIdeal_pow_le n : ∃ N, c.maxIdeal ^ N • ⊤ ≤ (span {↑p, xi} ^ n).restrictScalars
  c.S := ⟨_, by simpa [← pow_mul] using!
  pow_right_mono (exists_pow_le_of_le_radical_of_fg (span_le.2 (pair_subset ⟨1, by aesop⟩
  (mem_radical_of_not_isUnit c.4 (by simp)))) ⟨{_, _}, by aesop⟩).choose_spec n⟩

instance : IsHausdorff c.maxIdeal Ainf :=
  ⟨by simpa using! (isAdicComplete_span_pair prime_p.2.1 c.4).1.1⟩

/-- For a chart, A_inf has a topological basis over S, for the maximal ideal 𝔪 of S, one of
whose coordinates λ_i: A_inf → S is the identity on S. -/
lemma exists_adicBasis_coord_eq_self : ∃ d : AdicBasis c.maxIdeal Ainf, ∃ i, ∀ s : c.S,
  d.coord i s = s := (exists_adicBasis rfl
  (prime_p.2.2 _ · ⟨·, ·⟩ |>.resolve_left c.not_p_dvd_z) _ (let := Quotient.field c.maxIdeal
  by simpa [mem_span_pair_iff, ← isUnit_iff_dvd_one] using! c.4)).imp fun d h ↦
  (h (mem_singleton 1)).imp fun i e s ↦ by simpa [e, c.S.smul_def] using d.5 i (.single i s)

/-- For a chart, a chosen (p, z)-adic topological basis (b_i) of A_inf over S with its S-linear
coordinates λ_i. -/
def adicBasis := c.exists_adicBasis_coord_eq_self.choose

/-- For a chart, a chosen index i₀ of the chosen topological basis of A_inf over S whose
coordinate function A_inf → S is the identity on S. -/
def oneIndex := c.exists_adicBasis_coord_eq_self.choose_spec.choose

/-- The chosen coordinate λ₀ of A_inf over S: an S-linear map A_inf → S that is the identity on
S. -/
abbrev coord₀ := c.adicBasis.coord c.oneIndex

lemma coord₀_coe : ∀ s, c.coord₀ s.1 = s := c.exists_adicBasis_coord_eq_self.choose_spec.choose_spec

lemma dvd_iff_coe_dvd {a b : c.S} : a ∣ b ↔ a.1 ∣ b :=
  ⟨map_dvd c.S.val, (c.coord₀_coe b ▸ ·.choose_spec ▸ ⟨_, map_smul _ a _⟩)⟩

/-- For a chart, the ring endomorphism of S obtained by restricting the Frobenius φ of A_inf. -/
def φ : c.S →+* c.S :=
  (frobEnd.comp c.S.val.1).codRestrict _ (let F := c.seriesMap.comp (expand p out)
  have := isAdicComplete_span_singleton (a := F X) (by simp [F, c.4])
  (⟨_, mem_range_of_approx F.toAddMonoidHom (F.toSemilinearMap.2 X) _ (c.exists_z_dvd_sub_const ·
  |>.rec fun a ⟨t, e⟩ ↦ (a.exists_smul_algebraMap_eq _).imp' C fun _ _ ↦ ⟨t, by
  simpa [F, e, C_eq_algebraMap, z, seriesMap_X]⟩) · |>.choose_spec⟩))

/-- The element φ^n(E) of S, the image of E under the n-th power of the Frobenius φ of S. -/
def frobE n := (c.φ ^ n) c.E

lemma coe_φ_pow n : ∀ r, ((c.φ ^ n) r).1 = frobEnd^[n] ↑r := by induction n <;> aesop

/-- If g in G_p fixes Λ = W(F_{p^𝔣}) pointwise and d in A_inf divides gz − z, then d divides gs
− s for every s in the ring S of the chart. -/
lemma dvd_smul_sub_of_fixesLambda {d} (h : d ∣ g • c.z.1 - c.z) (k : FixesLambda c.f g) (s : c.S) :
  d ∣ g • s - s := have := isAdicComplete_span_singleton c.4
  (mem_range_of_approx (.mulLeft d) (mul_smul_comm (c.seriesMap X) _) (g • (↑) - (↑))
  (c.exists_z_dvd_sub_const · |>.rec fun a ⟨t, e⟩ ↦ (h.mul_right (g • t)).imp fun _ ↦ (⟨t, by
  simp [*, ← ·, sub_mul, z]⟩)) s).rec Dvd.intro

/-- If g in G_p fixes the image of Λ in A_inf pointwise and fixes θ(z), then g fixes θ(s) for
every s in S. -/
lemma smul_theta_of_fixesThetaZ (h : c.FixesThetaZ g) (s : c.S) : g • theta s = theta s := by
  simpa [← theta_eq_zero_iff_xi_dvd, h] using (c.dvd_smul_sub_of_fixesLambda (d := xi) · h.1 s)

open Polynomial hiding C X

/-- Weierstrass division by φ^n E: for s in S and N = p^n e there is a unique polynomial r over
Λ of degree < N with φ^n E dividing s − r(z) in S. -/
lemma weierstrass_division n {N} (e : p ^ n * c.e = N) s : ∃! r : (WittFq c.f)[X]_N,
  c.frobE n ∣ s - r.1.aeval c.z := by
  obtain ⟨h, rfl⟩ : let g := (c.seriesEquiv.symm (c.frobE n)).map (residue _)
    g ≠ 0 ∧ g.order.toNat = N := by simp [frobE, order_mul, ← pow_mul, -RingHom.coe_pow, e, by
    simpa using congrArg C ((residue_eq_zero_iff (p : WittFq c.f)).2 (irreducible p).1),
    IsUnit.ne_zero, ((c.φ ^ n) c.z).ext (a2 :=
    c.z ^ p ^ n) (by simp [↓coe_φ_pow, z_eq_teichmuller]), order_zero_of_isUnit]
  simpa [← map_dvd_iff c.seriesEquiv.symm, ← aeval_algHom_apply, dvd_def, sub_eq_iff_eq_add,
    aeval_def X, eval₂_C_X_eq_coe, ExistsUnique, mem_degreeLT] using (@exists_isWeierstrassDivision
    _ _ _ _ _ ((irreducible p).maximalIdeal_eq.substr inferInstance) h).rec fun _ ⟨_, H⟩ ↦
    ⟨_, ⟨_, H.2⟩, H.1, fun _ a _ b ↦ (H.elim h ⟨a, b⟩).2.symm⟩

lemma exists_dvd_sub_sum_z_pow n {N} (e : p ^ n * c.e = N) s : ∃ w : Fin N → WittFq c.f, c.frobE n ∣
  s - ∑ i, w i • c.z ^ i.1 := by simpa [(degreeLT.basis ..).equivFun.exists_congr_left] using
  (c.weierstrass_division n e s).exists

end Chart

end Lift

open Matrix nonZeroDivisors BdRPlus IsDiscreteValuationRing IsScalarTower Finset RingHom Function
  Units Filter algebraMap
variable {p} [ThePrime p] {ι} [Fintype ι] {A} [CommRing A] [Algebra A (PadicAlgCl p)]
  [Algebra A BdR] [IsScalarTower A (PadicAlgCl p) BdR]

/-- For a square matrix W over B_dR^+ and integers k_i, the matrix W·diag(t^k_i) over B_dR. -/
def hodgeMatrix (W : Matrix ι ι BdRPlus) (k : ι → ℤ) := W.map (↑) * diagonal (tUnit ^ k · |>.1)

/-- For square matrices N, P over C_p, integers k_i and g in G_p, the relation
N·gP·diag(χ(g)^k_i) = P. -/
abbrev IsHodgeTateFrame (N P : Matrix ι ι ℂ_[p]) (k : ι → ℤ) g :=
  ∀ w, P *ᵥ (fun i ↦ (cyclotomicGp g ^ (-k i)).1 • g • w i) = N *ᵥ g • P *ᵥ w

attribute [local simp] hodgeMatrix smul_sum comp_def Matrix.mul_apply diagonal dotProduct mul_sum
  mulVec sum_mul mul_assoc Algebra.smul_def

/-- Let W be a matrix over B_dR^+, k_i integers, N a matrix over Q̄_p and g in G_p. If H =
W·diag(t^k_i) satisfies N·gH = H, then N·gθ(W)·diag(χ(g)^k_i) = θ(W) over C_p. -/
lemma isHodgeTateFrame_of_hodgeMatrix {W k} {N : Matrix ι ι A} {g} (h : N.map (↑) * g • hodgeMatrix
  W k = hodgeMatrix W k) : IsHodgeTateFrame (N.map ((↑) : A → PadicAlgCl p)) (W.map thetaBdR) k g :=
  fun _ ↦ by ext i; simpa [← (by simpa [algebraMap_apply A (PadicAlgCl p) BdR, smul_tUnit_zpow,
  ← mul_assoc, ← sum_mul, ← map_mul, ← map_sum, algebraMap_apply _ BdRPlus
                                   BdR, -val_zpow_eq_zpow_val] using congrFun₂ h i)] using! sum_comm

/-- Hodge frame: let j have open image, F be coarser than the near-1 filter, U in GL(B_dR) with
N(g)·gU = U for F-almost all g, N(g) over Q̄_p. Then UY = W·diag(t^k_i), again invariant,
with W in GL(B_dR^+) and Y in SL(Z̄_p) fixed for F-almost all g. -/
lemma exists_hodge_frame Γ [Group Γ] [OverGp Γ p] {F} (hF : nearOne Γ ≤ F) {U} {N : Γ → Matrix ι ι
  A} (hU : IsUnit U) (h : ∀ᶠ g in F, (N g).map ((↑) : A → BdR) * U.map (toGp g • ·) = U) : ∃ Y :
  SpecialLinearGroup ι _, ∃ W k, IsUnit W ∧ (∀ᶠ g in F, Y.1.map (toGp g) = Y) ∧ U * Y.1.map (↑) =
  hodgeMatrix W k ∧ (∀ᶠ g in F, (N g).map (↑) * toGp g • hodgeMatrix W k = hodgeMatrix W k) ∧
  ∀ i l, ‖Y i l‖ ≤ 1 := by
  choose b W hW using IsLocalization.exist_integer_multiples_of_finite BdRPlus⁰ U.uncurry
  have t := prime_tPeriod
  let ⟨d, u, hu⟩ := eq_unit_mul_pow_irreducible (ne_zero b.2) t.irreducible
  refine ((InvImage.wf det wellFounded_dvdNotUnit).has_min {W | ∃ Y k, Y.1 ∈ (intQpBar p).matrix ∧
    _ ∧ _} ⟨of (u.2 • W.curry), 1, -↑d, by
    have := t.1; simp [← ext_iff, *, tUnit, uncurry, field]⟩).elim
    fun W ⟨⟨Y, k, hY, hg, e⟩, hm⟩ ↦ ⟨Y, W, k, (fun H ↦ ⟨?_, hg, e, H, hY⟩) (h.mp (hg.mono
    fun g y h ↦ e ▸ .trans (by simp [← ext_iff]) congr($h * $(y).map _)))⟩
  simp [isUnit_iff_isUnit_det, thetaBdR.map_det, ← exists_mulVec_eq_zero_iff]
  refine fun _ ↦ mt (le_of_hodgeTate_stable ((nhds_one_le_map_nearOne Γ).trans (map_mono hF)) _
    (toLin' _).ker ⊥ (fun v y ↦ H.mono fun _ h ↦
    (isHodgeTateFrame_of_hodgeMatrix h v).trans (by aesop)) (fun a i z n _ _ f ↦ ?_) ·)
  choose V w using fun m ↦ associated_xi_tPeriod.dvd'.trans ((thetaBdR_eq_zero_iff (x :=
    (↑) ∘ a ⬝ᵥ W m)).1 (by simpa [mul_comm] using congr($z m)))
  have hd := (funext w ▸ det_updateCol_sum W i _).symm.trans (det_updateCol_smul ..)
  simp [*, mul_comm] at hd
  cases hm _ ⟨⟨Y * updateCol 1 i a, by simpa [← cramer_apply]⟩, k + Pi.single i 1,
    mul_mem hY (by simpa [updateCol_apply, ite_mem, one_apply] using! n ·),
    (hg.and (.all f)).mono (by simp_all [map_updateCol]), by
    simp [← mul_assoc]; ext _ l; by_cases l = i <;> simp [one_apply, zpow_add₀, *]
    erw [mul_rotate', ← map_mul, ← w]; simp [← IsScalarTower.algebraMap_apply]; grind⟩ ⟨((hU.map
    detMonoidHom).ne_zero <| by simpa [← map_det, ← mapMatrix_apply, ·, *] using congr(det $e)), _,
    t.2.1, mul_comm tPeriod _ ▸ hd⟩
