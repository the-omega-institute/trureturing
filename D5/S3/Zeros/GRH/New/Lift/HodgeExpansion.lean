/- GID: D5/S3/Zeros/GRH/New/Lift/HodgeExpansion
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Lift/HodgeExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Lift.HodgeExpansion. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Lift/HodgeExpansion.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Lift.ExponentLattices
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cokernel bounds and vanishing cup products for Kisin modules (see New.Lift.LongGap).

This file: Galois operators (g-1)/zτ deepen Kisin module elements at explicit cost in p. Exponent
lattices: Frobenius shift, standard exponents give Frobenius pullbacks, exponents add under
pairings. -/

noncomputable section

attribute [-simp] map_smul smul_algebraMap_eq_algebraMap_smul

namespace Lift.KummerChart.JumpLattice

open Submodule DistribSMul algebraMap Module Matrix Set FrobGroup
variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} {L :
  JumpLattice O} {a : ℕ} {i : Letter} {n : ℤ} {x : L.Ambient} (Q : Submodule Ainf L.Ambient)

instance : Module ℤ_[p] L.kisinLoc := inferInstance

/-- For an A_inf-submodule Q of W(C^♭)⊗L, the Z_p-submodule of B =
`Lift.KummerChart.JumpLattice.kisinLoc` of the elements that lie in Q. -/
abbrev locKisinPart := (Q.restrictScalars ℤ_[p]).comap (L.kisinLoc.subtype.restrictScalars _)

/-- The Z_p-module of the x in W(C^♭) ⊗ L that are invariant modulo Q: gx − x lies in Q for all
g in Γ'. -/
def invariantsMod := (⨅ g : k.galMonoid, (Q.restrictScalars ℤ_[p]).comap
  (toLinearMap _ _ g - 1)).copy {x | ∀ g : k.galMonoid, g • x - x ∈ Q} (by aesop)

lemma cost_le_of_isUnramified (hk : IsUnramified) : (↑p ∣ n → n = 0) →
  k.cost a n ≤ 3 * a := by simp [cost, hk.2]; lia

/-- The exponents hi(a, u) where lo(a, u) > 0 and min(hi(a, u), 0) elsewhere; an element of 𝒩
with exponents lo and deep for hi has them. -/
@[simp] abbrev improvedExponent (lo hi : ℕ → ℤ → ℤ) a u :=
  min (hi a u) (ite (0 < lo a u) (hi a u) 0)

/-- If x has exponents lo at the letter i (`Lift.KummerChart.JumpLattice.withExponents`) and gx − x
has exponents hi for all g in Γ', then x has exponents hi(a, u) where lo(a, u) > 0 and min(hi(a, u),
0) elsewhere. -/
lemma mem_withExponents_of_deep {lo hi} (hx : x ∈ withExponents i lo) (H :
  x ∈ invariantsMod (withExponents i hi)) : x ∈ withExponents i (improvedExponent lo hi) :=
  ⟨hx.1, fun a u v μ e ↦ (BdR.exists_sub_mem_of_smul_sub_mem _ _ fun g ↦ valueAt_smul_sub hx.1.1
  e.1 ▸ (H ⟨_, g, rfl⟩).2 a u v μ e).rec fun _ E ↦ (sub_mem_iff_left _ (qpBar_mem_hodgeFil_iff.2
  (qpBar_mem_hodgeFil_iff.1 ((sub_mem_iff_right _ (hodgeFil_anti inf_le_left
  (hx.2 a u v μ e))).1 (hodgeFil_anti inf_le_right E)) ∘ by lia))).1 (hodgeFil_anti inf_le_left E)⟩

lemma galMonoid_smul_localFieldOf (c : localFieldOf k.Γ') : ∀ g : k.galMonoid, g • (c : BdR) = c :=
  fun ⟨_, g, rfl⟩ ↦ by erw [BdR.smul_algebraMap_qpBar, mem_localFieldOf.1 c.2]; rfl

/-- For all a, n there are t_1, …, t_m in Γ' and υ in A_inf such that, for x in 𝒩 and forms μ,
if μ(φ^{−a}x) is in K' modulo t^n, then μφ^{−a} of p^c x + υΣ(t_l − 1)x/(zτ) is in K' modulo
t^{n+1}, c = v_p(n) + d + 3a. -/
lemma exists_reaches_depth_succ a n : ∃ m, ∃ t : Fin m → galMonoid, ∃ υ : Ainf, ∀ x ∈ kisinLoc,
  ∀ μ ∈ L.forms, (∃ c : localFieldOf Γ', valueAt a μ x - c ∈ hodgeFil n) → ∃ c : localFieldOf Γ',
  valueAt a μ (p ^ cost a n • x + ∑ l, υ • zTauUnit⁻¹ • (t l • x - x)) - c ∈ hodgeFil (n + 1) := by
  obtain hn | rfl := ne_or_eq n 0
  · let ⟨t, ω, υ, X, hω, hg, ht, hX⟩ := exists_depth_step a hn
    use 1, ![t], -υ, fun x hx μ hμ ⟨c, e⟩ ↦ ⟨p ^ cost a n • c,
      (add_mem_cancel_right (mul_mem_hodgeFil e (phiInvToBdR_mem_hodgeFil_one_iff.2 ht))).1
      ((mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_zTau a) 1).1 ?_)⟩
    have := congr((valueAt a μ $(smul_inv_smul k.zTauUnit (t • x - x)), phiInvToBdR a $hX))
    convert mul_mem_hodgeFil (x := phiInvToBdR a (-υ)) algebraMap_mem_hodgeFil_zero
      (mul_mem_hodgeFil (galMonoid_smul_mem_hodgeFil t (frobE_zpow_mem_hodgeFil a n))
      (smul_sub_mem_hodgeFil_of_valueField t ![1] (mul_mem (zpow_mem (phiInvToBdR_mem_valueField _)
      _) (sub_mem (valueAt_mem_valueField hμ hx) (by simp))) (neg_add_cancel n ▸
      mul_mem_hodgeFil (frobE_zpow_mem_hodgeFil _ _) e) (by simp [*]))) using 1 <;> cases
      n <;> simp [↓zTauUnit_smul, ↓valueAt_smul_sub hx.1 hμ, smul_sub, hω,
      mul_pow, ↓_root_.zpow_neg, galMonoid_smul_localFieldOf, field] at this ⊢ <;> grind
  exact ⟨_, (exists_depth_step_zero a).imp fun t b ↦
    ⟨k.zTau, fun x hx μ hμ ⟨_, e⟩ ↦ BdR.exists_sub_mem_of_smul_sub_mem _ _ fun g ↦ by
    simpa [← zTauUnit_smul, ← add_eq_of_eq_sub (valueAt_smul_sub hx.1 hμ)] using!
      smul_sub_mem_hodgeFil_of_valueField ⟨_, g, rfl⟩ t
      (valueAt_mem_valueField hμ hx) ((sub_mem_iff_left _ algebraMap_mem_hodgeFil_zero).1 e) (b _)⟩⟩

variable {p : _} [ThePrime p] [Γ : GroupOverGp p] {k : Lift.KummerChart Γ} {O : _} {L A C :
  Lift.KummerChart.JumpLattice O} (b
  : A.Carrier →ₗ[O] L.Carrier →ₗ[O] C.Carrier) {x : L.Ambient} {y : A.Ambient}

/-- For an O-bilinear map b: A × L → C of lattices, its W(C^♭)-bilinear extension (W(C^♭)⊗A) ×
(W(C^♭)⊗L) → W(C^♭)⊗C, tensor products over Z_p. -/
abbrev wittPairing : A.Ambient →ₗ[WittCFlat] L.Ambient →ₗ[WittCFlat] C.Ambient :=
  DiagTensor.pair (b.restrictScalars₁₂ ..)

variable {b} {i : Letter} {n : ℤ} {μ : L.Functional} {l : ℕ} {c : ℕ → ℤ → ℤ}

lemma wittPairing_letterProj_left : ∀ x y, wittPairing b (A.letterProj i y) x = C.letterProj i
  (wittPairing b y x) := diagTensor_induction fun _ _ ↦ diagTensor_induction (by simp [letterProj])

lemma wittPairing_mem_saturateBy {T s t} {Q : Submodule Ainf _} : y ∈ saturateBy T s →
  x ∈ saturateBy T t → (∀ {y x}, y ∈ s → x ∈ t → wittPairing b y x ∈ Q) → wittPairing b y x ∈
  saturateBy T Q := fun ⟨_, r, a⟩ ⟨_, s, b⟩ ↦ (⟨_, mul_mem r s, by simpa [mul_smul] using · a b⟩)

/-- The family of exponents c shifted by l levels: the value at (a, u) is n for a < l and c(a −
l, u) for a ≥ l. -/
@[simp] abbrev frobExponent l (n : ℤ) (c : ℕ → ℤ → ℤ) a u := ite (a < l) n (c (a - l) u)

seal Finset.univ Finset.sum Finset.prod in
/-- For x in Frac(A_inf) ⊗ L: μ(x) ∈ tⁿB_dR^+ provided D(μ)ν(x) ∈ tⁿB_dR^+ for all κ, all ν of type
κ at i, and all Γ'-equivariant B_dR-linear maps D on functionals with D(μ') ∈ t^{m+κ}B_dR^+ whenever
μ'(1 ⊗ L) ⊂ t^mB_dR^+. -/
lemma mem_hodgeFil_of_hodge_basis (hx : x ∈ fracSpan) (H : ∀ κ, ∀ ν ∈ L.formsOfType i κ, ∀ D :
  L.Functional →ₗ[BdR] _, (∀ μ n, (∀ t, μ (.mk 1 t) ∈ hodgeFil n) → D μ ∈ hodgeFil (n + κ)) →
  (∀ μ μ' (g : k.Γ'), (∀ t, μ' (.mk 1 (L.ρ g t))
  = toGp g • μ (.mk 1 t)) → D μ' = toGp g • D μ) → D μ * ν x ∈ hodgeFil n) : μ x ∈ hodgeFil n := by
  obtain ⟨κ, -, -, -, -, P, G⟩ := L.inClass.isPotCrys.exists_hodge_basis (finBasis ..)
  let A := P.map (algebraMap ..).mapMatrix.1 *
    (MulEquiv.piUnits.symm (tUnit ^ κ ·)).map (diagonalRingHom ..).1
  choose ν e using (exists_functional_extend <| (finBasis ..).constr ℕ <| A.2 ·)
  have hν m : basisValues (ν m) = A.2 m := funext (by simp [basisValues, e])
  simpa [apply_eq_of_mem_fracSpan μ (∑ m, (basisValues μ ᵥ* A) m • ν m) (by simp [hν,
    ← vecMul_eq_sum]) hx] using sum_mem fun m _ ↦ H (κ m) _ ⟨forall_comm.1 fun g ↦
    (equivariant_iff_basisValues A.isUnit (G g)).2 (by simp [funext_iff, hν,
    ← mul_apply_eq_vecMul]), fun t ↦ mem_span.1 (ainfLattice_eq_span_basis.le
    (letterProj_mk_mem_ainfLattice t)) (comap _ ((hodgeFil ..).restrictScalars
    _)) (by simp [e, A, mem_hodgeFil, mul_comm])⟩ (.proj m ∘ₗ vecMulLinear A ∘ₗ
    basisValues) (fun _ _ h ↦ sum_mem fun l _ ↦ mul_mem_hodgeFil (h _) (mem_hodgeFil.2 ⟨P.1 l m, by
    simp [A]⟩)) fun _ _ g h ↦ congrFun ((equivariant_iff_basisValues A.isUnit (G g)).1 h) m

lemma valueAt_coordRetract_sub_mem_hodgeFil (hμ : μ ∈ forms) (y : L.kisinLocAinf) {v} (hv :
  v ∈ valueField l) : valueAt l μ y - v ∈ hodgeFil n → valueAt l μ (coordRetract y) - v ∈ hodgeFil
  n := have ⟨_, r, w, e⟩ := mem_span_set'.1 (span_kisinLoc.ge y.2)
  by simpa [coordRetract_sum _ e, ← e, S_smul, sub_eq_neg_add] using
                      sum_map_mem_of_valueField k.coord₀ (Option.rec _ _) (·.elim 1 r) (·.rec
    (neg_mem hv) (valueAt_mem_valueField hμ <| w · |>.2))

lemma coordRetract_mem_withExponents y (e : y.1 ∈ L.withExponents i c) :
  (coordRetract y).1 ∈ L.withExponents i c :=
  ⟨⟨(coordRetract y).2.1, by simpa [mem_letterPart_iff_mulZeta]
  using mulZeta.map_coordRetract y (k.letterTeich i • y) (mem_letterPart_iff_mulZeta.1 e.1.2)⟩,
  fun a u v μ m ↦ by simpa using
  valueAt_coordRetract_sub_mem_hodgeFil m.1 y (zero_mem _) (by simp_all [withExponents])⟩

lemma phi_pow_mem_withExponents (hx : x ∈ withExponents (i.stepBack l) c) :
  φ ^ l • x ∈ withExponents i (frobExponent l 0 c) :=
  ⟨hx.1.imp (span_kisinLoc ▸ (mapsTo_span (f := semilinearAct _) (fun _ ↦ phi_pow_mem_kisinLoc) ·))
  phi_pow_smul_mem_letterPart_iff.2, fun a u v μ e ↦ by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := (lt_or_ge a l).imp (·.dest) (·.dest) <;>
    simp [valueAt, Nat.succ_add, pow_add, mul_smul] at *
  exacts [saturateBy_induction hx.1.1 (by simp_all [kisinAinf, formsOfType, pow_succ, mul_smul])
    fun b y ↦ (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_frobE_of_ne
    (m + b).succ_pos.ne) 1).1 ∘ by simp [↓← valueAt_zero, frobE_eq, frobGroup_smul_smul, smul_smul,
    ← pow_succ', pow_add, mul_assoc], hx.2 m u v μ e]⟩

/-- An element x of W(C^♭) ⊗ L lies in `kisinLocAinf` at the letter i with the standard exponents
(0 at φ^a E for a < l, −u for a ≥ l) if and only if x lies in `frobKisinAinf` l and in the part
at i. -/
lemma mem_withExponents_stdExponent_iff : x ∈ withExponents i (stdExponent l) ↔
  x ∈ frobKisinAinf l ∧ x ∈ letterPart i := by
  obtain ⟨x, rfl⟩ := MulAction.surjective («φ» ^ l) x
  simp [frobKisinAinf, phi_pow_smul_mem_letterPart_iff]
  use fun H ↦ ⟨?_, phi_pow_smul_mem_letterPart_iff.1 H.1.2⟩, fun ⟨m@⟨⟨_, ⟨n, rfl⟩, e⟩, _⟩, hi⟩ ↦
    (phi_pow_mem_withExponents ⟨⟨le_saturateBy m, hi⟩, fun a u _ μ v ↦
    (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_zTau a <| ·.mul_right _) n).1
    (by simpa using valueAt_mem_hodgeFil_of_mem_ainfLattice v e (smul_mem _ _ hi))⟩ :)
  let ⟨_, ⟨n, rfl⟩, e⟩ := saturateBy_induction (C := (_ → · ∈ saturateBy (.powers («φ» ^ l • tau))
    _)) H.1.1 (fun x ⟨⟨_, ⟨n, rfl⟩, e⟩, _⟩ _ ↦ mem_saturateBy_of_smul (by simp [pow_dvd_pow_of_dvd,
    phi_pow_smul, tau, sub_one_dvd_pow_sub_one]) ⟨n, rfl⟩ (le_saturateBy e)) (fun a y e H ↦
    e (smul_mem _ _ H) |> if c : a < l
    then mem_saturateBy_of_smul (frobE_dvd_phi_pow_tau c) (by simp) else .imp fun r ↦ .imp_right (by
    simp [smul_comm r, ainfLattice_eq_span_basis, mem_span_range_iff_exists_fun]; intro b e
    choose μ hμ using (L.exists_functional_extend <| Algebra.linearMap .. ∘ₗ (finBasis ..).coord ·)
    choose w hw using fun s ↦ phiInvToBdR_mem_hodgeFil_one_iff.1 (mem_of_eq_of_mem
      (by simpa [valueAt, hμ, smul_smul, Finsupp.single_apply] using (congr(valueAt a (μ s) $e)))
      (mul_mem_hodgeFil (phiInvToBdR_mem_hodgeFil_one_iff.2 ⟨r, rfl⟩) (mem_hodgeFil_of_hodge_basis
     (smul_mem_fracSpan («φ» ^ a)⁻¹ (kisinLocAinf_le_fracSpan H.1.1)) fun κ _ e _ f _ ↦
      add_neg_cancel (_ + κ) ▸ mul_mem_hodgeFil (f _ _ (hμ
     _ · ▸ algebraMap_mem_hodgeFil_zero)) (valueAt_mem_of_hodgeFil_le _ H e)) :))
    use w, by simp_all [mul_smul, ← Finset.smul_sum])) H
  use ⟨_, ⟨n, rfl⟩, by simpa [frobGroup_smul_smul] using smul_mem_ainfLattice («φ» ^ l)⁻¹ e⟩, fun n
    μ f ↦ by simpa [smul_smul, pow_mul_comm] using (mem_hodgeFil_of_hodge_basis (smul_mem_fracSpan
    («φ» ^ l)⁻¹ (smul_mem_fracSpan _ (kisinLocAinf_le_fracSpan H.1.1))) fun _ _ e _ _ d ↦
    mul_mem_hodgeFil (mem_valueField_of_fixed (d _ _ · (f · _))).1 (valueAt_mem_of_hodgeFil_le _
    (phi_pow_mem_withExponents (i := (k.letterFrob ^ n.succ) i) (by simpa)) e))

lemma letterProj_mem_withExponents (H : x ∈ frobKisinAinf l) : L.letterProj i x ∈ withExponents i
  (stdExponent l) := mem_withExponents_stdExponent_iff.2 ⟨by simp [letterProj, letterOp, smul_pow,
  End.pow_apply, sum_mem, smul_of_tower_mem, smul_of_tower_mem _ _ (MapsTo.iterate
  (fun _ ↦ mulZeta.wittMap_mem_frobKisinAinf) _ H)], letterProj_mem_letterPart⟩

lemma letterProj_mem_of_valueFieldPoints (H : x ∈ L.valueFieldPoints (frobKisinAinf l)) :
    L.letterProj i x ∈ locLetterPart l i := ⟨⟨(letterProj_mem_withExponents H.1).1.1, fun _ ↦
  H.2 _ ∘ comp_letterProj_mem_forms⟩, letterProj_mem_withExponents H.1⟩

/-- Exponents add: for an equivariant O-bilinear b: A × L → C, if y, x have exponents c', c at
the letter i and c''_a(v) ≤ c'_a(u) + c_a(u') for allowed jumps with u + u' ≤ v, then b(y,
x) has exponents c''. -/
lemma wittPairing_mem_withExponents {x : L.Ambient} {b : A.Carrier →ₗ[O] L.Carrier →ₗ[O] C.Carrier}
  {y : A.Ambient} (hb : ∀ g y x, b (A.ρ g y) (L.ρ g x) = C.ρ g (b y x)) {c' c''} (hy :
  y ∈ A.withExponents i c') (hx : x ∈ L.withExponents i c) (H : ∀ a, ∀ u ∈ A.U (i.stepBack a),
  ∀ u' ∈ L.U (i.stepBack a), ∀ v ∈ C.U (i.stepBack a), u + u' ≤ v → c'' a v ≤ c a u' + c' a u) :
  wittPairing b y x ∈ C.withExponents i c'' := have F {μ x y n m} hx (hμ : μ ∈ C.forms) i u (H : ∀ᵉ
    (κ) (ν ∈ L.formsOfType i κ) (σ ∈ A.forms), (μ ∈ C.formsOfType i u → σ ∈ A.formsOfType i
    (u - κ)) → σ (m • y) * ν (m • x) ∈ hodgeFil n) : μ (m • wittPairing b y x) ∈ hodgeFil n :=
    (μ.congr_arg (baseChangePairing_map _ (hb _) ..)).subst (L.mem_hodgeFil_of_hodge_basis
    (smul_mem_fracSpan m hx) fun _ _ e D f d ↦ (fun I ↦ H _ _ e
    (D.restrictScalars _ ∘ₗ ((wittPairing b).restrictScalars₁₂ ..).compr₂ μ) I fun h ↦ ⟨I, fun t ↦
    hodgeFil_anti (by omega) (f _ (-u) (by simp [wittPairing_letterProj_left, h.2]))⟩) fun t ↦
    (d _ _ · (by simp [hb, hμ _])))
  ⟨⟨wittPairing_mem_saturateBy hy.1.1 hx.1.1 fun c d ↦ ⟨wittPairing_mem_saturateBy c.1 d.1
    (LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ ((wittPairing b).restrictScalars₁₂ ..) (by
    simp [mk_one_mem_ainfLattice]) _ _), fun n μ ↦ (F (kisinAinf_le_fracSpan d) · i 0 fun _ _ e _ f
  _ ↦ (mul_mem_hodgeFil (c.2 n _ f) (d.2 n _ e.1) :))⟩, mem_letterPart_iff_letterProj.1 hy.1.2 ▸
    wittPairing_letterProj_left x y ▸ letterProj_mem_letterPart⟩, fun a u _ μ t ↦
  F (kisinLocAinf_le_fracSpan hx.1.1) t.1 _ u fun _ _ e _ _ m ↦ valueAt_mem_of_hodgeFil_le
    ((hodgeFil ..).comap (.mulRight ..)) hy (m t) fun w s d z g ↦ valueAt_mem_of_hodgeFil_le (comap
    (.mulLeft _ z) _) hx e fun v r l _ f ↦ hodgeFil_anti (by grind) (mul_mem_hodgeFil g f)⟩
