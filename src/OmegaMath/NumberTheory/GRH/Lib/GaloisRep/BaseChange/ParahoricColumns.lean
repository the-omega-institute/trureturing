import OmegaMath.NumberTheory.GRH.Lib.LocalGL.Iwahori.HeckeCounts
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Local matching of pro-p Iwahori double cosets of t and its norm. Sums over columns of a
parahoric, counting vectors by last non-zero coordinate. -/
seal Finset.univ Finset.sum Finset.prod

open DoubleCoset Finset Fint Function IsLocalRing Matrix Polynomial Valued WithZero

attribute [-simp] RingHom.coe_pow

variable {F N} [Field F] [Valued F ℤᵐ⁰] {σ : F →+* F} (hv : ∀ x, v (σ x) = v x)

include hv

lemma map_mem_proIwahori_iff_of_isometry {g : GL (Fin N) F} : g.map σ ∈ proIwahori ↔
  g ∈ proIwahori := map_mem_proIwahori_iff_of_isEquiv (.of_eq (by bound))

lemma v_ringHom_pow_apply i x : v ((σ ^ i) x) = v x := i.rec rfl (by simp_all [pow_succ'])

attribute [local simp] charpoly_diagonal map_smul' Matrix.sum_apply twistedNorm_mem
  twistedNorm_succ' eval_prod diagGL_mem_proIwahori map_mem_proIwahori_iff_of_isometry mul_assoc
  mul_mem_cancel_left pow_succ' v_ringHom_pow_apply

variable {N : ℕ} {m : Fin N} {p : ℕ} {F'} [Field F'] [Valued F' ℤᵐ⁰] [CompactSpace 𝒪[F']]

/-- Hilbert 90 for the pro-unipotent Iwahori subgroup I of GL_n(F): if σ is an isometry with σ^p
= 1 and some integer of F has σ-trace 1, every s in I of twisted norm 1 satisfies sσ(t) = t
for some t in I. -/
lemma exists_coboundary_proIwahori (hσ : σ ^ p = 1) {c} (vc : v c ≤ 1) (hc : ∑ i ∈ range p,
  (σ ^ i) c = 1) {s : GL (Fin N) F} (hs : s ∈ proIwahori) (e : twistedNorm (.map σ) p s = 1) :
  ∃ t ∈ proIwahori, s * t.map σ = t :=
  have := (mem_proIwahori.1 <| twistedNorm_mem (.map σ) · (by simp [*]) hs)
  (exists_proIwahori_coe_eq (∑ l ∈ range p, (σ ^ l) c • (twistedNorm (.map σ) l s).1)
    (by simp_all [v.map_sum_le, mul_le_one']) (by simp_all (maxDischargeDepth := 3) [← hc,
    ← sum_sub_distrib, ← mul_sub_one, v.map_sum_lt, mul_lt_of_le_one_of_lt])).imp fun _ ⟨k, h⟩ ↦
    ⟨k, Units.ext (h ▸ fixed_sum (.comp (.mulLeft s.1) σ.mapMatrix.toAddMonoidHom) _ (by aesop) :)⟩

/-- If the norm Nm is onto on principal units, t strictly dominant, I, I' pro-unipotent Iwahori:
either no point of I'Nm(t)I' and no norm from ItI has characteristic polynomial P, or some z
with P ∣ Nm z − X matches the two double cosets by γ ↦ z(γ), uniquely modulo I. -/
lemma proIwahori_doubleCoset_match [CompactSpace 𝒪[F]]
    (hσ : σ ^ p = 1) (hp : 0 < p) (cont : Continuous σ) {ι :
  F' →+* F} (fix : ∀ x, σ x = x → x ∈ ι.range) (he : (v.comap ι).IsEquiv v) (hn : ∀ x,
  v (ι x - 1) < 1 → ∃ y : Fˣ, v (y.1 - 1) < 1 ∧ ∏ i ∈ range p, (σ ^ i) y = ι x)
    {t s : Fin N → _} (ht :
  StrictMono (v <| t · |>.1)) (ht' : StrictMono (v <| s · |>.1)) (hs : (diagGL s).map ι =
  twistedNorm (.map σ) p (diagGL t)) P (H : P ∈ (·.1.charpoly) '' (.map ι '' iwahoriDoubleCoset s ∪
  twistedNorm (.map σ) p '' iwahoriDoubleCoset t)) : ∃ z, P ∣ twistedNorm (.map σ) p z - X ∧
  ∀ γ a : GL (Fin N) F, γ.1.charpoly = P → a = aeval γ.1 z → (∀ x, x.map ι = γ →
  twistedNorm (.map σ) p a = γ → (x ∈ iwahoriDoubleCoset s ↔ a ∈ iwahoriDoubleCoset t)) ∧
  ∀ δ ∈ iwahoriDoubleCoset t, twistedNorm (.map σ) p δ = γ → a⁻¹ * δ ∈ proIwahori := by
  have fp k : (GeneralLinearGroup.map (n := Fin N) σ)^[p] k =
    k := congr(k.map $hσ).subst (p.rec .refl (by tauto) k)
  let ν d := twistedNorm (.map σ) p (diagGL (t * d))
  let ρ d i := ∏ l ∈ range p, (σ ^ l) ((t * d) i)
  have cν d : ν d = diagonal (ρ d) := twistedNorm_diagGL ..
  have A δ := exists_twisted_conj_diag (g := δ) ht σ hv cont (periodicPts_subset_range ⟨p, hp,
    fp ·⟩)
  have hT {x} (g : x ∈ iwahoriDoubleCoset s) : ∃ k ∈ proIwahori, ∃ d, diagGL d ∈ proIwahori ∧
    k⁻¹ * x.map ι * k = ν d := by
    choose k u d h H using exists_twisted_conj_diag ht' 1 (by simp) continuous_id surjective_id g
    rw [← map_mem_proIwahori_iff_of_isEquiv he] at *; choose y o e using (hn _ <| h.2.2 ·)
    exact ⟨_, u, y, by simpa [Units.ext_iff, ρ, *, -H] using congr(GeneralLinearGroup.map ι $H)⟩
  obtain ⟨d₀, h₀, ⟨⟩⟩ : ∃ d, diagGL d ∈ proIwahori ∧ (ν d).1.charpoly = P := by
    simp at H; grind [twistedNorm_conj, charpoly_units_conj', Units.val_mul, coe_units_inv]
  have inj {d} (h : diagGL d ∈ proIwahori) i l (e : ρ d i = ρ d₀ l) := ht.injective
    (by simpa [ρ, *, hp.ne', (by simpa using And.intro (v_diag_eq_one_of_mem_proIwahori h)
                                   (v_diag_eq_one_of_mem_proIwahori h₀))] using congr(v $e))
  choose z Z using (exists_eval_eq_iff (ρ _) ((t * d₀) ·)).2 (by tauto)
  use z, by simpa [*] using (Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C (inj h₀))
    (by simp [dvd_iff_isRoot, twistedNorm_map_eq_prod]; congr!; rw [← Z,
    ← eval_map_apply, σ.coe_pow, (isFixedPt_norm hσ).iterate])), fun γ a hγ H ↦ ?_
  have ac {d k} (o : diagGL d ∈ proIwahori) (h : k⁻¹ * γ * k = ν d) : k * diagGL (t * d₀) * k⁻¹ =
    a := by
    simpa [↓mul_inv_eq_iff_eq_mul, Units.ext_iff, ↓aeval_algHom_apply, aeval_pi_apply, *, fun i ↦
      Exists.elim (by simpa [prod_eq_zero_iff, -mul_assoc, cν, hγ] using
      congr(($h).1.charpoly.IsRoot (ρ d i))) fun l e ↦ (inj o i l e).symm ▸ e] using
      aeval_semiconj (x := diagonalAlgHom F (ρ d)) (by simp [← cν, ← h]) z
  use fun x r _ ↦ ⟨(mem_doubleCoset.2 <| hT · |>.imp fun k ⟨u, _⟩ ↦ ⟨u, _, mul_mem h₀
    (inv_mem u), by grind⟩), ?_⟩, ?_ <;> intros <;> choose k u d o h using A _ ‹_› <;>
    have e := (by grind [twistedNorm_conj] : k⁻¹ * γ * k = ν d) <;> cases ac o e
  refine mem_doubleCoset.2 (.imp (fun g G ↦ ⟨?_, _, ?_, eq_mul_of_inv_mul_eq rfl⟩)
    (exists_gl_map_eq_of_fixed ι.injective fix (g := k * diagGL (.mk0 _ <| v.pos_iff.1 <|
    v_diag_eq_one_of_mem_proIwahori u · ▸ one_pos)⁻¹) (GeneralLinearGroup.ext
    (by simp [-map_inv, by simpa [← map_inv] using (congr($(eq_inv_mul_of_mul_eq h) · ·))]))))
  repeat simp [*, ← map_mem_proIwahori_iff_of_isEquiv he, eq_mul_inv_of_mul_eq e,
    eq_mul_inv_of_mul_eq h, u.2.2,
    mul_mem_cancel_right, fun e k ↦ (GeneralLinearGroup.ext (by simp [*, ρ, mul_left_comm]) :
    diagGL e * (ν d * k) = (diagGL s).map ι * (diagGL e * (twistedNorm (.map σ) p (diagGL d) * k)))]

attribute [-simp] residue_eq_zero_iff ZeroMemClass.coe_eq_zero

attribute [local simp] updateCol_apply PEquiv.mul_toMatrix_toPEquiv Subgroup.inclusion

omit hv

lemma exists_v_entry_eq_one_of_mem_intGL {k} (hk : k ∈ intGL (Fin N) 𝒪[F]) m : ∃ r,
  v (k⁻¹ m r) = 1 ∧ v (k r m) = 1 := by grind [mem_intGL, mul_lt_of_lt_of_le_one, v.mem_integer_iff,
  (v.map_sum_lt' one_pos).mt (by simp : ¬v ((k⁻¹ * k) m m) < 1)]

variable [CompactSpace 𝒪[F]]

/-- Counting by the last nonzero coordinate, indices 0,…,N−1: the sum of a_{j(c)} over c ∈ 𝔽_q^N
nonzero on I with last nonzero coordinate j(c) ≥ m equals ∑ q^{j+1}(1−1/q)^{|I∪{j}|} a_j
over the j ≥ m that bound I from above. -/
lemma sum_by_last_nonzero_coord (a : _ → ℂ) I : letI q : ℂ := Nat.card 𝓀[F]; ∑ c : _ → 𝓀[F] with
    ∀ s ∈ I, c s ≠ 0, ∑ j ≥ m with c j ≠ 0 ∧ ∀ r > j, c r = 0, a j = ∑ j with m ≤ j ∧ I ⊆ Iic j,
    q ^ N * ((1 - q⁻¹) ^ #(insert j I) / q ^ #(Ioi j)) * a j := by
  rw [sum_comm' (s' := fun j ↦ Fintype.piFinset fun r ↦ ite (r ∈ insert j I) {0}ᶜ
    (ite (j < r) {0} univ)), ← Fin.prod_const]
  push_cast [sum_const, nsmul_eq_mul, ← prod_ite_mem_eq (insert ..), ← prod_const,
    ← (Ioi _).prod_ite_mem_eq, ← prod_div_distrib, ← prod_mul_distrib, Fintype.card_piFinset]
  congr!; split_ifs <;> simp [mul_sub, card_compl, Fin.pos']; repeat grind [mem_compl]

/-- Let P ⊂ GL_N(𝒪) have columns before m in 𝔭 below the diagonal, x be fixed by the p ∈ P with
column m in 𝔭 off the diagonal, φ Iwahori-invariant, a_j = (q−1)q^j φ((m j)x), indices from
0. Some P-fixed y has φ(y) = ∑_{j≥m} a_j; some z, fixed by the p ∈ P with row m in 𝔭 off the
diagonal, has φ((m i)z) = a_i + (1−1/q)∑_{j>i} a_j for i ≥ m. -/
lemma exists_line_orbit_sums {ρ : Rep ℂ (GL _ F)} [IsSmoothRep ρ.ρ] {x} {φ : ρ →ₗ[ℂ] ℂ}
    (hx : ∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x)
    (hφ : ∀ k ∈ blockParahoric (min N), ∀ z, φ (ρ k z) = φ z) : let q : ℂ := Nat.card 𝓀[F]
  let a j := q ^ N * ((1 - q⁻¹) / q ^ j.rev.1) * φ (ρ (permGL (.swap m j)) x)
  ∃ y, ∃ z ∈ levelSpace ρ.ρ (blockParahoric (Function.update (min m) m N)),
    φ (compactMean ρ.ρ (blockParahoric (min m)) y) =
    ∑ j ≥ m, a j ∧ ∀ i ≥ m, φ (ρ (permGL (.swap m i)) z) = (1 - q⁻¹) * ∑ j > i, a j + a i := by
  let κ := (intGL.map (residue _)).comp ((@blockParahoric F _ _ N (min m)).inclusion fun _ ↦ (·.1))
  let π k := (κ k · m)
  have M k p : κ k *ᵥ π p = π (k * p) := by simp [π]; rfl
  let X := π.extend (ρ · x) 0
  have S p : X (π p) = _ := FactorsThrough.extend_apply (fun u t e ↦ by simpa using (hx _ (t⁻¹ *
    u).2 fun a _ ↦ by simpa [↓M, π, κ, *, ← ZeroMemClass.zero_def] using congr((κ t⁻¹ *ᵥ $e) a))) ..
  let Y (I : Finset _) := ∑ c with ∀ s ∈ I, c s ≠ 0, X c
  have C I : φ (Y I) = _ := .trans (by
    simp [Y]; congr with c; by_cases! h : ∀ r ≥ m, c r = 0
    grind [sum_eq_zero, show X c = 0 from dite_eq_right fun ⟨⟨p, H⟩, e⟩ ↦ by
      simp [← e, π, κ] at h; grind [exists_v_entry_eq_one_of_mem_intGL H.1 m, inv_mem H]]
    obtain ⟨c, rfl⟩ := residue_surjective.comp_left c
    have ⟨j, _, _⟩ := exists_maximal_of_wellFoundedGT _ h; simp at *
    erw [sum_eq_single j, show _ ∘ c = π (⟨.mk'' (updateCol 1 j (c ·)) ?_, ?_⟩ * ⟨_,
      permGL_mem_intGL _, ?_⟩) from ?_, S, map_mul, hφ]; swap
    all_goals simp [← cramer_apply, mem_blockParahoric, mem_intGL_iff_det, π, κ]; grind
      [one_pos, v.mem_integer_iff]) (sum_by_last_nonzero_coord (m :=
    m) (φ ∘ (ρ · x) ∘ permGL ∘ Equiv.swap m) I)
  have G k {I} i (h : ∀ a ∈ I, ∀ r ≠ a, κ k i r = 0) : ρ k (Y I) = Y (I.image fun _ ↦ i) :=
    (map_sum ..).trans (sum_equiv (κ k).toLin.toLinearEquiv (by
    simp_intro c [entrywise]; peel with a
    grind [sum_eq_single a, (κ k).det_ne_zero, det_eq_zero_of_row_eq_zero i]) fun c _ ↦ by
    obtain ⟨p, rfl⟩ | h := em (∃ p, π p = c) <;> simp [X, *]
    exact .symm (dite_eq_right (h ∘ .imp' (k⁻¹ * ·) (by simp_all [← M]))))
  use Y ∅, Y {m}, (G ⟨·, by grind⟩ m ?_ ▸ ?_), ?_, fun i h ↦ G ⟨_, permGL_mem_intGL _, ?_⟩ i ?_ ▸ ?_
    <;> simp [mul_sum, ← sup_le_iff, G _ m, κ, *,
    filter_le_eq_Ici, card_insert_eq_ite, ← sum_Ioi_add_eq_sum_Ici] <;> grind [sum_congr, one_pos]
