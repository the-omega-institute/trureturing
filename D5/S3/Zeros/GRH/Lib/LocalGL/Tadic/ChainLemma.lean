/- GID: D5/S3/Zeros/GRH/Lib/LocalGL/Tadic/ChainLemma
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/LocalGL/Tadic/ChainLemma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.LocalGL.Tadic.ChainLemma. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/LocalGL/Tadic/ChainLemma.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori.HeckeOnLineStabiliser
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Satake parameters of unitary unramified representations of GL_n come in strings.
There is no classification here, and for a spherical Hecke eigenvector in a smooth unitary
representation, a root c with cq not a root has |c|² ≥ q^(N-2), so |c|² q^k = q^N forces c, …,
cq^(k-1) to be roots. The same count makes the vector orthogonal to the image of a polynomial in U
when a string divides. Source: Tadić, Classification of unitary representations in irreducible
representations of general linear group (non-archimedean case), Ann. ENS 19 (1986); Bernstein,
P-invariant distributions on GL(N), LNM 1041 (1983) for the inequality at the ends of segments.

Known result: Exponents, U-operators and spherical vectors at pro-p Iwahori level, and conjugacy in
I t I. The setting here is GL_n at pro-p Iwahori level with tame characters, and eigenforms of the
operators U_t on fixed vectors replace Jacquet modules. No regularity is assumed, ties between roots
are allowed, and conjugacy is twisted by an isometric automorphism of the field. Source: Casselman,
The unramified principal series of p-adic groups I, Compositio 40 (1980), Prop. 2.4, 2.5, 3.6;
Haines–Kottwitz–Prasad, Iwahori–Hecke algebras (arXiv math/0309168) §1;
Görtz–Haines–Kottwitz–Reuman, Compositio 146 (2010), Thm 1.1.5 (conjugacy in I t I).

This file: An unramified exponent with sorted roots is non-zero on spherical vectors. Chain lemma:
spherical vector orthogonal to a polynomial in U; strings of Satake roots. -/

open WithZero Valued Finset Equiv Pi Function Complex ComplexOrder Module Polynomial

attribute [local simp] mulSingle_apply normAbsChar mulSingle_comp_equiv update_apply

/-- Let (`torusChar` θ, l) be an exponent of a smooth ρ with l ≠ 0, all θ_i unramified and |θ_i(ϖ)|
non-increasing in i, ϖ a uniformiser. Then l does not vanish identically on the vectors fixed by
GL_N(𝒪[F]).

Known result: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t
I. -/
lemma IsExponent.eq_zero_of_eq_zero_on_spherical {F} [Field F] [Valued F _] [CompactSpace 𝒪[F]] {N}
  {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {ϖ θ l x} (hϖ : v ϖ.1 = WithZero.exp (-1)) (hl :
  IsExponent ρ (torusChar θ) l) (hu : ∀ y, v y.1 = 1 → ∀ i, (θ i y).1 = 1) (hs :
  Antitone fun i ↦ ‖(θ i ϖ).1‖) (H : ∀ y ∈ levelSpace ρ.ρ (intGL _ 𝒪[F]), l y = 0) : l x = 0 :=
  have L k (hk : k ∈ blockParahoric (min N)) z : l (ρ k z) = l z := by
    have u i : v (k i i) = 1 ∧
      k i i ≠ 0 := by grind [exists_v_entry_eq_one_of_mem_intGL hk.1 i, inv_mem hk, one_pos]
    simpa [hl.apply_diagGL_unit, torusChar, monoidHomMulEquiv, *] using
      hl.apply_proIwahori (diagGL (fun i ↦ (.mk0 _ (u i).2)⁻¹) * k)
      (by simp_all [mem_intGL_iff_det, mem_proIwahori_iff_blockParahoric, mem_blockParahoric]) z
  map_compactMean_of_const l (L · · x) ▸ @Fin.induction N (fun m ↦ ∀ y,
    l (compactMean ρ.ρ (blockParahoric (min m)) y) = 0) (by simp_all [mem_blockParahoric]) (fun m h
    y ↦ by simpa [← Perm.one_def] using (@Fin.induction N (fun j ↦ ∀ x,
    (∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x) → (∀ i, j ≤ i.castSucc →
    l (ρ (permGL (swap m i)) x) = 0) → l (ρ _ x) = 0) (fun _ _ ↦ (· m bot_le)) (fun j ih x X H ↦ by
    by_contra
    have ⟨y, z, hz, D, B⟩ := exists_line_orbit_sums X L
    let q : ℂ := Nat.card 𝓀[F]
    have A (i : Fin N) := by simpa [↓diagGL_mul_permGL] using
      (hl.apply_monomial_translate hϖ hz (·.1)
      (swap m i) (t := mulSingle i ϖ⁻¹) (by simp +decide [apply_ite, ite_apply, *]; grind))
    have := ih ((θ j ϖ).1 • ρ (diagGL (mulSingle m ϖ⁻¹)) z - q ^ N • (1 - q⁻¹) • x) (fun p h e ↦ by
      simpa [X p h e] using hz ⟨_, (conj_monomial_mem_blockParahoric (mulSingle m ϖ⁻¹) 1 .univ (d :=
        Function.update (min · m + 1) m 0) (by clear * - e h; grind) (by
      simp [@apply_ite Fˣ, apply_ite v, apply_ite WithZero.log, hϖ]; lia)).1⟩) fun i c ↦ by
      simp [-sub_eq_zero, A]
      rw [B, sum_eq_zero]; cases j.eq_or_lt_of_le c <;> simp [-sub_eq_zero, field, *]; repeat grind
    simp [*, -swap_self] at *
    simpa [(by grind [NeZero.ne (q ^ _), Nat.cast_eq_one, Finite.one_lt_card,
      sum_Ioi_add_eq_sum_Ici] : θ j ϖ = q * θ m ϖ), q, Finite.one_lt_card.not_ge] using
      @hs m j (by grind)) (.last N) _ (by grind [_root_.apply_compactMean]) (by simp))) ⊤ x

/-- P(dX) equals (X − 1)(X − q)⋯(X − q^{t−1}) times a divisor of the polynomial e. -/
def HasRootString (P e : ℂ[X]) q d t := ∃ S, P.comp (C d * X) =
  (∏ i ∈ range t, (X - C (q ^ i))) * S ∧ S ∣ e

variable {E} [Field E] [NumberField E] {w : FinPlace E} {N} [NeZero N] {ρ : Rep ℂ (GL (Fin N)
  (LocField w))} [IsSmoothRep ρ.ρ] {B x P} {t : ℕ → ℂ} (hB : IsUnitary ρ.ρ B) (hx : x ∈ levelSpace
  ρ.ρ (Kw ..)) (h0 : x ≠ 0) (e : P = heckePoly w.q N t) (ht : ∀ j, heckeGL ρ.ρ j x = t j • x)
include hB hx h0 e ht

/-- Chain lemma. Let x ≠ 0 be a spherical eigenvector with Hecke polynomial P in a smooth
unitary representation of GL_N(E_w), U the operator of diag(ϖ,1,…,1). A root c with P(qc) ≠
0 has |c|² ≥ q^(N−2); if P = ∏_{i≤k}(X − cq^i)·R, c ≠ 0, then x ⊥ (U − cq^k)R(U)y for
pro-p-Iwahori-fixed y.

Known result: Satake parameters of unitary unramified representations of GL_n come in strings. -/
lemma chain_lemma {ϖ} (hϖ : v ϖ.1 = .exp (-1)) : (∀ c, P.IsRoot c → ¬P.IsRoot (w.q * c) →
  w.q ^ N / w.q ^ 2 ≤ ‖c‖ ^ 2) ∧ ∀ d ≠ 0, ∀ k R, HasRootString P R w.q d⁻¹ (k + 1) →
  ∀ y ∈ levelSpace ρ.ρ proIwahori, B x (aeval (heckeCoset ρ.ρ proIwahori (diagGL (mulSingle 0 ϖ)))
  (((X - C (w.q ^ k : ℂ)) * R).comp (C d * X)) y) = 0 := by
  cases' N with n; nomatch ‹NeZero 0›
  -- the adjoint of `G(U)`
  have A {U U' : End ℂ ρ} (S : Set ρ) (a : ∀ y ∈ S, U y ∈ S ∧ ∀ x, B (U' x) y = B x (U y)) ⦃G
      x⦄ : ∀ y ∈ S, B (aeval U' (.map (starRingEnd ℂ) G) x) y = B x (aeval U G y) := by
    induction G using recOnHorner <;> simp_all [mul_comm]
  have S j := compactMean_eq_self (partialHecke ρ.ρ 1 j x)
    (levelSpace_anti proIwahori_le_blockParahoric (partialHecke_mem_levelSpace hx))
  -- the dual count is the same count for the dual lattices
  let y (a : Fin n.succ) := ite (a = 0) 1 ϖ⁻¹
  have h : x ∈ levelSpace (ρ.ρ.comp invTransposeGL.toMonoidHom) (Kw ..) := by simp_all
  have R i (e : i < n) := by simpa (disch := omega) only [Fin.val_zero, partialHecke_dual hϖ hx
                               i.succ, partialHecke_dual hϖ hx i] using
    partialHecke_hyperplane_count hϖ h 0 (ψ := compactMean ρ.ρ _ * ρ (diagGL y⁻¹)) (fun k o hk z ↦
    .trans (by simp) (compactMean_apply (mem_proIwahori_iff_blockParahoric.2
    (conj_monomial_mem_blockParahoric y 1 _ (d := 0) ⟨⟨(invTransposeGL_mem_intGL _).2 hk.1, nofun⟩,
    (inv_mem hk).2.2⟩ (by simp [y, invTransposeGL, transposeGL, Fin.forall_fin_succ, hϖ]; clear * -
                            o; grind))) _)) (n - i.succ)
  -- `U` and its adjoint `U'`, with the count and its dual read on them
  let u g := (w.q : ℂ) ^ n • (compactMean ρ.ρ proIwahori * ρ g * compactMean ρ.ρ proIwahori)
  have G g {y} (h : _ = y) : u g y = _ := congr((_ : ℂ) • compactMean _ _ (ρ _ $h))
  have I g x y : B (u g⁻¹ x) y =
    B x (u g y) := by simp [u, hB.adjoint_eq_inv, hB.compactMean_adjoint]
  obtain ⟨t0, s, hq, h1, D⟩ := ht 0 ▸ heckeGL_zero hx, S 0, (by simp : (1 : ℂ) < w.q),
    partialHecke_hyperplane_count hϖ hx 0 fun _ _ ↦ compactMean_apply,
    partialHecke_zero_right h ▸ partialHecke_dual hϖ hx _ n.succ.zero_add
  have L := congr(ρ (diagGL y⁻¹) $(D.symm.trans
    (partialHecke_zero_right h ▸ partialHecke_dual hϖ hx n (add_comm ..))))
  set β := diagGL (mulSingle (0 : Fin n.succ) ϖ)
  simp [partialHecke_zero_right hx, ht, S, partialHecke_zero_eq_heckeGL, y,
    (by simp [β, y, Units.ext_iff, diagGL, invTransposeGL, transposeGL,
    -Matrix.coe_units_inv, Fin.forall_fin_succ] : diagGL (fun _ ↦ ϖ⁻¹) = diagGL y * β⁻¹ ∧
    invTransposeGL β = diagGL y * β⁻¹ * diagGL y⁻¹)] at s L D h1 R
  obtain ⟨tn, adj, J, Q, Z, L', K⟩ := left_ne_zero_of_smul (h0 ∘ D.trans), I β, I β⁻¹, one_lt_pow₀
    hq n.succ_ne_zero, by simpa [← L] using (h1 n).symm, G β⁻¹ s,
    @A (heckeCoset ρ.ρ proIwahori β) (u β⁻¹)
    (levelSpace ρ.ρ proIwahori) (by simp +contextual [↓I, u, β, heckeCoset_mulSingle_zero_eq hϖ])
  simp [← G, S, (eq_inv_smul_iff₀ tn).2 L] at R h1 L'
  generalize u β = U, u β⁻¹ = U' at *; clear! u h D; let p := (heckePoly w.q · t)
  have a m : (p m).aeval U x = ((-1) ^ m * w.q ^ m.choose 2 : ℂ) • partialHecke ρ.ρ 1 m x ∧ ∀ c,
    m - 1 ≤ n → ∃ D, (X - C c) * D = p m - C ((p m).eval c) ∧ c • U' (aeval U D x) = ((p m).eval
    (w.q * c) / w.q ^ m) • U' x + (w.q ^ n / w.q : ℂ) • aeval U D x - U' (aeval U (p m) x) := by
    induction' m with m a; simpa [p, heckePoly, partialHecke_zero_right hx]
    rw [(by ext ⟨⟩ <;> simp [p, coeff_one] : p m.succ = X * p m + coeff (p m.succ) 0 • 1),
      coeff_heckePoly]
    use by simp [*, Nat.choose]; module, fun c (h : m ≤ n) ↦ (a.2 c (by omega)).elim fun D b ↦
      ⟨c • D + p m, by simp [smul_eq_C_mul]; linear_combination C c * b.1, ?_⟩
    obtain ⟨⟨⟩⟩ := h.eq_or_lt <;> simp [*, Nat.choose, pow_sub₀] <;> match_scalars <;> field
  choose hP D f d using by simpa [p, ← e, Z] using a n.succ
  -- a polynomial in `U` that kills `x` kills its cyclic module, which `U'` keeps
  have M {y} {V F : ℂ[X]} (N : V.aeval U x = 0) : ∀ j ≤ n, B y (V.aeval U (F.aeval U' (partialHecke
    ρ.ρ 1 j x))) = 0 := have m j := by simpa [*] using congr(aeval U $(mul_comm V (p j)) x)
    by induction F using recOnHorner <;> rintro ⟨⟩ <;> simp +contextual [*, le_of_lt,
                congr(U' $(partialHecke_zero_right hx)).trans L']
  have u c := congr(aeval U $(f c) x); simp [hP, sub_eq_iff_eq_add] at d u
  have k c := by simpa [← adj, L', Z, h1, field, u, ← J, tn] using congr(B x (U $(d c)))
  use fun c h o ↦ have g := congr(B $(d c) (aeval U (D c) x)); real_le_real.1 (sub_pos.1
    (pos_of_mul_pos_left ((hB.1 _ (smul_ne_zero o h0)).trans_eq (by
      simp [adj, u, ← mul_conj', field] at g h ⊢; clear * - g h k s Q;
      grind)) (mul_nonneg (sub_pos.2
      (lt_mul_self Q)).le ((em' _).elim (hB.1 (aeval U (D c) x) · |>.le) (by simp [·]))))).le
  -- if `c` and `q c` are roots, `(P / (X - c))(U) x` is zero, so these roots cancel
  have Y c F (E : (X - C c) * F = P) (r : P.IsRoot (w.q * c)) (o : c ≠ 0) : aeval U F x = 0 := by
    cases (by simpa [← E, X_ne_C] using f c); simp [f] at E r
    refine by_contra (hB.1 _ · |>.ne' ((recOnHorner · ?_ ?_ ?_ : ∀ G, B (aeval U G x) _ = 0)
      _)) <;> simp +contextual [J, r, ← X_mul, (eq_inv_smul_iff₀ o).2 (d c)]
    clear * - k E r s o Q; grind [Q.ne']
  rintro c hc l _ ⟨W, h, F, rfl⟩ y m
  replace h := (funext (by simp [hc]) : P = _).trans (congrArg (Polynomial.comp · (C c * X)) h)
  rw [← mul_assoc, mul_comm, ← partialHecke_zero_right hx, ← K y m,
    Not.imp_symm (hB.1 _) ((A ⊤ (by tauto) _ ⟨⟩).trans (M ?_ 0 bot_le)).not_gt, B.map_zero₂]
  induction' l with l ih generalizing W F; simp [by simpa [h] using hP]
  rw [prod_range_succ, mul_assoc] at h; set V := _ * W
  specialize Y (w.q ^ l / c) (c • (_ * V).comp (C c * X)) (.symm (funext (by
    simp [h, field, prod_range_succ]))) (by simp [h, V, field, pow_succ])
  simp [by simpa [hc, eval_prod, prod_eq_zero_iff, End.aeval_apply_of_mem_apply_eq_smul (by
    simpa [← eq_inv_smul_iff₀ hc, smul_smul, -map_pow] using ih _ 1 h),
    (pow_right_strictMono₀ hq).injective.eq_iff] using Y]

/-- Let x ≠ 0 be a spherical Hecke eigenvector in a smooth unitary representation of GL_N(E_w),
with Hecke polynomial P. If P(c) = 0 and |c|² q^k = q^N, then c, cq, …, cq^(k−1) are all
roots of P.

Known result: Satake parameters of unitary unramified representations of GL_n come in strings. -/
lemma isRoot_string_of_norm {c k} (hc : P.IsRoot c) (h : ‖c‖ ^ 2 * w.q ^ k = w.q ^ N) {i} (hi :
  i < k) : P.IsRoot (c * w.q ^ i) := by
  induction' i using Nat.strongRec with i ih
  obtain ⟨j, ⟨⟩⟩ := hi.dest
  by_contra; refine this (star_eq_zero.1 (.trans ?_ (mul_eq_zero_of_right ((-star c * w.q ^ i) ^ N *
    B (ρ (.scalar _ (uniformizer w)) x) x / B x x / w.q ^ N.choose 2) (ih j ?_ (by lia)))))
  simp [e, heckePoly, eval_finsetSum, mul_sum]; convert sum_flip _ with d
  cases' exists_add_of_le (mem_range_succ_iff.1 ‹_›) with b hd
  field [(hB.1 x h0).ne']
  linear_combination (norm := (simp [-sub_eq_zero, hd, ← mul_conj', ← heckeGL.eq_1, ht]; ring; simp
    [field])) -congr((star c * w.q ^ i) ^ b * w.q ^ $(show b.choose 2 + N * d = N.choose 2 +
    d.choose 2 + d by qify [*, Nat.cast_choose_two]; ring) * (-$h / w.q ^ N.succ) ^ d *
    $((heckeGL_dual hx (v_uniformizer w) (by simpa) ▸ hB.2 _ x _).trans (by simpa [Set.indicator]
    using ((isBiInvariant_basicDoubleCoset _).heckeFun_adjoint B hx hB.2 hx).2.symm)))
  cases i; lia; simpa +arith [eq_div_of_mul_eq _ h, field, ← pow_mul, ← pow_add,
    pow_le_pow_iff_right₀] using
    (chain_lemma hB hx h0 e ht (v_uniformizer w)).1 _ (ih _ .refl hi.le) (by grind)
