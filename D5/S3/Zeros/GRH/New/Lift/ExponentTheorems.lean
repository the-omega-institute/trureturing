/- GID: D5/S3/Zeros/GRH/New/Lift/ExponentTheorems
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Lift/ExponentTheorems
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Lift.ExponentTheorems. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Lift/ExponentTheorems.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.GoodCriterion
import D5.S3.Zeros.GRH.New.Lift.SparseThickLetters
import D5.S3.Zeros.GRH.New.Lift.FewLowJumps
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! (In the statements a jump is a Hodge–Tate weight, and Z_f the crystalline cocycles.) An exponent
independent of the ramification index for tame types. Over Q_ℓ, for potentially
crystalline lattices of tame inertial type with weights in two windows small against ℓ, a power of ℓ
makes Bloch–Kato classes cup to zero with those of congruent dual lattices, and the exponent, used
in the Selmer bound, depends on the sizes of the types and windows, not on the ramification index.
Small ramification, the tame potentially Barsotti–Tate case, and Kisin modules with descent data for
generic tame types are known. Related work: Iovita–Marmora, Continuity of the finite Bloch–Kato
cohomology, 2015; Nekovář, Compatibility of arithmetic and algebraic local constants II, 2018; Le–Le
Hung–Levin–Morra, Local models for Galois deformation rings, 2023.

Length bound for crystalline classes with few low weights. Over unramified ℓ-adic fields, if ℓ
divides no non-zero integer near 0 or the large weights, crystalline classes modulo those cupping to
zero with congruent dual lattices have length O(large weight/ℓ) per low weight plus O(rank × window
width), and length zero when there are no small negative weights; this bounds the loss above ℓ in
the Selmer bound. The absence of loss for weights below ℓ−1, exact Breuil–Kisin sequences for
weights of one sign, and torsion located by weights modulo ℓ are known. Related work:
Iovita–Marmora, Continuity of the finite Bloch–Kato cohomology, 2015; Čoupek–Gazaki–Marmora,
Exactness of Breuil–Kisin functors, 2026; Gao–Liu, Integral filtered Sen theory and applications,
2024.

This file: Final exponent and length bounds for crystalline classes against congruent dual
lattices. The prime ℓ of this comment is p in the code. -/

namespace Lift

open Polynomial Module Finset KummerChart JumpLattice Function IsLocalRing Topology Filter
variable {p} [l : ThePrime p] [Γ :
  GroupOverGp p] {O : Type} [CommRing O] {r N : ℕ} [PadicIntegerRing O p] [TopologicalSpace Γ] {L :
  GalLattice O Γ} {U U' : _ → Finset ℤ} (k : KummerChart Γ) (ζ : LetterRoot O) (ho :
  IsOpenEmbedding Γ.overGp.toGp) {F} (hF : map k.Γ'.subtype ⊤ ≤ F)

variable (p r N) in
/-- K holds for X^M − 1, M = lcm of the p^j − 1 for 1 ≤ j ≤ r, and for some monic polynomial over
ℤ_p of degree ≤ N. -/
def IsTameType (K : O[X] → _) := K (X ^ (Icc 1 r).lcm (p ^ · - 1) - 1) ∧
  ∃ q : ℤ_[p][X], q.Monic ∧ q.natDegree ≤ N ∧ K (q.map (algebraMap ..))

/-- For a letter i, the union of {0} and the finite sets U(g) over the Z_p-algebra maps g: O →
C_p with g(ζ) = θ(ω(i)). -/
noncomputable def KummerChart.letterJumps (U : (O →ₐ[ℤ_[p]] ℂ_[p]) → Finset ℤ) i :=
  insert 0 (Finset.biUnion {g | g ζ = ↑(theta (k.letterTeich i))} U)

/-- For L satisfying `Lift.InClass` F ⊥ U, with F containing only supersets of Γ': the side with
lattice L, jump sets `Lift.KummerChart.letterJumps` ζ U, C = Z_f(L) with trivial action, α the
identity. -/
noncomputable abbrev KummerChart.universalSide (h : InClass F ⊥ U L) : PairingSide ⟨O,
  ζ⟩ := have := crysCocycles.fg h.isPotCrys; ⟨⟨L, k.letterJumps ζ U, U, h.imp_left (.mono · (by
    gcongr)), by grind [letterJumps]⟩, ⟨crysCocycles L.ρ, 1⟩, .id, by simp [letterJumps]⟩

include ho

lemma KummerChart.mem_cupOrthogonal_of_scaledCupBounds {Q} (hc : Q ≤ InClass F ⊥ U) (hL :
  InClass F ⊥ U' L) e x (H : ∀ Y a (P : (k.universalSide ζ hF (hc Y
  a)).SidePairing (k.universalSide ζ hF hL)) c, P.ScaledCupBounds e c x) :
  (p : O) ^ e • x.1 ∈ cupOrthogonal Q L := fun Y P b y c ↦ mod_cast H Y b P ⟨y, c⟩ ho

/-- Unramified chart, p ≥ 5, L crystalline, U and U' in opposite windows, size and gap conditions.
Z_f(L) is orthogonal to crystalline lattices with jumps in U if neither U nor U' meets
[−a, 0), or U' lies in [−η, 0]; with ≤ m jumps in [−η, η], the defect has length ≤
11f(m(a+1) + (W+1) rk
L)·len(O/p). Orthogonal: in `Lift.cupOrthogonal`; defect: Z_f(L) modulo that part; U' holds the
jumps of L; p^f − 1 is the number of letters.

Length bound for crystalline classes with few low weights. -/
lemma KummerChart.few_low_jumps (hk : IsUnramified) (hp : 5 ≤ p) {a η W} {b : _ → ℕ} {ε : _ →
  _} (ha : ∀ n, b n + W + η ≤ (p - 3) * a) (hη : 1 ≤ η) (hb : ∀ n, 6 * (a + η + W) < b n) (hs : ∀ n,
  NoMultipleNear p (6 * (a + η + W)) (b n)) (hL : InClass ⊤ ⊥ U' L) (hV : ∀ i, IsInJumpWindow η
  (-ε i) (b i) W (k.letterJumps ζ U i) ∧ IsInJumpWindow η (ε i) (b i) W (k.letterJumps ζ U' i)) :
  ((∀ g u, u ∈ U g ∨ u ∈ U' g → u ∉ Ico (-↑a) 0) ∨ (∀ g, U' g ⊆ Icc (-η) 0) → crysCocycles L.ρ ≤
  cupOrthogonal (InClass ⊤ ⊥ U) L) ∧ ∀ m, (∀ g, ∑ u ∈ Icc (-↑η) ↑η, jump L.ρ g u ≤ m) →
  relLength (crysCocycles L.ρ) (cupOrthogonal (InClass ⊤ ⊥ U) L) ≤
  ↑(11 * (k.f * (m * (a + 1) + finrank O L * (W + 1)))) * length O (O ⧸ Ideal.span {(p : O)}) := by
  obtain M := k.mem_cupOrthogonal_of_scaledCupBounds ζ ho le_top le_rfl hL 0
  refine ⟨fun h₀ x m ↦ ?_, fun m hm ↦ (ENat.mul_le_mul_right_iff length_pos.ne' length_ne_top).1
    ((length_restrictScalars ℤ_[p] ..).ge.trans ?_)⟩
  · simpa using M ⟨x, m⟩ fun _ _ Q
      _ ↦ by apply Q.scaledCupBounds_of_killsCokernel (κ := 0) _ hs hV <;> (try intro <;>
      and_intros <;> apply PairingSide.killsCokernel_of_isUnramified) <;> simp [*,
      hk.2] <;> clear * - h₀ ha hb hV <;> grind [letterJumps]
  rw [mul_assoc, ← length_restrictScalars, ← map_natCast (algebraMap ℤ_[p] O),
    ← Set.image_singleton, ← Ideal.map_span, ← PadicInt.maximalIdeal_eq_span_p,
    length_eq_of_surjective residue_surjective (R := _ ⧸ _) (M := O ⧸ _),
    @length_eq_finrank _ _ (Ideal.Quotient.divisionRing _), finrank_quotient_map]
  refine ((k.universalSide ζ le_top hL).exists_scaledCupBounds_few_low_jumps hk hp ha hb hs
    (hV · |>.2) (by intro; grw [← mul_sum, sum_comm, hm]) (by intro; grw [← mul_sum, sum_comm,
    sum_le_sum fun g _ ↦ (hL.isPotCrys.exists_hasJumps g).rec fun J ⟨a, e⟩ ↦ funext e ▸ a ▸
    (sum_le_sum_of_ne_zero (by simp)).trans_eq J.toFinset_sum_count_eq]) hη).rec fun V H ↦
    ((relLength_mono le_rfl (T := ((cupOrthogonal ..).submoduleOf _).restrictScalars _) fun x y ↦ by
    simpa using! M x fun _ _ a _ ↦ H.2 _ a _ (hV · |>.1) _ y).trans (H.1.trans (mod_cast
    ?_))).trans_eq'
    (by rw [relLength_eq_length_map_mkQ, Submodule.map_top, Submodule.range_mkQ, length_top]; rfl)
  simp [← mul_sum, ← sum_mul]
  grw [← card_biUnion fun _ _ _ _ h ↦ disjoint_filter.2 fun _ _ a ↦ by simpa [a]
    using! (((isUnit_teichmuller_sub (Units.ext.mt h)).map (algebraMap ..)).map theta).ne_zero,
    card_le_univ, card_algHom_eq_finrank]; lia

/-- Tame types. Let j be a homeomorphism onto G_p, K tame on inertia (`Lift.IsTameType`),
κ = r²(N+1)², b + 6(W+η) + κ + 2 < p. For L of class (F, K(s⁻¹)) with jump sets in [−η, η] ∪ ε[b,
b+W], p^{3κ+150(η+W+1)} Z_f(L) is orthogonal to the class (F, K) with jump sets in the opposite
window.

Tame types: exponent independent of the ramification index. -/
lemma tame_types_exponent (hj : Surjective Γ.overGp.toGp) {F K} (hL : InClass F (K ·⁻¹) U' L) (hK :
  ∀ s, IsWeilPair (toGp s) 0 → IsTameType p r N (K s)) {η W b ε} (hU : ∀ g,
  IsInJumpWindow η (-ε) b W (U g) ∧ IsInJumpWindow η ε b W (U' g)) (hp : b + 6 * (W + η) +
  r ^ 2 * (N + 1) ^ 2 + 2 < p) : ∀ a ∈ crysCocycles L.ρ,
  (p : O) ^ (3 * (r ^ 2 * (N + 1) ^ 2) + 150 * (η + W + 1)) • a ∈ cupOrthogonal (InClass F K U) L :=
  (exists_tameChart hj ⟨_, r.factorial_pos⟩ (l.out.dvd_factorial.1.mt
  (by grind [le_self_pow])) (lcm_dvd fun _ ↦ Nat.pow_sub_one_dvd_pow_sub_one p ∘ And.elim
  Nat.dvd_factorial ∘ mem_Icc (b := r).1)).rec fun d he ↦ by
  obtain ⟨t, hm⟩ := d.isWeilPair_tameGen, show d.e ≤ p ^ r ^ 2 by
    grw [he, Nat.le_of_dvd _ (lcm_dvd_prod ..), prod_le_pow_card _ _ (p ^ r)] <;> simp_all
      [← pow_mul, sq, l.out.one_lt, le_add_right, pow_le_pow_iff_right₀, Nat.one_le_iff_ne_zero]
  let J := MulEquiv.ofBijective toGp ⟨ho.1.2, hj⟩
  have w (g : inertiaGroup ..) := isWeilPair_zero_iff.2 ((J.apply_symm_apply g.1).symm ▸ g.2)
  have A {K U} (hK : ∀ s, IsWeilPair (toGp s) 0 → IsTameType p r N (K s)) L (H : InClass F K ..) :
    InClass (O := O) _ ⊥ U L := ⟨.mono
    ((isAdmissible_comp_iff ..).1 ((H.isPotCrys.comp _).isCrystalline_of_inertia_fixes fun s u ↦ by
    simpa [linearFrob, Dpcris, ← map_nearOne _ ho.1.2 (@OverGp.isOpen_range d.Γ' ..)] using!
      (isLocalGalois_padic.tame_inertia isUniformiser_ell
      (valuation_natCast_eq_one d.tame) d.varpi_pow_eq ⟨⟨(linearFrob _ · 0) ∘ _, by simpa using
      (linearFrob_pow H.isPotCrys t 0)⟩, by simp [linearFrob_mul H.isPotCrys (w _) (w _)]⟩
      (Subgroup.isOpen_of_mem_nhds _ ((nhds _).3 (continuous_subtype_val.tendsto 1
      (mem_comap'.1 H.isPotCrys.eventually_linearFrob_eq_one)) fun g ↦ (· (J.right_inv _) (w g))))
      fun g ↦ by simpa [he] using (H.2.2 _ _ (hK _ (w g)).1 (w g)).2).1 (x :=
      ⟨J s, isWeilPair_zero_iff.1 u⟩) (d.apply_varpi s))) (sup_le nearOne_le le_rfl), H.2.1, nofun⟩
  obtain ⟨⟨-, q, m, n, k⟩, -, q', m', n', k'⟩ := hK _ t, hK _ t.inv
  refine (d.1.mem_cupOrthogonal_of_scaledCupBounds ⟨1, by simp⟩ ho le_rfl (A hK) (A (hK ·⁻¹ ·.inv) _
    hL) _ ⟨·, ·⟩ fun S hY h c ↦ (exists_isKilledBy_tateDual_tensor hY hL t.inv m' m k' ?_).rec fun _
    ⟨M, u, v⟩ ↦ h.scaledCupBounds_of_killsCokernel (fun _ ↦ ⟨d.killsCokernel_of_isKilledBy ?_ ?_ M
    hm hp (by grw [u, n, n']; lia), d.killsCokernel_of_isKilledBy ?_ ?_ m hm hp ?_,
    d.killsCokernel_of_isKilledBy ?_ ?_ m' hm hp ?_⟩) ?_ (fun _ ↦
    (?_ : IsInJumpWindow η (-ε) b W _ ∧ _)) ?_ ?_ c _) <;> (first | gcongr | simp_all [hY.2.2,
    hL.2.2, KummerChart.differentExp, ↓padicValNat.eq_zero_of_not_dvd d.tame]) <;> clear * - hp n n'
    hU <;> grind [NoMultipleNear, → Int.le_abs_of_dvd, KummerChart.letterJumps]
