/- GID: D5/S3/Zeros/GRH/New/Lift/FewLowJumps
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Lift/FewLowJumps
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Lift.FewLowJumps. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Lift/FewLowJumps.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Lift.LongGap
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Length bound for crystalline classes with few low weights (see
New.Lift.ExponentTheorems).

This file: Colength bound for constants lifting to deep points; cup products vanish on that
submodule. -/

open Int Finset Submodule Lift.KummerChart JumpLattice

namespace Lift.KummerChart.PairingSide

attribute [-instance] NormedAlgebra.toAlgebra

variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} (S : PairingSide O) (i :
  Letter)

/-- The images in W(C^♭) ⊗ C of the x in `Lift.KummerChart.PairingSide.deepElements` i c that lie at
the letter i with exponents t − u at E and −u at φ^a E, a ≥ 1. -/
noncomputable def deepConstants t c :=
  (locKisinPart (withExponents i (raisedAtE t)) ⊓ S.deepElements i c).map S.projTrivLoc

attribute [local grind =] stepBack_zero

variable {S : PairingSide O} {i : Letter} {c : ℕ → ℤ → ℤ} (c' : ℕ → ℤ → ℤ) (hk : IsUnramified)
  (hp : 5 ≤ p) {a η W : ℕ} {b n r : _ → ℕ} {ε : _ → _} (ha : ∀ i, b i + W + η ≤ (p - 3) * a) (hb :
  ∀ i, 6 * (a + η + W) < b i) (hs : ∀ i, NoMultipleNear p (6 * (a + η + W)) (b i)) (hU : ∀ i,
  IsInJumpWindow η (ε i) (b i) W (S.U i)) (hn : ∀ i, ∑ u ∈ Icc (-↑η) ↑η,
  k.f * S.jumpMultiplicity i u ≤ n i) (hr : ∀ i, ∑ u ∈ S.U i, k.f * S.jumpMultiplicity i u ≤ r i)

include hk hn hr in
/-- Unramified chart: raising the depth from c ≥ −u to c' at φ^a E only (c'_a antitone, no
multiple of p in any (c_0(v), c_0(v)+p^a), cost ≤ A per line, plus B if |u| ≤ η) shrinks
`Lift.KummerChart.PairingSide.deepConstants` by length ≤ A·r + B·n. -/
lemma relLength_deepConstants_le {i'} a A B (f : i.stepBack a = i') (ha : ∀ v, ∀ n ∈ Ioo (c 0 v) (c
  0 v + p ^ a), ¬↑p ∣ n) (hc : ∀ b, ∀ u ∈ S.U (i.stepBack b), -u ≤ c b u ∧ (b ≠ a → c' b u ≤ c b u))
  (ho : AntitoneOn (c' a) (S.U i')) (hA : ∀ u ∈ S.U i', ∑ n ∈ Ico (c a u) (c' a u), cost a n ≤ A +
  ite (u ∈ Icc (-↑η) ↑η) B 0) : relLength (S.deepConstants i 0 c) (S.deepConstants i 0 c') ≤
  ↑(A * r i' + B * n i') := by
  replace hA := sum_le_sum fun u m ↦ mul_le_mul_left (hA u m) (k.f * S.jumpMultiplicity i' u)
  simp [add_mul, -mem_Icc, sum_mul, sum_sigma'] at hA
  grw [← mul_sum, hr, ← mul_sum, inter_subset_right, hn] at hA
  grw [← hA]
  clear hA
  induction' E : (S.U i').sigma fun u ↦ Ico (c a u) (c' a u) using eraseInduction with I ih
    generalizing c
  subst E
  obtain w | ⟨u, hu⟩ := by
    simpa using not_or_of_imp (exists_min_image {v ∈ S.U i' | c a v < c' a v} id)
  exact (relLength_eq_zero.2 (map_mono fun _ ↦
    And.imp id (.imp id (mem_withExponents_of_le <| · ·)))).trans_le bot_le
  have M : locKisinPart (S.kerWithExponents i c) ≤ locKisinPart
    (S.extLattice.withExponents i (raisedAtE 0)) := fun _ ↦ (mem_withExponents_of_le ·.1)
  grw [← add_sum_erase (a := ⟨u, c a u⟩), relLength_trans _ (ih (c := raiseExponent c a u) ..)]
  grw [deepConstants, deepConstants, ← relLength_comap, comap_map_eq, relLength_mono le_rfl
    (sup_le_sup_left (fun _ ↦ (·.2) : locKisinPart (S.kerWithExponents i c) ≤ _) _),
    relLength_le_of_relations] <;> intro x hx
  refine (S.exists_reaches_deep {⟨a, c a u⟩}).rec fun A ⟨R, d⟩ ↦
    mem_sup.2 ⟨_, ⟨R.mem_of_stable M hx.1 hx.2, d hx.2 _ ?_⟩, _, neg_mem (R hx.2), by simp⟩
  swap
  choose x' n m b e using (mem_sup.1 <| hx · |>.2)
  choose y d q B using (exists_inclKer_eq_of_projTriv_eq_zero <| b ·)
  peel 3 exists_comb_of_jumpMultiplicity_le c hk .refl a i f
    (by clear * - hu ho; grind [AntitoneOn]) (⟨_, B · (m _).2⟩) d with b t
  obtain ⟨w, m, z, o, s⟩ := mem_sup.1 t
  have t := sum_smul_mem (t := univ) _ b fun l _ ↦ (hx l).1
  have m : ⟨_, S.inclKer.wittMap_mem_kisinLoc w.2⟩ ∈ locKisinPart (S.kerWithExponents i _) :=
    ⟨S.inclKer.map_mem_withExponents le_rfl m, by simp⟩
  have e : _ ∈ S.deepElements i (raiseExponent c a u) :=
    ⟨sub_mem (smul_mem _ ↑p t.2.1) (kerWithExponents_le_deepElements m).1, by
    simpa -implicitDefEqProofs [eq_sub_of_add_eq' s, smul_sum, smul_comm _ (b _), ← e, q, add_sub]
      using (invariantsMod _).add_mem (sum_smul_mem _ b fun l _ ↦
      (n l).2.2) (smul_sub_mem_withExponents (S.inclKer.map_mem_withExponents le_rfl o))⟩
  -- an operator of cost `0` moves `E M` into `E ^ p ^ a M ⊆ p M + M'`: apply it to `x`
  obtain ⟨A, R, d⟩ :=
    S.exists_reaches_deep (.image (.mk 0) ((S.U i).biUnion fun v ↦ Ioo (c 0 v) (c 0 v + p ^ a)))
  rw [sum_eq_zero] at R
  obtain ⟨y, z⟩ := R.mem_of_stable le_rfl m (kerWithExponents_le_deepElements m)
  have m₂ := frobEUnit_zpow_mem_withExponents (c' := c) 0 (-p ^ a)
    (mem_withExponents_of_deep y (d (kerWithExponents_le_deepElements m) (fun b v ↦ c b v +
    raisedAtE (p ^ a) b 0) ?_).2) fun _ v _ ↦ by clear * - ha; grind [ha v 0, dvd_zero]
  obtain ⟨r, f⟩ : ↑p ∣ k.frobE 0 ^ p ^ a - k.frobE a := by simpa [k.dvd_iff_coe_dvd, frobE_eq, hk.1,
    phi_pow_smul_z, ← sub_sub, dvd_sub_left] using sub_dvd_pow_sub_pow (k.z + p) k.z _
  have n := (locKisinPart (S.kerWithExponents i c)).sub_mem (x :=
    r • ⟨_, frobEUnit_zpow_smul_mem_kisinLoc.2 (A _).2⟩) ⟨smul_mem _ r.1 m₂, by
    simp [by simpa using z]⟩ (R t.2)
  refine mem_sup.2 ⟨_, ⟨sub_mem t.1 (M n), (sub_mem t.2 (kerWithExponents_le_deepElements
    n)).imp_right fun m g ↦ mem_withExponents_of_smul not_frobE_dvd_p (m g).1.1 ?_⟩, _, n, by simp⟩
  convert (invariantsMod _).add_mem (R.mem_of_stable kerWithExponents_le_deepElements e e).2
    (smul_sub_mem_withExponents (frobEUnit_zpow_mem_withExponents a 1 m₂)) g
  simp [S_smul, ← sub_eq_iff_comm.1 f, ← frobEUnit_pow_smul, ← zpow_natCast (k.frobEUnit 0),
    sub_smul, mul_smul, smul_sub, smul_comm g, Nat.cast_smul_eq_nsmul, -map_smul]
  abel
  all_goals clear * - hu ha hc hk; cases a <;> grind [cost_le_of_isUnramified]

include hk hp ha hb hs hU hn hr

/-- Unramified chart, p ≥ 5, jumps in the windows, p away from 0 and ±b_i: the constants at i
lifting to points of `kisinLoc` of the stated sign-dependent depth have colength ≤ (2a+1)n_i +
3(W+1)r_{i−1} + 6a·n_{i−1}; n, r bound f times the low and total jump counts. -/
lemma exists_relLength_deepConstants_le i : relLength (S.constantAt i).range
  (S.deepConstants i 0 (if ε i = 1 then raisedAtE (2 * a + η) else fun l u ↦
  if l = 1 then W + 1 - u + if |u| ≤ η then 2 * a else 0 else if l = 0 then b i + W + 2 * a else
  -u)) ≤ ↑((2 * a + 1) * n i + (3 * (W + 1) * r (i.stepBack 1) + 6 * a * n (i.stepBack 1))) := by
  have U (n : ℕ) : ∑ m ∈ Ico (0 : ℤ) (n + 1), cost 0 m = padicValNat p n.factorial := by
    induction n <;> simp_all [↓← insert_Ico_right_eq_Ico_add_one, add_nonneg, cost, IsUnramified,
      Nat.factorial, padicValNat.mul]; rfl
  have h₁ : ∀ t, -↑η ≤ t → t ≤ 0 → relLength (S.constantAt i).range (S.deepConstants i t
    (raisedAtE (2 * a + η))) ≤ ↑(a * ∑ u ∈ Ico (-↑η) t, k.f * S.jumpMultiplicity i u) := by
    have X s d m H : p ^ s • S.constantAt i d ∈ S.deepConstants i m (raisedAtE (2 * a + η)) :=
      (pointsOver_nonempty_of_noMultipleNear
      (pointsOver_nonempty_of_killsCokernel (killsCokernel_of_isUnramified
      s (a - s) (by grw [← le_add_tsub]; grind) hk hp) d) (hs i) _ (by grind)).rec fun x ⟨a, b, c,
      d⟩ ↦ ⟨⟨x, a⟩, ⟨mem_withExponents_of_le c H, by simp [b, nsmul_mem], d⟩, by simp [b, hk.2]⟩
    refine Int.leInduction (fun _ ↦ by simpa [IsConcreteLE.le_iff]
      using (X 0 · _ (by grind))) fun t ht ih h₀ ↦ ?_
    rw [← sum_Ico_add_eq_sum_Ico_add_one ht, mul_add]
    refine relLength_trans (ih (by lia))
      ((relLength_comap ..).ge.trans (relLength_le_of_relations _ (fun x ⟨_, ⟨d, e⟩, _⟩ ↦
      by simpa [e] using X a d _ (by clear * - h₀; simp; grind)) fun x l ↦ ?_))
    peel 3 exists_comb_of_jumpMultiplicity_le _ hk (sum_le_sum fun _ _ ↦
      jump_extension_le _ (by omega)) 0 i rfl (by simp [raisedAtE]) x (l · |>.1.1) with b m
    rw [sup_of_le_right fun _ e ↦ mem_withExponents_of_le e (by clear * -; grind)] at m
    exact ⟨_, (sum_smul_mem _ b fun j _ ↦ (l j).1.2).rec fun x s ↦
      ⟨mem_withExponents_of_le (mem_withExponents_of_deep m s) (by clear * - h₀; grind), x, s⟩, rfl⟩
  specialize h₁ 0 (by lia) le_rfl
  grw [Ico_subset_Icc_self, η.cast_nonneg, hn] at h₁
  split
  exact h₁.trans (mod_cast by lia)
  obtain ⟨q, h₀, -⟩ := existsUnique_add_zsmul_mem_Ico (natCast_pos.2 p.pos_of_neZero) 0
    (b i + W + 2 * a)
  simp [IsInJumpWindow] at hU h₀
  refine relLength_trans ((relLength_trans h₁ (relLength_deepConstants_le (fun l u ↦
    raisedAtE (q * p + u) l u) hk hn hr 0 0 (a + 1)
    rfl ?_ ?_ ?_ fun u hu ↦ ?_)).trans (mod_cast ?_)) (relLength_deepConstants_le _ hk hn hr _ _ _
    rfl (fun _ n x ↦ (not_dvd_iff_lt_mul_succ _ ?_).2 ⟨q, ?_⟩) ?_ ?_ fun u hu ↦ (sum_le_card_nsmul _
    _ _ fun y e ↦ cost_le_of_isUnramified hk (hs (i.stepBack 1) y ?_)).trans ?_) <;> clear h₁
  any_goals grind [card_Ico, AntitoneOn]
  split
  exact (sum_le_sum_of_subset (by grind)).trans ((U (q * p).toNat).trans_le
    (le_of_mul_le_mul_left (by rw [sub_one_mul_padicValNat_factorial]; grind [tsub_mul]) (by lia)))
  exact sum_nonpos fun y e ↦ cost_le_of_isUnramified hk fun d ↦ hs i y (by
    grind [le_of_dvd (by grind) ((dvd_mul_left _ q).sub d)]) d

/-- Few low jumps (unramified chart, p ≥ 5, window and gap hypotheses; n_i, r_i bound f times
the low, all jumps at i): on a ℤ_p-submodule of C of colength ≤ 11Σ_i(n_i(a+1) + r_i(W+1)),
α(d) ∪-pairs to a coboundary with every α'(c) of paired sides with opposite windows. -/
lemma exists_scaledCupBounds_few_low_jumps (hη : 1 ≤ η) : ∃ V : Submodule ℤ_[p] _, relLength ⊤ V ≤
  ↑(11 * ∑ i, (n i * (a + 1) + r i * (W + 1))) ∧ ∀ T (P : SidePairing T S) c, (∀ i,
  IsInJumpWindow η (-ε i) (b i) W (T.U i)) → ∀ d ∈ V, P.ScaledCupBounds 0 c d := by
  refine ⟨_, (relLength_iInf_le ..).trans ((sum_le_sum fun i _ ↦ (relLength_comap ..).trans_le
    (map_top (S.constantAt i) ▸ exists_relLength_deepConstants_le hk hp ha hb hs hU hn hr
    i :)).trans (mod_cast by simp [← mul_sum, ← sum_mul, Equiv.sum_comp]; lia)), fun _ P c V d
    h ↦ P.scaledCupBounds_of_points_at_cuts (e' := 0) ⊤ (ε · = 1) 1 (by simp; tauto) (fun i _ ↦
    ((mem_iInf _).1 h i).rec fun x ⟨⟨s, _, t⟩, e⟩ ↦ ⟨⟨_, 0, pointsOver_nonempty_of_noMultipleNear
    (pointsOver_nonempty_of_killsCokernel (killsCokernel_of_isUnramified 0 a ?_ hk hp) c) (hs i)
    (raisedAtE (2 * a + η)) ?_, ⟨⟩, ?x⟩, ⟨_, 1, ⟨_, x.2, by simpa, mem_withExponents_of_deep
    s t, t⟩, ⟨⟩, ?y⟩, pointsOver_nonempty_of_noMultipleNear (pointsOver_nonempty_of_killsCokernel
    (killsCokernel_of_isUnramified 0 a ?_ hk hp) 1) (hs i) (raisedAtE a) ?_, ?_⟩) (by simp [hk.2])⟩
  case x | y => rintro (_ | _ | _) u _ v _ <;> obtain ⟨w, x, _, _, e | e⟩ := V _ _ ‹_›, hU _ _
                  ‹_›, hb (k.letterFrob.symm i), hb i, units_eq_one_or (ε i) <;> simp [e, raisedAtE,
    stdExponent, abs_le, ite_apply] at w x ⊢ <;> omega
  all_goals clear * - ha hb hU V hη; grind (splits := 15) [mem_image₂, Antitone]
