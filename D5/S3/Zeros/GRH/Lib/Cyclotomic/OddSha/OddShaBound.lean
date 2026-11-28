/- GID: D5/S3/Zeros/GRH/Lib/Cyclotomic/OddSha/OddShaBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Cyclotomic/OddSha/OddShaBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Cyclotomic.OddSha.OddShaBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Cyclotomic/OddSha/OddShaBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cyclotomic.Kolyvagin.ComponentBound
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Bound for the odd part of a twisted Tate–Shafarevich group of an abelian CM field.
Only an upper bound is proved here, without the main conjecture, and small primes are handled by a
crude count of ray class group generators. One non-zero integer, at most an explicit quantity times
the class number, bounds the lengths at all primes including 2. Source: B. Mazur, A. Wiles, Class
fields of abelian extensions of Q, Invent. Math. 76 (1984); C. Greither, Ann. Inst. Fourier 42
(1992), Thm 3.2.

This file: Ray class group generators detect cocycles unramified off l; crude count by Minkowski.
One non-zero integer, at most an explicit quantity times the class number, bounds lengths of odd
Tate-twisted Sha groups at all primes. -/

open Function Ideal NeZero IsCyclotomicExtension.Rat IsDedekindDomain.HeightOneSpectrum

/-- For E ⊆ ℚ(ζ_N) and l prime, some finite s ⊆ G_E, with #s ≤ y²⁰ whenever N ≤ y and l ≤ y²,
detects the locally constant O/lⁿ(−e)-valued cocycles unramified off l, for all n, e and O
with `PadicIntegerRing` O l. -/
lemma exists_detecting_points_cocycles {N E} [NeZero N] [Field E] [EmbeddedNumberField E] (h : ∀ x,
  algebraMap E Ω x ∈ cycloField N) l [ThePrime l] : ∃ s : Finset _, (∀ y, N ≤ y → l ≤ y ^ 2 →
  s.card ≤ y ^ 20) ∧ ∀ {O} [CommRing O] [PadicIntegerRing O l] {n e}, ∀ z ∈ selmerModule (tateTwist
  l E O e) (placesDividing E l) ∅ (QuotSpan (l ^ n : O)), (∀ g ∈ s, z g = 0) → z = 0 := by
  set M := N * l ^ 2 with hM
  let r (g : cycloGalGroup M) :=
    {g.1 with commutes' := (h · ⟨_, cycCharMod_eq_one_of_dvd ⟨_, hM⟩ g.2⟩)}
  let f := cycCharMod (Γ := Gal(Ω/E)) Ω M
  have : 2 < M := by nlinarith [pos N, (Fact.out : 1 < l)]
  obtain ⟨⟨i, j⟩, _⟩ := index_pow_at_places_le M (placesDividing (cycloField M) l),
    isTotallyComplex (cycloField M) this
  choose ι _ b m hm hh H using exists_detecting_points_hom (cycloGalGroup M) _ M i
  refine ⟨.image (Sum.elim (invFun f) (r ∘ b)) .univ, fun y a c ↦ Finset.card_image_le.trans ?_,
    @fun O _ _ n _ z s t ↦
    (fun k (h : l ^ k • z = 0) ↦ ?_) n (funext₂ (by simp [↓nsmul_quot_eq_zero]))⟩
  · have d {p : Ideal ℤ} [p.IsMaximal] (h : p ≠ ⊥) : (IsDedekindDomain.primesOverFinset p
        (NumberField.RingOfIntegers (cycloField M))).card ≤ Module.finrank ℚ (cycloField M) := by
      rw [← NumberField.RingOfIntegers.rank, ← sum_ramification_inertia_eq_finrank p,
        ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset h, ← Nat.card_coe_set_eq,
        Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
      exact Finset.sum_le_sum fun q _ ↦ mul_pos (ramificationIdx_pos ..) (inertiaDeg_pos ..)
    apply Nat.le_of_dvd at hh
    grw [classNumber_le, j, natAbs_discr M, Nat.div_le_self, M.lt_two_pow_self.le, ← hm,
      Set.ncard_congr' (.trans (.subtypeEquivRight (by simp [placesDividing]))
      (equivPrimesOver _ (p := span {(l : ℤ)}) _)), ← IsDedekindDomain.coe_primesOverFinset] at hh
    simp [← pow_mul, ← pow_add, pow_le_pow_iff_right₀] at *
    grw [d, finrank M, Nat.totient_le, hM, a, c] at *
    nlinarith [Nat.zero_le (y ^ 15)]
    all_goals first | omega | simp [ne, NumberField.classNumber, Ne.pos, i]
  induction' k with _ ih generalizing z <;> ext1 g; simp [↓← h]
  replace h := ih _ (nsmul_mem s M) (by simp [t · ·]) (by grind)
  obtain ⟨A, u, -, c⟩ := (mem_selmerModule_iff.1 s).imp_left fun m x y ↦ (m (r x) y).trans (congrArg
    _ (by simpa [cycPowDirichlet, tateTwist, -map_inv] using! (cycPowDirichlet_smul_eq_self (O :=
    O) (ψ := 1) (cycCharMod_eq_one_of_dvd (one_mul M).dvd x⁻¹.2) congr($h y)).1))
  erw [← div_mul_cancel g, A ⟨(g / _).restrictScalars _, f.div_mem_ker_iff.2 _⟩, t (invFun f (f g)),
    congrFun ((@H _ _ (z <| r ·) (c.comp_continuous (continuous_of_equivariant_emb 1)) (A · <| r ·)
    congr($h ∘ r) (FinPlace.isPlaceOver_placeOver · |> fun o k y a ↦ u (r y) (o.isPlaceOver_below
    (K := ℚ).exists_above.imp fun w ⟨p, _⟩ ↦ ⟨k ∘ o.valuation_natCast_lt_one_iff.1 ∘
    p.valuation_natCast_lt_one_iff.2, _, p, a⟩))).2 (by simp [t]))] <;> simp [invFun_eq]

open Nat DirichletCharacter Finset IsDiscreteValuationRing MulAut NumberField Pointwise

attribute [local simp] smul_sum classNumber_ne_zero cycInv mul_assoc smul_smul smul_sub tateTwist

/-- For a CM field E in ℚ(ζ_N), some integer 1 ≤ X ≤ 2^{4(N+t+3)^27}·h_E, h_E the class number,
has length of `shaOdd` in O/lⁿ(−e) at most v(X), for all primes l, 0 ≤ e < t, n,
and characteristic zero discrete valuation rings (O, v) over ℤ_l with all O/l^m finite,
containing a primitive root of unity of order the exponent of (ℤ/N)^×.

Known result: Bound for the odd part of a twisted Tate–Shafarevich group of an abelian CM field. -/
lemma exists_length_shaOdd_le N t [NeZero N] E [Field E] [NumberField E] [IsCMField E] [Algebra E Ω]
  (h : ∀ x, algebraMap E Ω x ∈ cycloField N) : ∃ X ≠ 0, X ≤ 2 ^ (4 * (N + t + 3) ^ 27) * classNumber
  E ∧ ∀ l [_L : ThePrime l] O [CommRing O] [PadicIntegerRing O l], HasEnoughRootsOfUnity O
  (Monoid.exponent (ZMod N)ˣ) → ∀ e < t, ∀ n, Module.length O (shaOdd l E O e n) ≤ addVal O X := by
  choose! X hX hk hS using exists_isStickelbergerBound N
  generalize hy : _ + 3 = y
  let Y e := 4 * φ N * (4 * X e * X e)
  use (Ioo 0 t).prod Y ^ y ^ 20 * classNumber E, by simp [Y, ne, prod_eq_zero_iff]; grind, by
    simp_rw [Y, ← mul_assoc]
    grw [hk, show _ + _ ≤ y by grind, (?_ : _ * 4 ≤ 2 ^ (2 * y ^ 6)), prod_const, card_Ioo,
      (?_ : _ - 1 ≤ y)] <;> ring_nf <;> grind [Nat.lt_two_pow_self, totient_le]
  introv _ _; obtain rfl | he := eq_or_ne e 0
  · choose _ _ _ _ _ d R using exists_detecting_points_hom Gal(Ω/E) ∅ 0 (by simp [iInf_of_isEmpty])
    refine .trans (And.elim (length_le_of_detecting_points (.funUnique ..)) (forall₂_and.1 fun z h ↦
      R ?_ ?_ ?_ ?_)) (addVal_le_iff_dvd.2 (d.trans (by simp)).natCast) <;> simp [shaOdd,
      mem_selmerModule_iff, shaLocalSet, inertiaAbove, placesDividing] at h <;> grind
      [FinPlace.isPlaceOver_placeOver, IsPlaceOver.valuation_natCast_lt_one_iff]
  let ι := MulSemiringAction.toAlgAut Gal(Ω/E) ℚ Ω
  obtain ⟨hS, ⟨j, -⟩, hN, hE, p, hp, H⟩ := hS e he, isClosedEmbedding_galois_restrict ι, (fun g k ↦
      ⟨⟨_, g.2, g.3, (h · ⟨g, k⟩)⟩, rfl⟩ : _ ≤ ι.range), (by tauto : cycChar Ω l = (cycChar Ω
    l).comp ι ∧ ∀ g, ι (conjGal g) = cmConj * ι g * cmConj), exists_detecting_points_cocycles h l
  choose S hs using cycCharMod_surjective N
  let s := (S · / S 1)
  choose b hb using fun u g ↦ hN («conj» u («conj» cmConj g * g⁻¹)) (by simp [mul_left_comm])
  choose hZ hΦ using fun {x} (m : x ∈ shaOdd l E O e n) ↦ have a := mem_selmerModule_iff.1 m.2
    have hA u g k w (e : ι (b u g * k) = ι w := by simp [*]) : x (b u g) = x w - x k := by
      simp [*, ← j.1.2 e]
    let T ψ u g := (cycPowDirichlet (N := N) l e ψ u).1 • x (b u g) ()
    let z ψ := ∑ t, T ψ (s t)
    have hZ ψ : z ψ ∈ component l e ψ _ := ⟨_root_.sum_mem fun _ _ ↦ .comp (m.2.2.comp_continuous
      (by simp [j.continuous_iff, Function.comp_def, *]; fun_prop)) (_ • · _), fun g k ↦ by
      have hT {v} w (h : w / v ∈ cycloGalGroup N) : T ψ w k = T ψ v k := by
        obtain ⟨u, rfl⟩ := by simpa [eq_div_iff_mul_eq'] using hN _ h
        simp_all [T, cycPowDirichlet, hA v k u⁻¹ (u⁻¹ * b (ι u * v) k)]; ring_nf
      simp [z, T, mul_left_comm,
        ← Fintype.sum_equiv (.mulRight (cycCharMod Ω N g)) _ (fun t ↦ T ψ (s t)
        k) fun t ↦ hT (s t * g) (by simp [s, *]), fun u ↦ hA u g (b (u * g) k) (b u (g * k))], by
      rintro g (_|⟨h, d⟩); simp [z, T, *, hA _ cmConj 1 1]
      choose w e using fun u ↦ hN («conj» u g) (by simpa)
      have k u : x (w u) = 0 := d.rec (fun ⟨_, p, _, n, i⟩ ↦ a.2.1 _ ((n.smul u).exists_above.imp
        fun _ ⟨b, o⟩ ↦ ⟨by simpa [← o, placesDividing] using p, _, b, (e u).symm.subst (i.conj u)⟩))
        fun ⟨A, p, i, a⟩ ↦ m.1.1 _ ⟨u • A, by simpa using (val_smul_lt_one u).2 p, ite_eq_right he ▸
        ⟨(e u).symm.subst (conj_mem_decompGroup_smul i), by simp [*]⟩⟩
      simp [z, T, *, fun t ↦ hA t g (w t) (w (t * cmConj))]⟩; And.intro hZ
    fun (h : ∀ ψ, cycPowDirichlet l e ψ cmConj = -1 → z ψ = 0) g () ↦ show (4 * φ N) • x g () = 0 by
      have := mul_eq_one_iff_inv_eq.1 isComplexConj_cmConj.mul_self
      linear_combination (norm :=
        (simp [sum_characters_eq, cast_smul_eq_nsmul, z, T, s, *, cycPowDirichlet,
       ← sum_smul, ← mul_sum, sum_comm, -hE, fun g ↦ hA 1 (ι g) g (conjGal g)]; ring))
       Fintype.sum_congr (z · (ι (conjGal g))) (z · (ι g)) (fun ψ ↦ by
       cases (cycPowDirichlet l e ψ cmConj).inv_eq_self_iff.1 (by grind) <;> simp [(hZ
         ψ).2.symm, *]) + 2 * φ N * congrFun₂ ((Submodule.mem_iInf _).1 m.1.2 he) g ()
  by_contra C; have K {ι} [Fintype ι] (p : ι → _) c H :=
    C (.trans (length_le_of_detecting_points (.funUnique ..)
    (fun z h i ↦ (mul_smul ..).trans (funext (hΦ (nsmul_mem h _) (fun ψ k ↦ by simpa [funext_iff]
    using (nsmul_component_eq_zero hS k he (hZ h _))) (p i)))) H) (addVal_le_iff_dvd.2 (prod_const
    (Y e) ▸ (pow_dvd_pow_of_dvd_of_le (dvd_prod_of_mem Y (by grind)) c).mul_right _).natCast))
  have := mt (Fintype.card_coe p ▸ hp y (by omega)) (K (↑) · (H · ·.2 ∘ Subtype.forall.1))
  choose! γ hγ using (exists_detecting_points_component (O :=
    O) (ψ := ·) hS · he (hX e he) (by nlinarith))
  refine K (fun (t, ψ, i) ↦ b (s t) (γ ψ i)) ?_ fun z h k ↦ (nsmul_eq_zero_iff_of_coprime (.pow_left
    n (coprime_of_lt_prime out ?_ _L.out))).1 ⟨funext₂ ?_, funext₂ (hΦ h (hγ · · _ (hZ h _) ?_))⟩
  simp [by simpa using sum_characters_eq O (n := N) 1]; grw [(?_ : φ _ ≤ y),
    factorization_le_of_le_pow ((hk _ he).trans ?_), add_one_le_of_lt (?_ : y ^ 6 < y ^ 18)]
  all_goals (try gcongr) <;> first | nlinarith [N.totient_le] | simp [↓nsmul_quot_eq_zero, k (_, _,
    _)]
