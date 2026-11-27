/- GID: D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/GreenbergWilesBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/GreenbergWilesBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.GreenbergWiles.GreenbergWilesBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/GreenbergWiles/GreenbergWilesBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles.ProjectiveCount
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Greenberg–Wiles formula, as a lower bound for the dual side. Only this lower bound
is proved, under a hypothesis of a central element acting without fixed vectors. The dual Selmer
group is replaced by relations among values on tame inertia at auxiliary split primes, and no local
duality is used. Source: H. Darmon, F. Diamond, R. Taylor, Fermat's Last Theorem (1995; 2007 text),
Thm 2.18–2.19; A. Wiles, Ann. of Math. 141 (1995), Prop. 1.6; J. S. Milne, Arithmetic Duality
Theorems, I 4.10, 5.1; L. Washington, Galois cohomology (1997), Thm 2.

This file: Bound on trivialised cocycles when a central element acts without fixed vectors. -/

open NumberField Function Set Classical Nat DiscreteModule trivialisedCocycles Quotient Subgroup
  commutatorElement Fint
attribute [local simp] commutatorElement_def funext_iff add_smul

/-- Let K be totally complex, s auxiliary primes for l^r (r ≠ 0), N and U (`SplitPlaces`),
indexed by ι, with
Frobenii φ_i; V finite, l^r-torsion, U-fixed; z central modulo U, fixing l-power roots of unity,
z − 1 onto V. If U fixes each l^r-th root, fixed by all φ_i, of a U-fixed N-unit, the trivialised
cocycles unramified outside N and s are finite in number, at most (#V)^{#ι+1}.

Known result: Greenberg–Wiles formula, as a lower bound for the dual side. -/
lemma SplitPlaces.hasFewCocycles_of_central {K R ι} [Field K] [EmbeddedNumberField K] [CommRing R]
  {l r N : ℕ} [Fact l.Prime] [NeZero N] {I} {V : DiscreteModule R Gal(Ω/K)} [Fintype ι]
  [IsTotallyComplex K] {U} (s : SplitPlaces (l ^ r) N I U ι) (h : r
  ≠ 0) {z} (c : V.FiniteKilledFixedInj (l ^ r) U z 1) (o : cycChar Ω l z = 1) (w : ∀ g, ⁅z, g⁆ ∈ U)
  (d : s.FrobeniiDetectRoots) : V.HasFewCocycles (PlaceAboveS N) I (Fintype.card ι + 1) := by
  obtain ⟨j, P, f, b, q⟩ := dvd_pow_self l h, exists_open_sylow l U
  obtain ⟨e, B, r, n, i⟩ : (cycCharMod Ω l z).1 = (1 : ℕ) ∧ ∃ B ≥ P, (P.1.subgroupOf B).Normal ∧
    z ∈ B := ⟨cycCharMod_eq_of_dvd j (by simp [cycCharMod_prime_pow_eq, o]),
    ⟨_, isOpen_mono le_normalizer P.2⟩, le_normalizer,
    inferInstance, (w · |> f |> mul_mem_cancel_left |>.symm.trans (by simp))⟩
  replace d {y} i k g a := (by simp [IsFixedPt]; grind : _ → IsFixedPt (unitsRep g) (unitsRep z y -
    1 • y)) congr(unitsRep (z * g) $(d y (j.choose_spec ▸ mul_nsmul y .. ▸ nsmul_mem i _) k _ (w (g
    * z)⁻¹)) + $(cycCharMod_eq_iff_unitsRep.1 e
    ((map_nsmul (unitsRep g - 1) l y).symm.trans (sub_eq_zero.2 a))))
  let S := { s with dvd_level := j.trans s.dvd_level, cyc_eq_one :=
    (cycCharMod_eq_one_of_dvd j ∘ s.cyc_eq_one ·) }
  obtain ⟨⟨Z, _, p⟩, F, b, u⟩ :=
    exists_permModule_isHigmanProjective R l ⟨U.1.comap _ (by fun_prop), U.2.subgroupOf B⟩
    (z := ⟨z, i⟩) (w ·), f.trans r, coprime_mul_iff_right.1 (relIndex_mul_index r ▸ b)
  have hn Q u m {W} := (card_trivialised_of_isHigmanProjective (R := R) (V := W) (z :=
    ⟨z, i⟩) (S.liftToSubgroup B Q F u m (update out ⟦1⟧ 1)
    (by clear * -; grind [out_eq'])) · · fun y x o ↦ (d ⟨x.1, fun g ↦ x.2 ⟨⟨g, F g.2⟩, u g.2⟩⟩
    (by simpa [liftToSubgroup] using! o ⟨·, ⟦1⟧⟩) · (x.2 _)))
  have le := id @devissage_induction l.pow_one (P.1.subgroupOf B) (U.1.1.subgroupOf B) (q ·) (fun V
    _ t ↦ (hn ⟨⟨_, P.2.preimage_val⟩,
    n⟩ (@f ·) (by simpa [← Units.val_eq_one] using! S.cyc_eq_one _ <| q · · |>.choose_spec) t
    (t.isHigmanProjective_of_coprime b)).1) fun s _ ↦ (card_le_of_isShortExact s · · |>.1)
  have X {A V C ι π} (s : IsShortExact ι π) c := (((FiniteKilledFixedInj.of_isShortExact (B :=
    V) s c).imp (le A) (le C)).elim (card_le_of_isShortExact s)).2
  refine devissage_induction rfl U _ (by tauto) (fun _ _ t ↦ mem_of_eq_of_mem (cast_injective
    (eq_of_div_eq_one (IsMultiplicative.eq_one_of_isHigmanProjective R l U (fun A _ ↦ Nat.card
    (A.trivialisedCocycles ..) / (Nat.card A ^ _ :)) w (@fun _ V _ _ π o k ↦ ?_) t fun t@⟨_,
    _⟩ H ↦ by simp [S.card_trivialised_of_isHigmanProjective t H fun y x ↦ (d x · · (x.2 _)), *])))
    ⟨by simp [t.1], le_rfl⟩) (fun s _ ↦ (card_le_of_isShortExact s · · |>.1)) V c
  have T (c : (V.restrictTo B).FiniteKilledFixedInj .. := k.imp_right (by tauto)) (k := p c (_ ⧸
    Z)) := let ι : Hom _ _ := ⟨.const .., by tauto⟩; X (o.restrictAlong _) c (X ⟨const_injective,
    ι.1.exact_map_mkQ_range,
      (isShortExact_submodule _ _ ι.range.2).2.2⟩ k.1 ((hn _ le_rfl (S.cyc_eq_one ·) k.1 (k.2
    (Pi.single 1 1) (by simp [inv_mul_eq_one]))).2 e (isTotallyComplex_of_algebra K _)).ge).2
  simp [mul_pow, o.card_eq_mul, mul_div_mul_comm, card_eq_of_isShortExact _ I o,
    (map _ I π).range_eq_top.2 fun witness ↦ by
    obtain ⟨⟨a, x⟩, _, p⟩ := witness
    obtain ⟨⟨q, v⟩, e⟩ := T.1.ge (mem_univ ⟨(a, (x ·)), by fun_prop, by tauto⟩)
    obtain ⟨m, _⟩ := o.2.2 (∑ g : _ ⧸ B.1, x g.out)
    obtain ⟨_, n, E⟩ := u.isCoprime
    exact ⟨⟨_, zsmul_mem (sub_mem (corestrict_mem B
    (s.mem_and_conj_mem · · |>.imp_left (F ·)) v) (y := (fun _ ↦ m, _)) ⟨(coboundary _ m).2.1, by
    simp +contextual [k.2.2.1 _ (s.mem_and_conj_mem ..).1]⟩) n⟩, (fun (P : trivialisedCocycles ..)
    (e : P.1.1 = a) ↦ show P = _ by
      ext g; simp [*]; simpa [*] using (P.2.2.1 g ofNonempty).symm) _
    (by simpa [trivialisedCocycles.map, π.isIntertwining, (k.of_isShortExact o).2.2,
    (congr($e.1.1 _) : π _ = _), *, index, mul_smul] using congr($E • a))⟩]
