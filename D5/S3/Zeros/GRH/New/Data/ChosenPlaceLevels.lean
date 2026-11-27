/- GID: D5/S3/Zeros/GRH/New/Data/ChosenPlaceLevels
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Data/ChosenPlaceLevels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Data.ChosenPlaceLevels. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Data/ChosenPlaceLevels.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel.NeatLevel
import D5.S3.Zeros.GRH.New.Seesaw.IndexTypes
import D5.S3.Zeros.GRH.Lib.SiegelWeil.Formula.SiegelWeilFormula
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Chosen places above g, the integer `Data.chosenGroupOrder`, principal level, trivial
stabilisers, sizes. -/

noncomputable section

variable {P} {D : Data P} (i : Fin 2) {w : FinPlace D.E} {n : Type} [Fintype n] {K :
  Subgroup (Gf D.E n)}

namespace Data

/-- A chosen bijection from the infinite places of E to the chosen places above g_i. -/
def chosenEquiv : D.Φ ≃ D.ChosenPlace i :=
  (Parameters.nonempty_infinitePlace_equiv_finPlace (g_modEq_one ..) D.exists_cofactor).some

/-- For each i ∈ {0, 1}, the number of chosen places of E above g_i equals f, the number of
infinite places of E. -/
lemma card_chosenPlace : Fintype.card (D.ChosenPlace i) = D.f :=
  (Fintype.card_congr (D.chosenEquiv i)).symm

lemma v_N_eq_exp_neg_one (h : ↑D.N ∈ w.1) : Valued.v (D.N : LocField w) = .exp (-1) := by
  simp [← Parameters.intValuation_p h (Parameters.not_dvd_N₁_mul_d_of_modEq_one D.N_modEq_one),
    ← v_algebraMap_eq_intValuation]

lemma intValuation_pi (h : D.π ∈ w.1) : w.intValuation D.π = .exp (-1) :=
  Parameters.intValuation_eq_of_mul_star D.N_modEq_one
  (D.π_mul_star ▸ w.1.mul_mem_right _ h) ⟨1, by simp [π_mul_star]⟩ h

/-- The product, over the chosen places w of E (those above g₀ and those above g₁), of the
orders of the groups GL_{rt}(𝔽_w), 𝔽_w the residue field. -/
def chosenGroupOrder := Nat.card (∀ x, GL (Fin (D.r * D.t)) (ResField (D.chosen x))) deriving NeZero

lemma prod_q_chosenPlace : ∏ x, (D.chosen x).q = D.gProd ^ D.f := by simp [chosen,
  Fintype.prod_sigma, D.q_eq_g (_ : D.ChosenPlace _).2.2, card_chosenPlace, gProd, mul_pow]

/-- The principal congruence subgroup of level `Data.piGBar` (1 at the chosen places) in the
finite adelic unitary group of rank
n. -/
abbrev chosenLevel := levelOf (n := n) D.chosen ⊥

lemma isChosen_star_iff {i} : ↑(D.g i) ∈ w.1 → (D.IsChosen (star w) ↔ ¬D.IsChosen w) :=
    (Parameters.star_mem_iff (g_modEq_one ..) · D.exists_cofactor)

/-- For a finite index set n with at most rt elements, the order of ∏_w GL_n(𝔽_w), over the
chosen places w above g₀ and g₁, divides `Data.chosenGroupOrder`. -/
lemma card_GL_dvd_chosenGroupOrder (h : Fintype.card n ≤ D.r * D.t) :
  .card (∀ x, GL n (ResField (D.chosen x))) ∣ D.chosenGroupOrder :=
  Subgroup.card_dvd_of_injective (.piMap fun _ ↦ extendGL (Function.Embedding.nonempty_of_card_le
  (by simpa)).some) (by simp [Function.Injective, funext_iff]; grind [extendGL_spec, Units.ext])

instance isConjApart_chosen : IsConjApart D.chosen := ⟨by grind [g_injective, q_eq_g, chosen,
  Function.Injective], fun i ↦ by grind [D.isChosen_star_iff i.2.2.2, chosen, IsChosen]⟩

lemma range_chosen : .range D.chosen =
  {w | D.IsChosen w} := by ext; rw [Set.mem_ofPred, isChosen_iff]; aesop

lemma principalLevel_le_chosenLevel {a} (h : D.piGBar ∣ a) : principalLevel n a ≤ D.chosenLevel :=
  principalLevel_le_levelOf (Ideal.mem_of_dvd _ h ·.2.2.1)

/-- If n has at most 2𝗇_m elements, every subgroup K of the level `Data.chosenLevel` is a free level
for I_n: the stabiliser of each point gK in the rational unitary group is trivial. -/
lemma classAut_eq_bot_of_le_chosenLevel (hK : K ≤ chosenLevel) (h : Fintype.card n ≤ 2 * D.n D.m) :
  ∀ g, classAut stdRatPoints K g = ⊥ := classAut_eq_bot D.isConjApart_chosen.1
  (by grw [prod_q_chosenPlace, h, finrank_eq_two_mul_card_infinitePlace,
  pow_mul]; gcongr; use D.nat_lt_of_hasLogBound) hK

/-- Minkowski's lemma: for the standard definite hermitian space of rank at most 2n_m, a
subgroup K of the stabiliser of the standard lattice and any finite adelic g, the stabiliser
of gK in the rational unitary group has order dividing `Data.chosenGroupOrder`. -/
lemma card_classAut_dvd_chosenGroupOrder (hn : Fintype.card n ≤ 2 * D.n D.m) (hK : K ≤ Kf _ n) g :
    .card (classAut stdRatPoints K g) ∣ D.chosenGroupOrder := .trans (Subgroup.card_dvd_of_injective
  ((Kf.reduceFamily _).comp (.comp (.subgroupComap ..) (Subgroup.inclusion fun _ ↦ (hK ·.2))))
  ((injective_iff_map_eq_one _).2 (Subtype.ext <| (D.classAut_eq_bot_of_le_chosenLevel le_rfl hn
  _).le ⟨·.2.1, _, ·, rfl⟩))) (D.card_GL_dvd_chosenGroupOrder (hn.trans D.nat_le_of_hasLogBound))

lemma IsChosen.not_star : D.IsChosen w →
  ¬D.IsChosen (star w) := by grind [isChosen_iff, isChosen_star_iff]

/-- For an integer n with 0 < |n| ≤ 8m and a finite place w of E, the residue character ω_w^n is
non-trivial if and only if w is a chosen place (`Data.IsChosen`). -/
lemma omega_zpow_ne_one (n : ℤ) (h : n ≠ 0 ∧ n.natAbs ≤ 8 * D.m := by omega) w : (D.ω ^ n) w ≠ 1 ↔
  D.IsChosen w := by
  by_cases D.IsChosen w <;> simp [*, ← orderOf_dvd_iff_zpow_eq_one, orderOf_ω, Int.natCast_dvd]
  use Nat.not_dvd_of_pos_of_lt (by lia) (h.2.trans_lt D.nat_lt_of_hasLogBound) ∘
    Parameters.N₁_mul_d_dvd_M_omega.trans

instance : D.HasLogUpper (P.Mω D.s) (D.logB / 9) :=
  Parameters.Mω.eq_1 .. ▸ .of_mem_Icc (a := by simpa using D.le_of_hasLogBound)

instance : D.HasLogUpper (.log D.chosenGroupOrder) (32 * D.logX) := ⟨by
  simp; grw [chosenGroupOrder, Nat.card_pi, card_GL_le _] <;> simp [card_ResField, Finset.prod_pow,
    prod_q_chosenPlace, Finset.prod_pos]
  use D.le_of_hasLogBound⟩
