/- GID: D5/S3/Zeros/GRH/New/Seesaw/IndexTypes
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/IndexTypes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.IndexTypes. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/IndexTypes.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Trace.BadShare
import D5.S3.Zeros.GRH.New.Data.Weights
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Different generator and root discriminant lie between x^10 and x^12. Chosen places above
g, tame characters there, base characters and pairs for the data. Row parameter, level prime N and
its size, tame twists, characters of the lifts. Index types, signs, parameters, level group and good
idempotent for the proof's spaces. -/

noncomputable section

open Ideal Nat AutChar Finset Fint MulChar NeZero NumberField Parameters Polynomial

variable {P} (D : Data P) {w : FinPlace D.E} (a n j : ℕ) {S T α : Type}

namespace Data

instance hasLogBound_varpi (v : D.Φ) (u) :
  D.HasLogBound u (v (P.ϖ D.s)) (ite u 12 10 * D.logX) := by
  obtain ⟨hz, e⟩ := isPrimitiveRoot_zeta.map_of_injective v.embedding.injective,
    v.pos_iff.2 (P.relDifferentGen_ne_zero _)
  simp [↓infinitePlace_apply_varpi, ← v.norm_embedding_eq, ← eval_map_apply,
    ← expand_towerDeg_cyclotomic, ← derivative_map,
    derivative_expand, hz.norm'_eq_one out, pos, -norm_pos_iff] at *
  exact Real.exp_log e ▸ .of_mem_Icc (a := by grind [Data, c, single_le_sum,
            (mem_primitiveRoots one_le).2 (hz.pow one_le (mul_comm ..))])

/-- The root discriminant is the geometric mean of the `|ϖ|_v`, so lies in `[x¹⁰, x¹²]`. -/
instance hasLogBound_rootDisc (u) : D.HasLogBound u D.rootDisc (ite u 12 10 * D.logX) := have :=
    (D.hasLogBound_varpi · u |>.1); ⟨by split <;> apply le_of_pow_le_pow_left₀ (ne D.f) <;> simp_all
    [↓pow_abs, ↓← prod_varpi_eq_rootDiscr_pow, abs_prod,
    ← Finset.card_univ, ← prod_const, prod_le_prod₀, Real.exp_pos, rootDiscr_pos, le_of_lt]⟩

/-- The complex conjugate of the element piG ∈ 𝓞_K of norm g₀g₁, as an integer of E; the chosen
places are its prime divisors. -/
abbrev piGBar := star (algebraMap _ (𝓞 D.E) D.piG)

/-- The finite place w of E is chosen: it divides the complex conjugate of the element piG ∈ 𝓞_K of
norm g₀g₁. -/
def IsChosen (w : FinPlace D.E) := D.piGBar ∈ w.1

/-- The chosen places above the prime g_i: the finite places of E dividing both g_i and the complex
conjugate of the element piG ∈ 𝓞_K of norm g₀g₁. -/
protected abbrev ChosenPlace i := {w : FinPlace _ // D.piGBar ∈ w.1 ∧ ↑(D.g i) ∈ w.1}

lemma piGBar_mul_star : D.piGBar * star D.piGBar = D.gProd := by
  ext; simpa [gProd, map_star_CM, mul_comm] using! congr(algebraMap P.K D.E $D.norm_piG)

@[simp] lemma piG_ne_zero : D.piG ≠ 0 := (by simpa [·, ne] using D.norm_piG)

lemma piGBar_ne_zero : D.piGBar ≠ 0 := by simp

lemma exists_cofactor {i} : ∃ c : ℕ, D.piGBar * star D.piGBar = D.g i * c ∧ (D.g i).Coprime c :=
    ⟨D.g i.rev, by rw [piGBar_mul_star, gProd]; grind [coprime_primes, g_prime, g_injective]⟩

lemma isChosen_iff : D.IsChosen w ↔ ∃ i, D.IsChosen w ∧ ↑(D.g i) ∈ w.1 := by
  simpa using (w.2.2 <| mod_cast D.piGBar_mul_star ▸ mul_mem_right _ _ ·)

/-- If a finite place w of E lies above the prime g_i of the data, then its absolute norm equals
g_i; that is, w has residue degree one. -/
lemma q_eq_g {i} {w : FinPlace D.E} : ↑(D.g i) ∈ w.1 → w.q = D.g i :=
  q_eq_of_modEq_one (g_modEq_one ..)

lemma finite_isChosen :
  {w | D.IsChosen w}.Finite := by simp [IsChosen, ← dvd_span_singleton, finite_factors]

/-- At every chosen place w of E, the residue field has a complex multiplicative character of
order exactly M_ω², where M_ω = `Parameters.Mω`. -/
lemma exists_residue_char_of_order (h : D.IsChosen w) : ∃ T : MulChar (ResField w) ℂ, orderOf T =
  P.Mω D.s ^ 2 := exists_mulChar_orderOf _ (by grind [isChosen_iff, q_eq_g, dvd_g_sub_one,
  card_ResField, card_eq_fintype_card]) (Complex.isPrimitiveRoot_exp _ out)

/-- The family of residue characters ω_w: at a chosen place the M-th power of a fixed character
of order M², M = `Parameters.Mω`, and trivial elsewhere. -/
def ω w := if h : D.IsChosen w then (D.exists_residue_char_of_order h).choose ^ P.Mω D.s else 1

/-- At a chosen place w of E, the residue character ω_w has order exactly M_ω = (N₀d)^{s+6}. -/
lemma orderOf_ω (h : D.IsChosen w) : orderOf (D.ω w) = P.Mω D.s := by
  simp [ω, orderOf_pow, (exists_residue_char_of_order ..).choose_spec.trans (sq _), *, ne]

@[simp] lemma omega_eq_one_of_not_isChosen : ¬D.IsChosen w → D.ω w = 1 := (dite_eq_right ·)

lemma omega_zpow_mul_pow_eq_one {ψ} (n : ℤ) (h : ψ w = 1) : (D.ω ^ n * ψ) w ^ P.Mω D.s = 1 := by
  by_cases D.IsChosen w <;> simp_all [← @orderOf_ω _ _ w]

/-- For all natural numbers a and n there is a unitary automorphic character of U(1)(𝔸) of
weight σ ↦ −a·w₀(σ) and tame part (ω_w^n)_w. -/
lemma exists_char_hasWeight : ∃ μ, HasWeight μ (-a * D.w 0 ·) (D.ω ^ n) :=
  exists_hasWeight_of_prod_eq_one (S := D.finite_isChosen.toFinset) (by aesop) fun ⟨_, _⟩ U ↦ by
  obtain ⟨_, -, rfl⟩ := exists_zeta_pow_eq
    (.of_pow ((pow_torsionOrder_eq_one _ (algebraMap_mem_Ô.1 U)).substr .one) out)
  simp_all [↓← map_pow, w, b₁, b₂, ω, prod_eq_one, ↓zpow_mul, ↓zpow_natCast, pow_add, roundUp,
    pow_mul, pow_right_comm, ← Submonoid.one_def, pow_apply', ne, pow_right_comm _ _ D.N₁,
    isPrimitiveRoot_zeta.1, ↓inv_pow, pow_eq_pow_of_modEq N₁_mul_d_dvd_M_omega.modEq_zero_nat]
  simp [↓prod_phi_eq_norm,
    isPrimitiveRoot_zeta.norm_eq_one (by grind [Parameters] : D.N₁ ≠ 2) (irreducible_cyclotomic ..)]

/-- A fixed character of U(1)(𝔸), trivial on rational points, of weight −w₀ (`Data.w` at j =
0) and trivial tame part. -/
def muFlat := (D.exists_char_hasWeight 1 0).choose

/-- A fixed character of U(1)(𝔸), trivial on rational points, of weight 0 and tame part ω
(`Data.ω`). -/
def χ := (D.exists_char_hasWeight 0 1).choose

/-- The character μ♭ = `Data.muFlat` of U(1)(𝔸) has weight σ ↦ −w₀(σ) and trivial tame part. -/
lemma muFlat_hasWeight : D.muFlat.HasWeight (-D.w 0 ·) 1 := by grind [muFlat, pow_zero]

/-- The character χ = `Data.χ` of U(1)(𝔸) has weight 0 and tame part ω = `Data.ω`. -/
lemma chi_hasWeight : D.χ.HasWeight 0 D.ω := by rw [Pi.zero_def]; grind [χ, pow_one]

/-- A pair: an integer 1 ≤ z ≤ t and a character ν of U(1)(𝔸) of weight −c, z ≤ c(v) ≤ 4b, with
tame part supported on the chosen places. -/
structure Pair where
  ν : AutChar D.E
  c : D.Φ → ℕ
  (ψ z) hasWeight : ν.HasWeight (-c ·) ψ
  ψ_eq_one w : ¬D.IsChosen w → ψ w = 1
  z_mem : z ∈ Set.Icc 1 D.t
  le_c v : z ≤ c v
  c_le v : c v ≤ 4 * D.b

/-- The entry i (from 0) of the row parameter at v: k/2 − 1 − i for i < k − 1, and
−w⁻_{i+2−k}(v) otherwise, where w⁻_j = `Data.w` j − h₂. -/
def rowParameter v i := ite (i + 1 < D.k) (D.k / 2 - 1 - i : ℤ) (D.h₂ - D.w (i + 2 - D.k) v)

instance {u} : D.HasLogBound u (P.bigOmega D.s) (ite u 0 (-13 * D.logX)) :=
  bigOmega.eq_1 .. ▸ .of_mem_Icc (a := by grind [Data, c, sum_nonneg])

/-- The real number λ = m·(mean over infinite places v of log w(v)) + (m − 1) log(g·rd_E/2π) −
(15/2) log b, with w = `Data.nominalWeight`, g = g₀g₁. -/
def logLevelTarget := D.m * ((∑ v, .log (D.nominalWeight v)) / D.f) + (D.m - 1) * .log
  (D.gProd * D.rootDisc / (2 * .pi)) - 15 / 2 * D.logB

/-- The number λ = `Data.logLevelTarget` satisfies m log b ≤ λ ≤ 29 m log b. -/
lemma logLevelTarget_mem_Icc : D.logLevelTarget ∈ Set.Icc (D.m * D.logB) (29 * D.m * D.logB) := by
  constructor <;> [grw [logLevelTarget, ← (D.le_of_hasLogBound : D.b ^ 2 ≤ _ * _ / _),
    ← (D.le_of_hasLogBound : 1 ≤ D.nominalWeight _)]; grw [logLevelTarget, (D.le_of_hasLogBound :
    _ * _ / _ ≤ D.b ^ 27), (D.le_of_hasLogBound : D.nominalWeight _ ≤ D.b ^ 2)]] <;>
    simp [HasLogBound.pos D] <;> grind [Data, (D.le_of_hasLogBound : 99 * D.logB ≤ D.m * D.logB)]

/-- The level: a chosen prime N ≡ 1 mod M_ω² with log N ∈ [λ, λ + √(log b)], where λ =
`Data.logLevelTarget` and M_ω = `Parameters.Mω`. -/
def N := (D.exists_prime_window _
  (Set.Icc_subset_Icc D.le_of_hasLogBound D.le_of_hasLogBound D.logLevelTarget_mem_Icc)).choose

/-- The level N of the data is a prime number. -/
lemma N_prime : D.N.Prime := by grind [N]

lemma N_modEq_one : D.N ≡ 1 [MOD D.cycloConductor] := by grind [N, ModEq.of_dvd,
  N₁_mul_d_dvd_M_omega, sq]

/-- The level N satisfies λ ≤ log N ≤ λ + √(log b), where λ = `Data.logLevelTarget`.

Choice of the level prime. -/
lemma log_N_mem_window :
  .log D.N ∈ Set.Icc D.logLevelTarget (D.logLevelTarget + √D.logB) := by grind [N]

/-- The level N satisfies m log b ≤ log N ≤ 30 m log b. -/
lemma log_N_mem_Icc : .log D.N ∈ Set.Icc (D.m * D.logB) (30 * D.m * D.logB) := by
  grind [N, D.logLevelTarget_mem_Icc, (D.le_of_hasLogBound : √D.logB ≤ D.m * D.logB)]

instance {u} : D.HasLogBound u (.log D.N) (D.logX / 2 + D.logB.log + ite u 32 0) :=
  .of_mem_Icc _ _ D.log_N_mem_Icc

instance : Fact D.N.Prime := ⟨D.N_prime⟩

instance : D.HasLogLower D.N (101 * D.logB) :=
  ⟨(Real.le_log_iff_exp_le (HasLogBound.pos D)).1 D.le_of_hasLogBound⟩

/-- There is an integer π of E with ππ̄ = N, the level. -/
lemma exists_pi_mul_star : ∃ π : 𝓞 D.E, π * star π = D.N :=
  (Prime.sq_add_sq ((D.N_modEq_one.of_dvd (by grind [Parameters])).trans_ne nofun)).rec fun a ⟨b,
  h⟩ ↦ StablyUnram.exists_i_c₀.imp' (a + b * ·) (h ▸ by simp; grind)

/-- A chosen integer π of E with ππ̄ = N, the level. -/
def π := D.exists_pi_mul_star.choose

/-- The chosen integer π of E satisfies ππ̄ = N, where N is the level and the bar is complex
conjugation. -/
lemma π_mul_star : D.π * star D.π = D.N := by grind [π]

/-- A character of U(1)(𝔸) of weight 0 with tame part supported on a finite set Q of places of
norm prime to gN, Q disjoint from its conjugate. -/
structure TameChar where
  toAutChar : AutChar D.E
  Q : Finset _
  (ψ) hasWeight : toAutChar.HasWeight 0 ψ
  ψ_eq_one : ∀ w ∉ Q, ψ w = 1
  star_notMem : ∀ w ∈ Q, star w ∉ Q
  coprime : (D.gProd * D.N).Coprime (∏ w ∈ Q, w.q)

/-- The product of the norms of the places in the finite set Q of the tame character ϑ. -/
abbrev TameChar.levelNorm {D} (ϑ : @TameChar P D) := ∏ w ∈ ϑ.Q, w.q

/-- A twist: a tame character (`Data.TameChar`) whose tame part is non-trivial at every place of
its set Q. -/
structure Twist extends D.TameChar where psi_ne_one : ∀ w ∈ Q, ψ w ≠ 1

instance : One D.Twist := by use! 1, ∅, 1, .one <;> simp

instance : Coe D.Twist D.TameChar := ⟨Twist.toTameChar⟩

/-- The trivial character, as a tame character with empty set Q and trivial tame part. -/
abbrev TameChar.one {D} : @TameChar P D := Twist.toTameChar 1

/-- The character μ_j⁰ = μ♭(υ^{−h}χ)^j of U(1)(𝔸), with μ♭ = `Data.muFlat`, χ = `Data.χ`, υ
the restricted splitting character and h the gap. -/
def μ₀ := D.muFlat * (WeilData.upsilonU1 ^ (-D.h : ℤ) * D.χ) ^ j

/-- For every natural number j, the character μ_j⁰ of U(1)(𝔸) has weight −w_j and tame part ω^j. -/
lemma mu₀_hasWeight : (D.μ₀ j).HasWeight (-D.w j ·) (D.ω ^ (j : ℤ)) := by
  convert! D.muFlat_hasWeight.mul
    (((WeilData.hasWeight_upsilonU1_zpow _).mul D.chi_hasWeight).zpow j) <;> simp; grind

/-- For a tame character ϑ and a natural number j, the character μ_j⁰ϑ of U(1)(𝔸). -/
def liftChar ϑ j := D.μ₀ j * TameChar.toAutChar ϑ

/-- The family of residue field characters ω_w^j ϑ_w, with ϑ_w the tame part of ϑ; it is the
tame part of μ_j⁰ϑ. -/
def liftTamePart ϑ (j : ℕ) := D.ω ^ (j : ℤ) * TameChar.ψ ϑ

instance hasWeight_liftChar {ϑ j} : (D.liftChar ϑ j).HasWeight (-D.w j ·)
  (D.liftTamePart ϑ j) := by simpa using! (mu₀_hasWeight ..).mul ϑ.hasWeight

/-- The natural numbers j with 1 ≤ j ≤ m, m the number of lifts; they index the lifts. -/
abbrev LiftIndex := Set.Icc 1 D.m

/-- The disjoint union of S and j copies of T, the index type of Y_j. -/
@[instance_reducible] def _root_.BlockIndex (S T : Type) | 0 => S | j + 1 => BlockIndex S T j ⊕ T

/-- The inclusion of the first block S into the union of S and j copies of T. -/
def _root_.BlockIndex.firstBlock : ∀ j,
  S ↪ BlockIndex S T j | 0 => .refl _ | j + 1 => (BlockIndex.firstBlock j).trans .inl

/-- Given a bijection ν from S to α, a chosen bijection from `BlockIndex` S T j to the disjoint
union of α and {0, …, j − 1} × T; for j = 0 it is ν. -/
def _root_.BlockIndex.equivSum (ν : S ≃ α) : ∀ j, BlockIndex S T j ≃ α ⊕ Fin j × T
  | 0 => ν.trans (.symm (.sumEmpty ..))
  | j + 1 => (Cardinal.eq.1 (by simp! [(BlockIndex.equivSum ν j).cardinal_eq]; ring)).some

variable [Fintype S] [Fintype T] {P : Parameters} (D : Data P) (j : ℕ)

instance _root_.instFintypeYT :
    ∀ j, Fintype (BlockIndex S T j) | 0 => ‹_› | j + 1 => @instFintypeSum _ T (instFintypeYT j) _

@[simp] lemma _root_.BlockIndex.card : Fintype.card (BlockIndex S T j) = Fintype.card S + j *
  Fintype.card T := by simp [Fintype.card_congr (BlockIndex.equivSum (.refl _) j)]

/-- The natural number ⌊m/2⌋ − 1 (truncated at zero), where m is the number of lifts. -/
def ϱ := D.m / 2 - 1

/-- The basis indices of X_j other than the last: a set with n_j − 1 elements. -/
abbrev InitIndex := Fin (D.n j - 1)

/-- The basis index set of X_j: n_j − 1 indices together with one extra point for the last basis
vector e. -/
abbrev X := D.InitIndex j ⊕ Unit

/-- The shape of Y₀: ϱ = `Data.ϱ` hyperbolic planes, the basis indices of X₀, and the last
of them as distinguished index. -/
abbrev shape : Shape := ⟨D.ϱ, D.X 0, .inr ()⟩

/-- The basis index set of Y₀: e₁, …, e_ϱ, the indices of X₀, the middle vector z, and e*₁, …,
e*_ϱ. -/
@[reducible] def RowIndex := D.shape.BesselIndex deriving DecidableEq, Fintype

/-- The basis index set of Y_j: block R followed by j blocks of t indices each. -/
abbrev Y := BlockIndex D.RowIndex (Fin D.t) j

/-- The basis index set `Data.RowIndex` of Y₀ has exactly r elements, r the rank parameter of the
data. -/
lemma card_rowIndex : Fintype.card D.RowIndex = D.r := by simp; grind [ϱ, n]

instance {u l} [D.HasLogBound u D.r l] : D.HasLogBound u (Fintype.card D.RowIndex) l :=
  D.card_rowIndex ▸ ‹_›

/-- A chosen numbering of the basis indices of Y₀: a bijection from `Data.RowIndex` to {0, …, r −
1}. -/
def basisNumber := Fintype.equivFinOfCardEq D.card_rowIndex

/-- Twice the entry of ς = `Data.rowParameter` at τ numbered by i: the doubled parameter on the
spaces W_j of signs `Data.signsW` and on Y₀. -/
def paramW τ i := 2 * D.rowParameter τ (D.basisNumber i)

/-- The sign (−1)^{o + a + min(a − o, j)} of natural numbers o, j, a, with a − o truncated at
zero. -/
def entrySign : ℕ → ℕ → ℕ → ℤˣ | o + 1, 0, a => -entrySign o 0 a | o, j, a => (-1) ^ (o + a + min (a - o) j)

lemma ite_odd_eq_sub_emod (y : ℤ) : ite (j % 2 = 1) (y - 1) y = y - j % 2 := by lia

/-- Signs ±1 for W_j on the indices i of Y₀: −1 when `Data.basisNumber` i + 1 ≥ k + j, and +1
otherwise. -/
def signsW i := ite (D.posRank j ≤ D.basisNumber i) (-1 : ℤˣ) 1

/-- The map sending a pair (i, w), with w in the i-th family of places above g, to the
underlying finite place w of E. -/
def chosen (x : Σ i, D.ChosenPlace i) := x.2.1

/-- The finite group 𝖦 = ∏ GL_r(𝔽_w), over the chosen places w above g₀ and g₁. -/
abbrev G := ∀ x, GL D.RowIndex (ResField (D.chosen x))

instance (i) : Fintype (D.ChosenPlace i) := (D.finite_isChosen.sep _).fintype

/-- The finite set of families of monic polynomials c_w of degree r over the residue fields at
the chosen places w above g₀, g₁ that lie in `goodTuples` over each g_i. -/
def goodTupleFamilies :=
  (Fintype.piFinset fun _ ↦ goodTuples (P.Mω D.s) (Fintype.card D.RowIndex)).map
  (Equiv.piCurry fun i w ↦ Polynomial (ResField (D.chosen ⟨i, w⟩))).symm.toEmbedding

/-- The element e₀ of ℂ[𝖦], the sum of `tupleIdem` c over c in `goodTupleFamilies` for the integer
`Parameters.Mω`. -/
def e₀ := ∑ c ∈ D.goodTupleFamilies, tupleIdem D.RowIndex c
