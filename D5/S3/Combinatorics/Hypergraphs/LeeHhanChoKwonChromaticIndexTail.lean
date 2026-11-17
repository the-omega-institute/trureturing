/- GID: D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: none
   digest: Fixed-edge prefixes refute the proposed chromatic-index tail bound. -/

/-
result:
  proof_shape: content (a finite-prefix count and an unbounded dyadic counterexample family).
  escape_witness: fixed_prefix_prob_lower (the fixed-prefix probability estimate).
  admission_basis: open-problem-resolution (#20030; Refuted).
Direct frozen dependencies: none (all imports are pinned Mathlib).

The escape audit for result is unfinished: https://github.com/the-omega-institute/trureturing/issues/31150.
The symbolic refutation has utility: none; result is a §3.9 audit target.
The edge space and edge-size expressions from issue #20030 are inlined
literally; proofs use Finset.powersetCard and Nat.ceil without duplicate aliases.

Private declarations (Direct frozen dependencies: none for each):
  chromaticIndex_ge_of_prefix_eq: proof_shape: bind-only;
    consumer: filter_card_ge_fixed_prefix;
    Mathlib graph-colouring cardinality.
  filter_card_ge_fixed_prefix: proof_shape: content;
    consumer: tailProb_ge_fixed_prefix_ratio; suffix injection into the tail event.
  tailProb_ge_fixed_prefix_ratio: proof_shape: content;
    consumer: fixed_prefix_prob_lower; the same suffix-count estimate.
  cast_pow_two: proof_shape: bind-only; consumer: log_pow_two.
  log_pow_two: proof_shape: bind-only;
    consumers: mParam_pow_two, kParam_one_pow_two, result.
  eps_one: proof_shape: bind-only;
    consumers: log_inv_eps_one, kParam_one_pow_two, result.
  log_inv_eps_one: proof_shape: bind-only; consumer: alphaParam_one_three_pow_two.
  mParam_pow_two: proof_shape: bind-only; consumer: result.
  kParam_one_pow_two: proof_shape: bind-only; consumer: result.
  alphaParam_one_three_pow_two: proof_shape: bind-only; consumer: result.
  ratio_eq: proof_shape: bind-only; consumer: fixed_prefix_prob_lower.
  four_mul_le_two_pow: proof_shape: bind-only; consumer: pow4_le_pow2pow;
    Mathlib Nat.mul_le_pow applied at s-2 and normalized.
  pow4_le_pow2pow: proof_shape: bind-only; consumer: result.
  exists_nonempty_edge: proof_shape: bind-only;
    consumers: fixed_prefix_prob_lower, result; Finset.powersetCard_nonempty.
  fixed_prefix_prob_lower: proof_shape: content; consumer: result;
    suffix count and Nat.choose_le_pow give the fixed-prefix probability bound.
  pow2eq: proof_shape: bind-only; consumer: result.
  eight_mul_pow_two_eq: proof_shape: bind-only; consumer: result.

The public definitions are chromaticIndex, tailProb, eps, kParam, alphaParam,
and claim. Only result is a public theorem. The proof uses repeated edges;
it does not establish the binomial-strength bound or the distinct-edge variant.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace D5.S3.Combinatorics.Hypergraphs.LeeHhanChoKwonChromaticIndexTail

noncomputable def chromaticIndex {k α : ℕ} (e : Fin α → Finset (Fin k)) : ℕ :=
  sInf {c | ∃ f : Fin α → Fin c, ∀ i j, i ≠ j → (e i ∩ e j).Nonempty → f i ≠ f j}
open Classical in
noncomputable def tailProb (k m α : ℕ) (x : ℝ) : ℝ :=
  (((Fintype.piFinset (Function.const (Fin α) ((Finset.univ : Finset (Fin k)).powersetCard m))).filter fun e => x < chromaticIndex e).card : ℝ) /
    ((((Finset.univ : Finset (Fin k)).powersetCard m)).card ^ α : ℕ)

private theorem chromaticIndex_ge_of_prefix_eq {k α r : ℕ} {e0 : Finset (Fin k)}
    (e : Fin α → Finset (Fin k)) (hr : r ≤ α)
    (heq : ∀ i : Fin r, e (Fin.castLE hr i) = e0)
    (he0 : e0.Nonempty) : r ≤ chromaticIndex e  := by
  classical
  let G := SimpleGraph.fromRel (fun i j : Fin α => (e i ∩ e j).Nonempty)
  have hnon : {c : ℕ | ∃ f : Fin α → Fin c,
      ∀ i j, i ≠ j → (e i ∩ e j).Nonempty → f i ≠ f j}.Nonempty := by
    obtain ⟨C⟩ := G.colorable_of_fintype
    refine ⟨Fintype.card (Fin α), C, ?_⟩
    intro i j hij he
    exact C.valid ⟨hij, Or.inl he⟩
  apply le_csInf hnon
  intro c ⟨f, hf⟩
  let C : G.Coloring (Fin c) := SimpleGraph.Coloring.mk f (by
    intro i j hij
    apply hf i j hij.1
    rcases hij.2 with h | h
    · exact h
    · simpa only [Finset.inter_comm] using h)
  have hp : Pairwise (fun i j : Fin r => G.Adj (Fin.castLE hr i) (Fin.castLE hr j)) := by
    intro i j hne
    refine ⟨(Fin.castLE_injective hr).ne hne, Or.inl ?_⟩
    change (e (Fin.castLE hr i) ∩ e (Fin.castLE hr j)).Nonempty
    rw [heq i, heq j, Finset.inter_self]
    exact he0
  simpa only [Nat.card_fin] using
    SimpleGraph.Colorable.card_le_of_pairwise_adj (G := G) (n := c) ⟨C⟩ (Fin.castLE hr) hp

private theorem filter_card_ge_fixed_prefix {k m α r : ℕ} (hr : r ≤ α)
    (x : ℝ) (hx : x < r)
    {e0 : Finset (Fin k)} (he0 : e0 ∈ ((Finset.univ : Finset (Fin k)).powersetCard m)) (hne : e0.Nonempty) :
    ((Fintype.piFinset (Function.const (Fin α) ((Finset.univ : Finset (Fin k)).powersetCard m))).filter
      (fun e => x < chromaticIndex e)).card ≥
      (((Finset.univ : Finset (Fin k)).powersetCard m)).card ^ (α - r) := by
  classical
  let E := {s : Finset (Fin k) // s ∈ ((Finset.univ : Finset (Fin k)).powersetCard m)}
  let φ : (Fin (α - r) → E) → (Fin α → Finset (Fin k)) :=
    fun u i => Fin.append (fun _ : Fin r => e0) (fun j => (u j).1)
      (Fin.cast (Nat.add_sub_of_le hr).symm i)
  have hφinj : Function.Injective φ := by
    intro u v huv
    funext j
    apply Subtype.ext
    have h := congrFun huv (Fin.cast (Nat.add_sub_of_le hr) (Fin.natAdd r j))
    change Fin.append _ _ (Fin.natAdd r j) = Fin.append _ _ (Fin.natAdd r j) at h
    simpa only [Fin.append_right] using h
  let ψ : (Fin (α - r) → E) →
      {e : Fin α → Finset (Fin k) // e ∈
        (Fintype.piFinset (Function.const (Fin α) ((Finset.univ : Finset (Fin k)).powersetCard m))).filter
          (fun e => x < chromaticIndex e)} := by
    intro u
    refine ⟨φ u, ?_⟩
    rw [Finset.mem_filter]
    constructor
    · rw [Fintype.mem_piFinset]
      intro i
      change Fin.append (fun _ : Fin r => e0) (fun j => (u j).1)
        (Fin.cast (Nat.add_sub_of_le hr).symm i) ∈
          ((Finset.univ : Finset (Fin k)).powersetCard m)
      generalize Fin.cast (Nat.add_sub_of_le hr).symm i = j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.append_left] using he0
      · simpa only [Fin.append_right] using (u j).2
    · have hNat := chromaticIndex_ge_of_prefix_eq
        (e := φ u) hr (by
          intro i
          change Fin.append _ _ (Fin.castAdd (α-r) i) = e0
          exact Fin.append_left _ _ i) hne
      have hReal : (r : ℝ) ≤ (chromaticIndex (φ u) : ℝ) := by
        exact_mod_cast hNat
      exact lt_of_lt_of_le hx hReal
  have hψinj : Function.Injective ψ := by
    exact Function.Injective.of_comp (f := Subtype.val) (g := ψ) hφinj
  have hcard := Fintype.card_le_of_injective ψ hψinj
  have hdomain : Fintype.card (Fin (α - r) → E) = (((Finset.univ : Finset (Fin k)).powersetCard m)).card ^ (α - r) := by
    rw [Fintype.card_fun, Fintype.card_subtype]
    simp
  have hfilter : Fintype.card {e : Fin α → Finset (Fin k) // e ∈
      (Fintype.piFinset (Function.const (Fin α) ((Finset.univ : Finset (Fin k)).powersetCard m))).filter
        (fun e => x < chromaticIndex e)} =
      ((Fintype.piFinset (Function.const (Fin α) ((Finset.univ : Finset (Fin k)).powersetCard m))).filter
        (fun e => x < chromaticIndex e)).card := by
    rw [Fintype.card_subtype]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hfilter] at hcard
  simpa [hdomain] using hcard

private theorem tailProb_ge_fixed_prefix_ratio {k m α r : ℕ} (hr : r ≤ α)
    (x : ℝ) (hx : x < r)
    {e0 : Finset (Fin k)} (he0 : e0 ∈ ((Finset.univ : Finset (Fin k)).powersetCard m)) (hne : e0.Nonempty)
    (hN : 0 < (((Finset.univ : Finset (Fin k)).powersetCard m)).card) :
    ((((Finset.univ : Finset (Fin k)).powersetCard m)).card : ℝ) ^ (α - r) /
        ((((Finset.univ : Finset (Fin k)).powersetCard m)).card : ℝ) ^ α ≤
        tailProb k m α x := by
  classical
  unfold tailProb
  have hcount := filter_card_ge_fixed_prefix hr x hx he0 hne
  have hnum : ((((Finset.univ : Finset (Fin k)).powersetCard m)).card ^ (α - r) : ℝ) ≤
      (((Fintype.piFinset (Function.const (Fin α) ((Finset.univ : Finset (Fin k)).powersetCard m))).filter
        (fun e => x < chromaticIndex e)).card : ℝ) := by
    exact_mod_cast hcount
  have hden : 0 < ((((Finset.univ : Finset (Fin k)).powersetCard m)).card ^ α : ℕ) := by positivity
  have hdenR : 0 < ((((Finset.univ : Finset (Fin k)).powersetCard m)).card ^ α : ℝ) := by
    exact_mod_cast hden
  simpa only [Nat.cast_pow] using div_le_div_of_nonneg_right hnum hdenR.le

noncomputable def eps (c : ℝ) (t : ℕ) : ℝ := (2 : ℝ) ^ (-((t : ℝ) ^ (1 + c)))
noncomputable def kParam (c : ℝ) (t : ℕ) : ℕ := ⌈3 * Real.logb 2 ((t : ℝ) ^ 2 / eps c t)⌉₊
noncomputable def alphaParam (c β : ℝ) (t : ℕ) : ℕ := ⌈β * t * Real.logb 2 (1 / eps c t)⌉₊
private theorem cast_pow_two (q : ℕ) : ((2 ^ q : ℕ) : ℝ) = (2 : ℝ)^q := by
  norm_num [Nat.cast_pow]
private theorem log_pow_two (q : ℕ) : Real.logb 2 ((2 ^ q : ℕ) : ℝ) = q := by
  rw [cast_pow_two, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num
private theorem eps_one (t : ℕ) : eps 1 t = (2 : ℝ) ^ (-((t : ℝ) ^ 2)) := by
  simp only [eps]
  congr 2
  norm_num

private theorem log_inv_eps_one (t : ℕ) : Real.logb 2 (1 / eps 1 t) = (t : ℝ) ^ 2 := by
  rw [eps_one, one_div, Real.rpow_neg (by norm_num)]
  simp only [inv_inv]
  rw [Real.logb_rpow (by norm_num) (by norm_num)]
private theorem mParam_pow_two (q : ℕ) : ⌈Real.logb 2 ((2 ^ q : ℕ) : ℝ)⌉₊ = q := by
  rw [log_pow_two]
  exact Nat.ceil_natCast _
private theorem kParam_one_pow_two (q : ℕ) : kParam 1 (2 ^ q) = 3 * (2 ^ q)^2 + 6*q := by
  rw [kParam, eps_one]
  have hlog : Real.logb 2 (((2 ^ q : ℕ) : ℝ) ^ 2 /
      (2 : ℝ) ^ (-((2 ^ q : ℕ) : ℝ) ^ 2)) =
      2*(q : ℝ) + ((2 ^ q : ℕ) : ℝ)^2 := by
    rw [Real.logb_div]
    · rw [Real.logb_pow, log_pow_two, Real.logb_rpow (by norm_num) (by norm_num)]
      ring
    · positivity
    · positivity
  rw [hlog]
  have hlin : (3 : ℝ) * (2*(q : ℝ) + ((2 ^ q : ℕ) : ℝ)^2) =
      3 * ((2 ^ q : ℕ) : ℝ)^2 + 6*(q : ℝ) := by ring
  rw [hlin]
  have hcast : (3 : ℝ) * ((2 ^ q : ℕ) : ℝ)^2 + 6*(q : ℝ) =
      (3 * (2 ^ q)^2 + 6*q : ℕ) := by
    norm_num [Nat.cast_pow]
  rw [hcast]
  exact Nat.ceil_natCast _
private theorem alphaParam_one_three_pow_two (q : ℕ) : alphaParam 1 3 (2 ^ q) = 3 * (2 ^ q)^3 := by
  rw [alphaParam, log_inv_eps_one]
  have hcast1 : (3 : ℝ) * ((2 ^ q : ℕ) : ℝ) * ((2 ^ q : ℕ) : ℝ)^2 =
      3 * (((2 ^ q : ℕ) : ℝ)^3) := by ring
  have hcast2 : (3 : ℝ) * (((2 ^ q : ℕ) : ℝ)^3) =
      (3 * (2 ^ q)^3 : ℕ) := by norm_num [Nat.cast_pow]
  rw [hcast1, hcast2]
  exact Nat.ceil_natCast _
private theorem ratio_eq {N α r : ℕ} (hr : r ≤ α) (hN : 0 < N) :
    (N : ℝ) ^ (α-r) / (N : ℝ)^α = (N : ℝ)⁻¹ ^ r := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  rw [pow_sub₀ _ hNr hr]
  field_simp
  rw [one_div, ← mul_pow, mul_inv_cancel₀ hNr, one_pow]

private theorem four_mul_le_two_pow : ∀ s : ℕ, 4 ≤ s → 4*s ≤ 2^s := by
  intro s hs
  have h := Nat.mul_le_pow (by decide : (2 : ℕ) ≠ 1) (s - 2)
  have hs2 : s - 2 + 2 = s := by omega
  have hpow : 2^s = 4 * 2^(s-2) := by
    calc
      2^s = 2^(s-2+2) := by rw [hs2]
      _ = 4 * 2^(s-2) := by rw [pow_add]; ring
  rw [hpow]
  have hsub : s = (s - 2) + 2 := hs2.symm
  nlinarith

private theorem pow4_le_pow2pow (s : ℕ) (hs : 4 ≤ s) : (2^s)^4 ≤ 2^(2^s) := by
  rw [← Nat.pow_mul]
  apply Nat.pow_le_pow_right (by decide : 2 > 0)
  simpa [Nat.mul_comm] using four_mul_le_two_pow s hs

def claim : Prop :=
  ∀ c β : ℝ, 0 < c → 1 + c < β → ∃ C : ℝ, ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
    tailProb (kParam c t) (⌈Real.logb 2 (t : ℝ)⌉₊) (alphaParam c β t) (C * t * Real.logb 2 t) < eps c t


private theorem exists_nonempty_edge {k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) :
    ∃ e₀ : Finset (Fin k), e₀ ∈ ((Finset.univ : Finset (Fin k)).powersetCard m) ∧ e₀.Nonempty := by
  have hu : (Finset.univ : Finset (Fin k)).card = k := by simp
  have hp : (((Finset.univ : Finset (Fin k)).powersetCard m)).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    simpa [hu] using hmk
  rcases hp with ⟨e₀, he₀⟩
  refine ⟨e₀, he₀, ?_⟩
  apply Finset.card_pos.mp
  rw [(Finset.mem_powersetCard.mp he₀).2]
  omega

private theorem fixed_prefix_prob_lower {k m α r : ℕ} (hr : r ≤ α)
    (x : ℝ) (hx : x < r) (hm : 1 ≤ m) (hmk : m ≤ k)
    (hN : 0 < (((Finset.univ : Finset (Fin k)).powersetCard m)).card) :
    1 / (k : ℝ) ^ (m * r) ≤ tailProb k m α x := by
  rcases exists_nonempty_edge hm hmk with ⟨e₀, he₀, hne⟩
  have hratio := tailProb_ge_fixed_prefix_ratio hr x hx he₀ hne hN
  have hratio' := ratio_eq hr hN
  rw [hratio'] at hratio
  have hcard : (((Finset.univ : Finset (Fin k)).powersetCard m)).card ≤ k ^ m := by
    simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using
      Nat.choose_le_pow k m
  have hcardR : (((Finset.univ : Finset (Fin k)).powersetCard m)).card ≤ (k : ℝ)^m := by
    exact_mod_cast hcard
  have hpow : ((((Finset.univ : Finset (Fin k)).powersetCard m)).card : ℝ)^r ≤ ((k : ℝ)^m)^r :=
    pow_le_pow_left₀ (by positivity) hcardR r
  have hinv : 1 / ((k : ℝ)^m)^r ≤ 1 / ((((Finset.univ : Finset (Fin k)).powersetCard m)).card : ℝ)^r :=
    one_div_le_one_div_of_le (by positivity) hpow
  calc
    1 / (k : ℝ) ^ (m * r) = 1 / ((k : ℝ)^m)^r := by rw [pow_mul]
    _ ≤ 1 / ((((Finset.univ : Finset (Fin k)).powersetCard m)).card : ℝ)^r := hinv
    _ = ((((Finset.univ : Finset (Fin k)).powersetCard m)).card : ℝ)⁻¹ ^ r := by rw [one_div, inv_pow]
    _ ≤ tailProb k m α x := hratio

private theorem pow2eq (A m r : ℕ) :
    1 / ((2 ^ A : ℕ) : ℝ) ^ (m*r) =
      (2 : ℝ) ^ (-((A*m*r : ℕ) : ℝ)) := by
  rw [Nat.cast_pow, ← pow_mul, one_div, ← Real.rpow_natCast]
  calc
    ((2 : ℝ) ^ ((A * (m * r) : ℕ) : ℝ))⁻¹ =
        (2 : ℝ) ^ (-((A * (m * r) : ℕ) : ℝ)) :=
      (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm
    _ = (2 : ℝ) ^ (-((A*m*r : ℕ) : ℝ)) := by
      congr 2
      norm_num [Nat.mul_assoc]

private theorem eight_mul_pow_two_eq (q : ℕ) : 8 * (2^q)^2 = 2^(2*q+3) := by
  calc
    8 * (2^q)^2 = 2^3 * (2^q)^2 := by norm_num
    _ = 2^3 * 2^(q*2) := by rw [← Nat.pow_mul]
    _ = 2^(3 + q*2) := by rw [← Nat.pow_add]
    _ = 2^(2*q+3) := by congr 1; omega

theorem result : ¬ claim := by
  intro hclaim
  rcases hclaim 1 3 (by norm_num) (by norm_num) with ⟨C, T, htail⟩
  let L : ℕ := max 1 (Nat.ceil C)
  have hL1 : 1 ≤ L := by dsimp [L]; exact Nat.le_max_left _ _
  have hCL : C ≤ (L : ℝ) := by
    calc
      C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil C
      _ ≤ (L : ℝ) := by exact_mod_cast Nat.le_max_right 1 (Nat.ceil C)
  let s : ℕ := max 64 (max T (32 * (L + 1)))
  have hs64 : 64 ≤ s := by dsimp [s]; exact Nat.le_max_left _ _
  have hsT : T ≤ s := by
    dsimp [s]
    exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hsL : 32 * (L + 1) ≤ s := by
    dsimp [s]
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  let q : ℕ := 2 ^ s
  let t : ℕ := 2 ^ q
  have hspos : 1 < s := by omega
  have hsq : s < q := by
    dsimp [q]
    exact Nat.lt_pow_self (n := s) (a := 2) (by decide)
  have hq64 : 64 ≤ q := hs64.trans hsq.le
  have hqT : T ≤ q := hsT.trans hsq.le
  have hqt : q < t := by
    dsimp [t]
    exact Nat.lt_pow_self (n := q) (a := 2) (by decide)
  have hTt : T ≤ t := hqT.trans hqt.le
  let k : ℕ := 3 * t^2 + 6*q
  let a : ℕ := 3 * t^3
  let r : ℕ := L * t * q + 1
  have hqpos : 1 ≤ q := by omega
  have htpos : 1 ≤ t := by omega
  have hLq : L ≤ q := by
    have : 32 * (L + 1) ≤ q := hsL.trans hsq.le
    omega
  have hmk : q ≤ k := by
    dsimp [k]
    nlinarith
  have hm : 1 ≤ q := hqpos
  have hN : 0 < (((Finset.univ : Finset (Fin k)).powersetCard q)).card := by
    rcases exists_nonempty_edge hm hmk with ⟨e₀, he₀, _⟩
    exact Finset.card_pos.mpr ⟨e₀, he₀⟩
  have hLprod : L * t * q ≤ t^3 := by
    have h1 : L * (t*q) ≤ q * (t*q) := by
      exact Nat.mul_le_mul_right (t*q) hLq
    have h2 : q * (t*q) ≤ t * (t*q) := by
      exact Nat.mul_le_mul_right (t*q) hqt.le
    have h3 : t * (t*q) ≤ t * (t*t) := by
      exact Nat.mul_le_mul_left t (Nat.mul_le_mul_left t hqt.le)
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h1.trans (h2.trans h3)
  have hra : r ≤ a := by
    dsimp [r, a]
    have hrt : L * t * q + 1 ≤ t^3 + 1 := Nat.add_le_add_right hLprod 1
    have ht3pos : 0 < t^3 := Nat.pow_pos htpos
    have ht3 : 1 ≤ t^3 := by omega
    exact hrt.trans (by omega)
  have hlogt : Real.logb 2 (t : ℝ) = q := by
    dsimp [t]
    exact log_pow_two q
  have hx : C * (t : ℝ) * Real.logb 2 (t : ℝ) < r := by
    rw [hlogt]
    have hprod : C * (t : ℝ) * (q : ℝ) ≤ (L : ℝ) * (t : ℝ) * (q : ℝ) := by
      gcongr
    have hstrict : (L : ℝ) * (t : ℝ) * (q : ℝ) < (r : ℝ) := by
      dsimp [r]
      norm_num
    exact hprod.trans_lt hstrict
  have hk8 : k ≤ 8 * t^2 := by
    dsimp [k]
    nlinarith
  have hpow4 : q^4 ≤ t := by
    dsimp [q, t]
    have hs4 : 4 ≤ s := by omega
    exact pow4_le_pow2pow s hs4
  have hA : 2*q + 3 ≤ 3*q := by omega
  have h32L : 32 * L ≤ q := by
    have : 32 * (L + 1) ≤ q := hsL.trans hsq.le
    omega
  have h16r : 16 * r ≤ 2 * t * q^2 := by
    dsimp [r]
    have hprod : 32 * (L * t * q) ≤ t * q^2 := by
      have h := Nat.mul_le_mul_right (t*q) h32L
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    have hsmall : 32 ≤ t * q^2 := by
      have ht16 : 16 ≤ t := by
        dsimp [t]
        have hq4 : 4 ≤ q := by omega
        exact (Nat.pow_le_pow_right (n := 2) (by decide) hq4)
      nlinarith
    nlinarith [hprod]
  have hE : (2*q + 3) * q * r < t^2 := by
    have hmul : 16 * ((2*q + 3) * q * r) ≤ 6 * t^2 := by
      have h1 : (2*q + 3) * q * r ≤ 3 * q^2 * r := by
        have h := Nat.mul_le_mul_right (q*r) hA
        simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
      have h2 := Nat.mul_le_mul_left 16 h1
      have h3 := Nat.mul_le_mul_left (3*q^2) h16r
      have hq4 := Nat.mul_le_mul_left (6*t) hpow4
      nlinarith [h2, h3, hq4]
    have ht2 : 0 < t^2 := by positivity
    omega
  have hprob := fixed_prefix_prob_lower (k := k) (m := q) (α := a) (r := r)
    hra (C * (t : ℝ) * Real.logb 2 (t : ℝ)) hx hm hmk hN
  have hkpow : k ≤ 2^(2*q + 3) := by
    calc
      k ≤ 8*t^2 := hk8
      _ = 2^(2*q + 3) := by
        dsimp [t]
        exact eight_mul_pow_two_eq q
  have hpowk : k^ (q*r) ≤ (2^(2*q+3) : ℕ)^(q*r) := by
    exact pow_le_pow_left₀ (by positivity) hkpow (q*r)
  have hinvk : 1 / ((2^(2*q+3) : ℕ) : ℝ)^(q*r) ≤
      1 / (k : ℝ)^(q*r) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast hpowk
  have hpow2 : 1 / ((2^(2*q+3) : ℕ) : ℝ)^(q*r) =
      (2 : ℝ) ^ (-(((2*q+3)*q*r : ℕ) : ℝ)) := by
    exact pow2eq (2*q+3) q r
  have hEreal : (((2*q+3)*q*r : ℕ) : ℝ) < ((t^2 : ℕ) : ℝ) := by
    exact_mod_cast hE
  have hpowgt : (2 : ℝ)^(-((t^2 : ℕ) : ℝ)) <
      (2 : ℝ)^(-(((2*q+3)*q*r : ℕ) : ℝ)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    exact neg_lt_neg hEreal
  have heps : eps 1 t = (2 : ℝ)^(-((t^2 : ℕ) : ℝ)) := by
    rw [eps_one]
    congr 2
    norm_num [Nat.cast_pow]
  have htail_lower : eps 1 t < tailProb k q a (C * (t : ℝ) * Real.logb 2 (t : ℝ)) := by
    rw [heps]
    exact hpowgt.trans_le (hpow2 ▸ hinvk.trans hprob)
  have htail_upper := htail t hTt
  have hparams :
      kParam 1 t = k ∧ ⌈Real.logb 2 (t : ℝ)⌉₊ = q ∧ alphaParam 1 3 t = a := by
    subst t
    dsimp [k, a]
    exact ⟨kParam_one_pow_two q, mParam_pow_two q, alphaParam_one_three_pow_two q⟩
  rw [hparams.1, hparams.2.1, hparams.2.2, hlogt] at htail_upper
  rw [hlogt] at htail_lower
  exact (lt_irrefl _ (htail_lower.trans htail_upper))

end D5.S3.Combinatorics.Hypergraphs.LeeHhanChoKwonChromaticIndexTail
