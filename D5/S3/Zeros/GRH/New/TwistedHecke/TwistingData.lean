/- GID: D5/S3/Zeros/GRH/New/TwistedHecke/TwistingData
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/TwistedHecke/TwistingData
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.TwistedHecke.TwistingData. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/TwistedHecke/TwistingData.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Algebra.ZerosCostDegree
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: A Frobenius-twisted Hecke operator has small elementary divisors (see
New.Columns.TwistedHeckeType).

This file: Frobenius-twisted circle of letters: action, depth, excess, weight conditions, basic
properties. -/

noncomputable section


open Fintype Finset MvPolynomial Matrix IsLocalRing Ideal
variable (k N) (W R R' : Type) [CommRing W] [IsLocalRing W] [CommRing R] [CommRing R']
  (φ : R →+* R')
attribute [local simp ←] prod_pow_eq_pow_sum add_assoc coeff_map Quotient.eq_zero_iff_dvd
attribute [local simp] polyOfCoeffs exponentOf Finsupp.weight_eq_sum prod_prod_type_right
  Fintype.prod_ite_zero prod_univ_sum sum_prod_type_right diagonal_apply linSubst_mul map_bind₁
  AlgHom.ext_iff smul_eq_C_mul

/-- For natural r, the labelling of indices b in {0,…,k−1} equal to 0 if b < r and 1 otherwise. -/
def twoBlock r (b : Fin k) := ite (b.1 < r) 0 1

/-- Twisting data: p prime, P = p^o₀ ≥ 5, W with P^N residues, alternately even and odd ring maps
ι_s: W → R (s in ℤ/N, the letters), ι_{s+1} ≡ ι_s^P mod p, and w² = p in R. -/
structure TwistingData where
  (p o₀ : ℕ) ι : ZMod N → W →+* R
  isEven : ZMod N → _
  w : R
  prime : p.Prime
  five_le_P : 5 ≤ p ^ o₀
  w_sq : w ^ 2 = p
  frobenius_congr s x : ↑p ∣ ι (s + 1) x - ι s x ^ p ^ o₀
  isEven_succ s : isEven (s + 1) = !isEven s
  card_residueField : .card (ResidueField W) = (p ^ o₀) ^ N

namespace TwistingData

variable {k N W R R'} [NeZero N] (T : TwistingData N W R) (n r : ℕ) (i) (a a' :
  Fin k) {τ} (g : GL (Fin k) W) (s : ZMod N) (x : Fin k × _)

/-- The prime power P = p^o₀ of the twisting data. -/
abbrev P := T.p ^ T.o₀

/-- The number q = P^N = p^{o₀N} of elements of the residue field of W. -/
abbrev q := T.P ^ N

/-- For twisting data over R and a ring map φ: R→R', the twisting data over R' obtained by
composing each ι_s with φ and replacing w by φ(w). -/
def map := {T with
  ι := φ.comp ∘ T.ι, w := φ T.w, w_sq := by simp [← map_pow, w_sq]
  frobenius_congr := by simpa using (map_dvd φ <| T.frobenius_congr · ·)}

/-- The homomorphism sending g in GL_k(W) to the matrix g_s over R: ι_s(g) if the letter s is
even, ι_s of the inverse transpose if s is odd. -/
@[simps -isSimp] def letterMatrix := MonoidHom.mk ⟨fun g : GL (Fin k) W ↦
  (ite (T.isEven s) ↑g g⁻¹.1ᵀ).map (T.ι s), by simp⟩ (by bound)

/-- The action of GL_k(W) on polynomials in the variables x_{bs}: g sends x_{bs} to ∑_c
(g_s)_{cb} x_{cs}, with g_s = `TwistingData.letterMatrix` s g. -/
def polyAction := MonoidHom.mk ⟨fun g ↦ linSubst (blockDiagonal (T.letterMatrix (k := k) · g)),
  by simp [← Pi.one_def]⟩ (by simp)

/-- The matrix ρ(g) of g in GL_k(W) on forms of degree n in each letter: the Kronecker product
over s of the n-th symmetric powers of `TwistingData.letterMatrix` s g. -/
@[simps -isSimp] def letterRep := MonoidHom.mk ⟨fun g ↦
  kroneckerPi (symPowMatrix n <| T.letterMatrix (k := k) · g), by simp⟩ (by simp [kroneckerPi_mul])

/-- The indicator of the deep variables (b,s), b counted from 0: 1 if s is even and b ≥ r, or s
is odd and b < r; else 0. -/
def deepIndicator := if T.isEven x.2 ↔ r ≤ x.1 then 1 else 0

/-- The depth of a family β of degree-n exponents: the total degree of the monomial x^β in the
variables that are deep for r (`TwistingData.deepIndicator`). -/
def depth k n r β := (exponentOf (a := n) β).weight (T.deepIndicator (k := k) r)

/-- For indices a,a' and letter s, the variable index (a',s) if s is even and (a,s) if s is odd. -/
@[simps] def rootVar := (ite (T.isEven s) a' a, s)

/-- The weight on variables defining the excess at letter i: ±P^{(s−i) mod N}/q at u_s =
`TwistingData.rootVar` a a' s, ū_s = `TwistingData.rootVar` a' a s, plus 1−1/q at u_i. -/
def excessWeight := (ite (x = T.rootVar a a' x.2) (T.P ^ (1 + (x.2 - 1 - i).val)) 0 -
  ite (x = T.rootVar a' a x.2) (T.P ^ (x.2 - i).val) 0 : ℝ) / T.q

/-- The submodule of vectors F with (ρ(g)F)_β in the ideal I for all β in B and all g in the
Levi subgroup of τ, ρ acting in degree n. -/
def translatesIn τ (I : Ideal R) (B : Set _) := (⟨⟨⟨{F | ∀ g ∈ @levi k W _ τ, ∀ β ∈ B,
  (T.letterRep n g *ᵥ F) β ∈ I}, by aesop⟩, by simp⟩, by simp_all [mul_mem_left]⟩ : Submodule R _)

/-- Columns F such that (ρ(g)F)_β lies in I whenever g is block diagonal with blocks a', k−a'
and β has excess (`TwistingData.excessWeight`) above h at some letter. -/
abbrev excessCond I h :=
  T.translatesIn n (twoBlock k a') I {β | ∃ i, h < (exponentOf β).weight (T.excessWeight i a a')}

/-- The space V_d of forms F of degree n in each letter such that, for all g in GL_k(W), ρ(g)F
has only monomials of depth at least d. -/
abbrev deepForms k n r d := T.translatesIn n 0 ⊥ {β | T.depth k n r β < d}

attribute [local simp] symPowMatrix linSubst polyAction kroneckerPi letterRep pow_mul' excessWeight
  depth blockDiagonal mulVec_eq_sum
attribute [local grind!] TwistingData le_self_pow NeZero

omit [NeZero N] in
lemma one_lt_P : (1 : ℝ) < T.P := mod_cast by lia

lemma one_lt_q : (1 : ℝ) < T.q := mod_cast by grind

omit [NeZero N] in
lemma frobenius_pow_congr x : ↑T.p ∣ T.ι (s + n) x - T.ι s x ^ T.P ^ n := have := T.frobenius_congr
             by induction n <;> simp_all [pow_succ']

variable {n r i a a' g x}

omit [NeZero N] in
lemma w_ne_zero [CharZero R] : T.w ≠ 0 := by grind [Nat.cast_inj, T.prime.pos]

omit [NeZero N] in
include T in lemma finite_residueField : Finite (ResidueField W) := by grind [Nat.card_pos_iff]

lemma p_dvd_letterMatrix_of_mem_parahoric (hg : g ∈ parahoric W τ) i j (h : ite (T.isEven s)
  (τ i < τ j) (τ j < τ i)) : ↑T.p ∣ T.letterMatrix s g i j := ((isUnit_one_sub_self_of_mem_nonunits
  _ (pow_mem_of_mem _ ((residue_eq_zero_iff (ite (T.isEven s) _ g⁻¹.1ᵀ i j)).1 (by
  split_ifs at * <;> apply_rules [inv_mem hg])) (T.q - 1) (by grind))).map (T.ι s)).dvd_mul_right.1
  (by simpa [letterMatrix, mul_sub, mul_pow_sub_one, T.prime.ne_zero] using
  T.frobenius_pow_congr N ..)

/-- An element g of GL_k(W) sends the variable x = x_{cs} to ∑_b (g_s)_{bc} x_{bs}, where g_s =
`TwistingData.letterMatrix` s g. -/
lemma polyAction_X : T.polyAction g (X x) = ∑ b,
  C (T.letterMatrix x.2 g b x.1) * X (b, x.2) := by simp

lemma diagonal_pow_depth (x : R) : diagonal (x ^ T.depth k n r ·) = kroneckerPi fun s ↦
  symPowMatrix n (diagonal (n := Fin k) (x ^ T.deepIndicator r ⟨·, s⟩)) := by ext; simp [apply_ite,
  -aeval_eq_bind₁, aeval_monomial, C_mul_X_eq_monomial, monomial_pow, ← monomial_sum_prod]; grind

/-- For a coefficient vector F, g sends ∑_β F(β) x^β to ∑_β (ρ(g)F)(β) x^β: the matrix ρ(g) =
`TwistingData.letterRep` n g represents the action on forms of degree n in each letter. -/
lemma polyAction_polyOfCoeffs F : T.polyAction g (polyOfCoeffs F) =
  polyOfCoeffs (T.letterRep n g *ᵥ F) := by
  simpa [monomial_eq, coeff_map, -univ_eq_attach] using congr(∑ α, F α • ∏ s, rename (·, s)
    $(sum_monomials_eq_of_isHomogeneous ((α s).isHomogeneous_linSubst (T.letterMatrix s g)))).symm

lemma letterRep_map : (T.map φ).letterRep n g = (T.letterRep n g).map φ := by aesop

@[simp] lemma one_add_val_sub_one_sub : 1 + (s - 1 - i).val = ite (s = i) N (s - i).val := by
  zify; simp [sub_right_comm, ZMod.cast_sub_one]

lemma five_mul_P_pow_le_q : 5 * T.P ^ s.val ≤
  T.q := by grw [T.five_le_P, ← pow_succ', q]; gcongr <;> grind

lemma excessWeight_mem_Icc : T.excessWeight i a a' x ∈ Set.Icc (-5⁻¹) 1 :=
  (unitInterval.div_mem (by simp) (by simp)
  (Nat.mono_cast (T.five_mul_P_pow_le_q (x.2 - i)))).elim (by simp [sub_div, ite_div]; grind)
