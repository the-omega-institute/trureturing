/- GID: D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.claim; result=D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.result; claim=D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.claim
   digest: Refute the truncated loss-dephasing entropy optimizer conjecture on a qutrit. -/

/-
proof_shape: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#11680; Refuted)
Direct frozen dependencies:
  D5/S3/Entropy/MaxEntropy.shannonEntropy (definition),
  statement_id: sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87;
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity (definition),
  statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Entropy.MaxEntropy
import D5.S3.Quantum.PureState.PureStateHandshake

open D5.S3.Quantum.PureState.PureStateHandshake


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open scoped BigOperators Matrix ComplexOrder

namespace D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation

private abbrev Index (K : ℕ) := Fin (K + 1)

private abbrev State (K : ℕ) := Matrix (Index K) (Index K) ℂ

private abbrev Ket (K : ℕ) := Index K → ℂ

noncomputable def amplitudeKraus {K : ℕ} (j : Index K) (f : ℝ) : State K :=
  Matrix.of fun r c =>
    if r.val + j.val = c.val then
      if j.val ≤ c.val then
        Complex.ofReal
          (Real.sqrt (Nat.choose c.val j.val) *
            (Real.sqrt (1 - f)) ^ (c.val - j.val) *
            (Real.sqrt f) ^ j.val)
      else 0
    else 0

noncomputable def phaseKraus {K : ℕ} (k : ℕ) (eta : ℝ) : State K :=
  Matrix.of fun r c =>
    if r = c then
      Complex.ofReal
        (Real.sqrt (((2 : ℝ) * (r.val : ℝ)^2 * eta) ^ k /
          (Nat.factorial k : ℝ)) *
          Real.exp (-((r.val : ℝ)^2 * eta)))
    else 0

private noncomputable def phaseClosedForm {K : ℕ} (eta : ℝ) (ρ : State K) : State K :=
  Matrix.of fun m n =>
    Complex.ofReal (Real.exp (-eta * ((m.val : ℝ) - n.val)^2)) * ρ m n

private noncomputable def phaseChannel {K : ℕ} (eta : ℝ) (ρ : State K) : State K :=
  ∑' k : ℕ, phaseKraus k eta * ρ * (phaseKraus k eta)ᴴ

noncomputable def lossDephasingChannel {K : ℕ} (ε t : ℝ) (ρ : State K) : State K :=
  let f := 1 - Real.exp (-2 * (1 - ε) * t)
  ∑ j : Index K, ∑' k : ℕ,
    (amplitudeKraus j f * phaseKraus k (ε*t)) * ρ *
      (amplitudeKraus j f * phaseKraus k (ε*t))ᴴ

noncomputable def numberOperator (K : ℕ) : State K :=
  Matrix.diagonal (fun i => (i.val : ℂ))

noncomputable def vonNeumannEntropy {K : ℕ} (ρ : State K) : ℝ :=
  if h : ρ.IsHermitian then
    D5.S3.Entropy.MaxEntropy.shannonEntropy h.eigenvalues
  else 0

def admissible {K : ℕ} (N : ℝ) (ρ : State K) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧
    (Matrix.trace (ρ * numberOperator K)).re = N

noncomputable def binomialKet {K : ℕ} (M : ℕ) (μ : ℝ) : Ket K :=
  fun i =>
    if i.val ≤ M then
      Complex.ofReal
        (Real.sqrt ((Nat.choose M i.val : ℝ) * μ ^ i.val * (1 - μ) ^ (M - i.val)))
    else 0

noncomputable def kappaKet (K : ℕ) (N α : ℝ) : Ket K :=
  fun i =>
    if i.val = 0 then
      Complex.ofReal (Real.sqrt (1 - N / K))
    else if i.val = K then
      Complex.ofReal (Real.sqrt (N / K)) *
        Complex.exp (Complex.I * (α * K : ℂ))
    else 0

def candidate (K : ℕ) (N : ℝ) (φ : Ket K) : Prop :=
  (∃ M : ℕ, 1 ≤ M ∧ M ≤ K ∧ ∃ μ : ℝ,
    0 ≤ μ ∧ μ ≤ 1 ∧ (M : ℝ) * μ = N ∧ φ = binomialKet M μ) ∨
    ∃ α : ℝ, φ = kappaKet K N α

def claim : Prop :=
  ∀ (K : ℕ) (N ε t : ℝ),
    1 ≤ K → 0 ≤ N → N ≤ K → 0 ≤ ε → ε ≤ 1 → 0 ≤ t →
      ∃ φ : Ket K, candidate K N φ ∧
        ∀ ρ : State K, admissible N ρ →
          vonNeumannEntropy (lossDephasingChannel ε t (rankOneDensity φ)) ≤
            vonNeumannEntropy (lossDephasingChannel ε t ρ)

private noncomputable def psiKet : Ket 2 := fun i =>
  if i.val = 1 then (1 / Real.sqrt 2 : ℂ)
  else if i.val = 2 then (1 / Real.sqrt 2 : ℂ) else 0

private noncomputable def expectedPsiOutput : State 2 :=
  !![3/8, 1/32, 0; 1/32, 1/2, (Real.sqrt 2 : ℂ)/64;
     0, (Real.sqrt 2 : ℂ)/64, 1/8]

private noncomputable def expectedBinomialOutput : State 2 :=
  !![25/64, (Real.sqrt 3 : ℂ)/128 + 3*(Real.sqrt 6 : ℂ)/256, 3/131072;
     (Real.sqrt 3 : ℂ)/128 + 3*(Real.sqrt 6 : ℂ)/256, 15/32, 3*(Real.sqrt 3 : ℂ)/256;
     3/131072, 3*(Real.sqrt 3 : ℂ)/256, 9/64]

private noncomputable def expectedKappaOutput : State 2 :=
  !![7/16, 0, (Real.sqrt 3 : ℂ)/32768;
     0, 3/8, 0;
     (Real.sqrt 3 : ℂ)/32768, 0, 3/16]
private noncomputable def kappaPhase (α : ℝ) : ℂ := Complex.exp (Complex.I*(α*2:ℂ))
private noncomputable def kappaRotation (α : ℝ) : State 2 :=
  Matrix.diagonal ![1,Complex.exp (Complex.I*(α:ℂ)),kappaPhase α]
open Matrix Unitary

/-- Conjecture 1 fails at K = 2, N = 3/2, epsilon = 6/7 and t = (7/2) log 2. -/
theorem result : ¬ claim := by
  have triple_entropy_lt {a b c x y z : ℝ}
      (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
      (ha : (1/8 : ℝ) < a ∧ a < 1/2)
      (hb : (1/8 : ℝ) < b ∧ b < 1/2)
      (hc : (1/8 : ℝ) < c ∧ c < 1/2)
      (hs1 : a+b+c=1) (hs2 : x+y+z=1)
      (hmax : (1/2 : ℝ) < max x (max y z))
      (hmin : min x (min y z) < (1/8 : ℝ)) :
      Real.negMulLog x + Real.negMulLog y + Real.negMulLog z <
        Real.negMulLog a + Real.negMulLog b + Real.negMulLog c := by
    have pair_entropy_le {u v p q : ℝ} (hu : 0 ≤ u) (huv : u < v)
        (hp : u ≤ p) (hpv : p ≤ v) (hs : p + q = u + v) :
        Real.negMulLog u + Real.negMulLog v ≤ Real.negMulLog p + Real.negMulLog q := by
      let a := (v-p)/(v-u)
      let b := (p-u)/(v-u)
      have hd : 0 < v-u := sub_pos.mpr huv
      have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hpv) hd.le
      have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hp) hd.le
      have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
      have hpa : a*u+b*v=p := by dsimp [a,b]; field_simp; ring
      have hqa : b*u+a*v=q := by dsimp [a,b]; field_simp; nlinarith [hs]
      have h1 := Real.concaveOn_negMulLog.2 hu (by linarith : 0 ≤ v) ha hb hab
      have h2 := Real.concaveOn_negMulLog.2 hu (by linarith : 0 ≤ v) hb ha (by linarith : b+a=1)
      simp only [smul_eq_mul, hpa, hqa] at h1 h2
      have hsum : (a * Real.negMulLog u + b * Real.negMulLog v) +
          (b * Real.negMulLog u + a * Real.negMulLog v) =
          Real.negMulLog u + Real.negMulLog v := by
        rw [show b=1-a by linarith]
        ring
      linarith
    have pair_entropy_lt {u v p q : ℝ} (hu : 0 ≤ u) (huv : u < v)
        (hp : u < p) (hpv : p < v) (hs : p + q = u + v) :
        Real.negMulLog u + Real.negMulLog v < Real.negMulLog p + Real.negMulLog q := by
      let a := (v-p)/(v-u)
      let b := (p-u)/(v-u)
      have hd : 0 < v-u := sub_pos.mpr huv
      have ha : 0 < a := div_pos (sub_pos.mpr hpv) hd
      have hb : 0 < b := div_pos (sub_pos.mpr hp) hd
      have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
      have hpa : a*u+b*v=p := by dsimp [a,b]; field_simp; ring
      have hqa : b*u+a*v=q := by dsimp [a,b]; field_simp; nlinarith [hs]
      have h1 := Real.strictConcaveOn_negMulLog.2 hu (by linarith : 0 ≤ v) (ne_of_lt huv) ha hb hab
      have h2 := Real.strictConcaveOn_negMulLog.2 hu (by linarith : 0 ≤ v) (ne_of_lt huv) hb ha (by linarith : b+a=1)
      simp only [smul_eq_mul, hpa, hqa] at h1 h2
      have hsum : (a * Real.negMulLog u + b * Real.negMulLog v) +
          (b * Real.negMulLog u + a * Real.negMulLog v) =
          Real.negMulLog u + Real.negMulLog v := by
        rw [show b=1-a by linarith]
        ring
      linarith
    have sorted_triple_entropy_lt {a b c x y z : ℝ}
        (hz : 0 ≤ z) (hxy : y ≤ x) (hyz : z ≤ y)
        (hab : b ≤ a) (hbc : c ≤ b) (hxa : a < x) (hzc : z < c)
        (hs : a+b+c=x+y+z) :
        Real.negMulLog x + Real.negMulLog y + Real.negMulLog z <
          Real.negMulLog a + Real.negMulLog b + Real.negMulLog c := by
      by_cases hya : y ≤ a
      · let u := x+y-a
        have h1 := pair_entropy_le (u:=y) (v:=x) (p:=a) (q:=u)
          (by linarith) (by linarith) hya hxa.le (by dsimp [u]; ring)
        have h2 := pair_entropy_lt (u:=z) (v:=u) (p:=b) (q:=c)
          hz (by dsimp [u]; linarith) (by linarith) (by dsimp [u]; linarith)
          (by dsimp [u]; linarith)
        linarith
      · let u := y+z-a
        have h1 := pair_entropy_le (u:=z) (v:=y) (p:=a) (q:=u)
          hz (by linarith) (by linarith) (by linarith) (by dsimp [u]; ring)
        have h2 := pair_entropy_lt (u:=u) (v:=x) (p:=b) (q:=c)
          (by dsimp [u]; linarith) (by dsimp [u]; linarith)
          (by dsimp [u]; linarith) (by linarith) (by dsimp [u]; linarith)
        linarith
    have triple_entropy_lt_of_sorted_outer {a b c x y z : ℝ}
        (hz : 0 ≤ z) (hxy : y ≤ x) (hyz : z ≤ y)
        (ha : z < a ∧ a < x) (hb : z < b ∧ b < x) (hc : z < c ∧ c < x)
        (hs : a+b+c=x+y+z) :
        Real.negMulLog x + Real.negMulLog y + Real.negMulLog z <
          Real.negMulLog a + Real.negMulLog b + Real.negMulLog c := by
      rcases le_total a b with hab | hab <;>
        rcases le_total b c with hbc | hbc <;>
        rcases le_total a c with hac | hac
      all_goals first
        | have h := sorted_triple_entropy_lt hz hxy hyz hbc hab hc.2 ha.1 (by linarith : c+b+a=x+y+z); linarith
        | have h := sorted_triple_entropy_lt hz hxy hyz hbc hac hb.2 ha.1 (by linarith : b+c+a=x+y+z); linarith
        | have h := sorted_triple_entropy_lt hz hxy hyz hac hab hc.2 hb.1 (by linarith : c+a+b=x+y+z); linarith
        | have h := sorted_triple_entropy_lt hz hxy hyz hac hbc ha.2 hb.1 (by linarith : a+c+b=x+y+z); linarith
        | have h := sorted_triple_entropy_lt hz hxy hyz hab hac hb.2 hc.1 (by linarith : b+a+c=x+y+z); linarith
        | have h := sorted_triple_entropy_lt hz hxy hyz hab hbc ha.2 hc.1 hs; linarith
        | linarith
    rcases le_total x y with hxy | hxy <;>
      rcases le_total y z with hyz | hyz <;>
      rcases le_total x z with hxz | hxz
    all_goals simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right,
      hxy, hyz, hxz] at hmax hmin
    all_goals first
      | have h := triple_entropy_lt_of_sorted_outer hx hyz hxy
          (by constructor <;> linarith) (by constructor <;> linarith)
          (by constructor <;> linarith) (by linarith : a+b+c=z+y+x); linarith
      | have h := triple_entropy_lt_of_sorted_outer hx hyz hxz
          (by constructor <;> linarith) (by constructor <;> linarith)
          (by constructor <;> linarith) (by linarith : a+b+c=y+z+x); linarith
      | have h := triple_entropy_lt_of_sorted_outer hy hxz hxy
          (by constructor <;> linarith) (by constructor <;> linarith)
          (by constructor <;> linarith) (by linarith : a+b+c=z+x+y); linarith
      | have h := triple_entropy_lt_of_sorted_outer hy hxz hyz
          (by constructor <;> linarith) (by constructor <;> linarith)
          (by constructor <;> linarith) (by linarith : a+b+c=x+z+y); linarith
      | have h := triple_entropy_lt_of_sorted_outer hz hxy hxz
          (by constructor <;> linarith) (by constructor <;> linarith)
          (by constructor <;> linarith) (by linarith : a+b+c=y+x+z); linarith
      | have h := triple_entropy_lt_of_sorted_outer hz hxy hyz
          (by constructor <;> linarith) (by constructor <;> linarith)
          (by constructor <;> linarith) (by linarith : a+b+c=x+y+z); linarith
      | linarith

  have ldl_posDef (a d e p q s : ℝ) (ha : 0 < a) (hd : 0 < d) (he : 0 < e) :
      ( !![(a:ℂ),p,q; p,(p^2/a+d:ℝ),(p*q/a+s:ℝ);
           q,(p*q/a+s:ℝ),(q^2/a+s^2/d+e:ℝ)] : Matrix (Fin 3) (Fin 3) ℂ).PosDef := by
    let L : Matrix (Fin 3) (Fin 3) ℂ :=
      !![1,0,0; (p/a:ℝ),1,0; (q/a:ℝ),(s/d:ℝ),1]
    have hL : IsUnit L := by
      apply (Matrix.isUnit_iff_isUnit_det L).mpr
      have hdet : L.det = 1 := by simp [L, Matrix.det_fin_three]
      rw [hdet]
      exact isUnit_one
    have hD : (Matrix.diagonal ![(a:ℂ),(d:ℂ),(e:ℂ)]).PosDef := by
      apply Matrix.posDef_diagonal_iff.mpr
      intro i
      fin_cases i <;> simp <;> exact_mod_cast (by assumption : (0:ℝ) < _)
    have hmatrix :
        ( !![(a:ℂ),p,q; p,(p^2/a+d:ℝ),(p*q/a+s:ℝ);
             q,(p*q/a+s:ℝ),(q^2/a+s^2/d+e:ℝ)] : Matrix (Fin 3) (Fin 3) ℂ) =
          L * Matrix.diagonal ![(a:ℂ),(d:ℂ),(e:ℂ)] * Lᴴ := by
      have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
      have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [L, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.diagonal_apply,
          Matrix.conjTranspose_apply, Complex.ofReal_div, Complex.ofReal_add,
          Complex.ofReal_mul, Complex.ofReal_pow]
      all_goals (try field_simp) <;> ring
    rw [hmatrix]
    exact hL.posDef_star_right_conjugate_iff.mpr hD

  have entropy_comparison {M : State 2} (hM : M.IsHermitian) (ht : Matrix.trace M=1)
      (hlo : (M-(1/8:ℂ) • (1:State 2)).PosDef)
      (hhi : ((1/2:ℂ) • (1:State 2)-M).PosDef) :
      vonNeumannEntropy expectedPsiOutput < vonNeumannEntropy M := by
    have expectedPsiOutput_isHermitian : expectedPsiOutput.IsHermitian := by
      rw [Matrix.IsHermitian.ext_iff]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [expectedPsiOutput, Complex.conj_ofReal]
    have symmetric_three_posDef (a b c p q r : ℝ)
        (ha : 0 < a) (hab : 0 < a*b-p^2)
        (hdet : 0 < a*b*c+2*p*q*r-a*r^2-b*q^2-c*p^2) :
        (!![(a:ℂ),p,q; p,b,r; q,r,c] : Matrix (Fin 3) (Fin 3) ℂ).PosDef := by
      let d := b-p^2/a
      let s := r-p*q/a
      let e := c-q^2/a-s^2/d
      have hdEq : d = (a*b-p^2)/a := by dsimp [d]; field_simp <;> ring
      have hd : 0 < d := hdEq ▸ div_pos hab ha
      have heEq : e = (a*b*c+2*p*q*r-a*r^2-b*q^2-c*p^2)/(a*b-p^2) := by
        dsimp [e,s]
        rw [hdEq]
        field_simp
        ring
      have he : 0 < e := heEq ▸ div_pos hdet hab
      have hm : (!![(a:ℂ),p,q; p,b,r; q,r,c] : Matrix (Fin 3) (Fin 3) ℂ) =
          !![(a:ℂ),p,q; p,(p^2/a+d:ℝ),(p*q/a+s:ℝ);
             q,(p*q/a+s:ℝ),(q^2/a+s^2/d+e:ℝ)] := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [d,s,e] <;> ring
      rw [hm]
      exact ldl_posDef a d e p q s ha hd he
    have psi_posDef : expectedPsiOutput.PosDef := by
      unfold expectedPsiOutput
      convert symmetric_three_posDef (3/8) (1/2) (1/8) (1/32) 0 (Real.sqrt 2/64)
        ?_ ?_ ?_ using 1
      · norm_num
      · norm_num
      · norm_num
      · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have shift_psd_upper {n : Type} [Fintype n] [DecidableEq n]
        {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ)
        (h : ∀ i, hM.eigenvalues i ≤ c) :
        ((c : ℂ) • (1 : Matrix n n ℂ) - M).PosSemidef := by
      let U := hM.eigenvectorUnitary
      have hd : (Matrix.diagonal (fun i => ((c-hM.eigenvalues i : ℝ) : ℂ))).PosSemidef := by
        apply Matrix.posSemidef_diagonal_iff.mpr
        intro i
        exact_mod_cast sub_nonneg.mpr (h i)
      have he : (c:ℂ) • (1 : Matrix n n ℂ) - M =
          (U : Matrix n n ℂ) * Matrix.diagonal (fun i => ((c-hM.eigenvalues i : ℝ):ℂ)) *
            (U : Matrix n n ℂ)ᴴ := by
        rw [show Matrix.diagonal (fun i => ((c-hM.eigenvalues i : ℝ):ℂ)) =
          (c:ℂ) • (1 : Matrix n n ℂ) - Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) by
            ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]; split_ifs <;> simp_all]
        simp only [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc]
        have hu := Unitary.coe_mul_star_self U
        have hm := hM.spectral_theorem
        simp only [conjStarAlgAut_apply] at hm
        change (U:Matrix n n ℂ) * (U:Matrix n n ℂ)ᴴ = 1 at hu
        change M = (U:Matrix n n ℂ) * Matrix.diagonal (fun i => (hM.eigenvalues i:ℂ)) *
          (U:Matrix n n ℂ)ᴴ at hm
        rw [hu, ← hm]
      rw [he]
      exact hd.mul_mul_conjTranspose_same _
    have shift_psd_lower {n : Type} [Fintype n] [DecidableEq n]
        {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ)
        (h : ∀ i, c ≤ hM.eigenvalues i) :
        (M - (c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
      let U := hM.eigenvectorUnitary
      have hd : (Matrix.diagonal (fun i => ((hM.eigenvalues i-c : ℝ) : ℂ))).PosSemidef := by
        apply Matrix.posSemidef_diagonal_iff.mpr
        intro i
        exact_mod_cast sub_nonneg.mpr (h i)
      have he : M - (c:ℂ) • (1 : Matrix n n ℂ) =
          (U : Matrix n n ℂ) * Matrix.diagonal (fun i => ((hM.eigenvalues i-c : ℝ):ℂ)) *
            (U : Matrix n n ℂ)ᴴ := by
        rw [show Matrix.diagonal (fun i => ((hM.eigenvalues i-c : ℝ):ℂ)) =
          Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) - (c:ℂ) • (1 : Matrix n n ℂ) by
            ext i j; simp [Matrix.diagonal_apply,Matrix.one_apply]; split_ifs <;> simp_all]
        simp only [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc]
        have hu := Unitary.coe_mul_star_self U
        have hm := hM.spectral_theorem
        simp only [conjStarAlgAut_apply] at hm
        change (U:Matrix n n ℂ) * (U:Matrix n n ℂ)ᴴ = 1 at hu
        change M = (U:Matrix n n ℂ) * Matrix.diagonal (fun i => (hM.eigenvalues i:ℂ)) *
          (U:Matrix n n ℂ)ᴴ at hm
        rw [hu, ← hm]
      rw [he]
      exact hd.mul_mul_conjTranspose_same _
    have eigenvalue_gt_of_quadratic {n : Type} [Fintype n] [DecidableEq n]
        {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) (v : n → ℂ)
        (hq : c * (star v ⬝ᵥ v).re < (star v ⬝ᵥ (M *ᵥ v)).re) :
        ∃ i, c < hM.eigenvalues i := by
      by_contra h
      push Not at h
      have hp := (shift_psd_upper hM c h).re_dotProduct_nonneg v
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul, map_sub, RCLike.re_eq_complex_re, Complex.re_ofReal_mul] at hp
      linarith
    have eigenvalue_lt_of_quadratic {n : Type} [Fintype n] [DecidableEq n]
        {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) (v : n → ℂ)
        (hq : (star v ⬝ᵥ (M *ᵥ v)).re < c * (star v ⬝ᵥ v).re) :
        ∃ i, hM.eigenvalues i < c := by
      by_contra h
      push Not at h
      have hp := (shift_psd_lower hM c h).re_dotProduct_nonneg v
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul, map_sub, RCLike.re_eq_complex_re, Complex.re_ofReal_mul] at hp
      linarith
    have eigenvector_quad_one {n : Type} [Fintype n] [DecidableEq n]
        {M : Matrix n n ℂ} (hM : M.IsHermitian) (i : n) :
        star ⇑(hM.eigenvectorBasis i) ⬝ᵥ ⇑(hM.eigenvectorBasis i) = (1:ℂ) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
      simp [hM.eigenvectorBasis.orthonormal.1 i]
    have eigenvalue_lt_of_posDef_shift {n : Type} [Fintype n] [DecidableEq n]
        {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ)
        (hp : ((c:ℂ) • (1 : Matrix n n ℂ) - M).PosDef) (i : n) :
        hM.eigenvalues i < c := by
      have hv : ⇑(hM.eigenvectorBasis i) ≠ 0 :=
        (WithLp.ofLp_eq_zero 2).ne.mpr (hM.eigenvectorBasis.orthonormal.ne_zero i)
      have hq := hp.re_dotProduct_pos hv
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, eigenvector_quad_one, smul_eq_mul,
        mul_one, map_sub, RCLike.re_eq_complex_re, Complex.ofReal_re] at hq
      have heq : (star ⇑(hM.eigenvectorBasis i) ⬝ᵥ (M *ᵥ ⇑(hM.eigenvectorBasis i))).re =
          hM.eigenvalues i := by simpa [RCLike.re_eq_complex_re] using (hM.eigenvalues_eq i).symm
      rw [heq] at hq
      linarith
    have eigenvalue_gt_of_posDef_shift {n : Type} [Fintype n] [DecidableEq n]
        {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ)
        (hp : (M - (c:ℂ) • (1 : Matrix n n ℂ)).PosDef) (i : n) :
        c < hM.eigenvalues i := by
      have hv : ⇑(hM.eigenvectorBasis i) ≠ 0 :=
        (WithLp.ofLp_eq_zero 2).ne.mpr (hM.eigenvectorBasis.orthonormal.ne_zero i)
      have hq := hp.re_dotProduct_pos hv
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, eigenvector_quad_one, smul_eq_mul,
        mul_one, map_sub, RCLike.re_eq_complex_re, Complex.ofReal_re] at hq
      have heq : (star ⇑(hM.eigenvectorBasis i) ⬝ᵥ (M *ᵥ ⇑(hM.eigenvectorBasis i))).re =
          hM.eigenvalues i := by simpa [RCLike.re_eq_complex_re] using (hM.eigenvalues_eq i).symm
      rw [heq] at hq
      linarith
    have psi_has_large_eigenvalue (hM : expectedPsiOutput.IsHermitian) :
        ∃ i, (1/2:ℝ) < hM.eigenvalues i := by
      apply eigenvalue_gt_of_quadratic hM (1/2) ![(1/4:ℂ),1,0]
      norm_num [expectedPsiOutput,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
        Matrix.cons_val_two,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,map_ofNat]
    have psi_has_small_eigenvalue (hM : expectedPsiOutput.IsHermitian) :
        ∃ i, hM.eigenvalues i < (1/8:ℝ) := by
      apply eigenvalue_lt_of_quadratic hM (1/8) ![(0:ℂ),-(Real.sqrt 2:ℂ)/16,1]
      norm_num [expectedPsiOutput,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
        Matrix.cons_val_two,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,map_ofNat,
        ←Complex.ofReal_pow]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have eigenvalue_sum_one {M : State 2} (hM : M.IsHermitian) (ht : Matrix.trace M=1) :
        hM.eigenvalues 0+hM.eigenvalues 1+hM.eigenvalues 2=1 := by
      have h := congrArg Complex.re hM.trace_eq_sum_eigenvalues
      rw [ht] at h
      simpa [Fin.sum_univ_succ,add_assoc,RCLike.re_eq_complex_re] using h.symm
    have vonNeumannEntropy_eq {K : ℕ} {M : State K} (hM : M.IsHermitian) :
        vonNeumannEntropy M = ∑ i, Real.negMulLog (hM.eigenvalues i) := by
      unfold vonNeumannEntropy D5.S3.Entropy.MaxEntropy.shannonEntropy
      rw [dif_pos hM]
    let hp := expectedPsiOutput_isHermitian
    have hs := eigenvalue_sum_one hp (by norm_num [expectedPsiOutput,Matrix.trace,Fin.sum_univ_succ,Matrix.cons_val_two])
    have hsM := eigenvalue_sum_one hM ht
    have hn (i) : 0 ≤ hp.eigenvalues i := psi_posDef.posSemidef.eigenvalues_nonneg i
    have hb (i) : (1/8:ℝ) < hM.eigenvalues i ∧ hM.eigenvalues i < (1/2:ℝ) :=
      ⟨eigenvalue_gt_of_posDef_shift hM (1/8) (by norm_num; exact hlo) i,
       eigenvalue_lt_of_posDef_shift hM (1/2) (by norm_num; exact hhi) i⟩
    have hmax : (1/2:ℝ) < max (hp.eigenvalues 0) (max (hp.eigenvalues 1) (hp.eigenvalues 2)) := by
      rcases psi_has_large_eigenvalue hp with ⟨i,hi⟩
      fin_cases i
      · exact lt_max_of_lt_left hi
      · exact lt_max_of_lt_right (lt_max_of_lt_left hi)
      · have hf : (⟨2, by decide⟩:Fin 3)=2 := by decide
        rw [hf] at hi
        exact lt_max_of_lt_right (lt_max_of_lt_right hi)
    have hmin : min (hp.eigenvalues 0) (min (hp.eigenvalues 1) (hp.eigenvalues 2)) < (1/8:ℝ) := by
      rcases psi_has_small_eigenvalue hp with ⟨i,hi⟩
      fin_cases i
      · exact min_lt_of_left_lt hi
      · exact min_lt_of_right_lt (min_lt_of_left_lt hi)
      · have hf : (⟨2, by decide⟩:Fin 3)=2 := by decide
        rw [hf] at hi
        exact min_lt_of_right_lt (min_lt_of_right_lt hi)
    have h := triple_entropy_lt (hn 0) (hn 1) (hn 2) (hb 0) (hb 1) (hb 2)
      hsM hs hmax hmin
    rw [vonNeumannEntropy_eq hp,vonNeumannEntropy_eq hM]
    change (∑ i:Fin 3,Real.negMulLog (hp.eigenvalues i)) <
      ∑ i:Fin 3,Real.negMulLog (hM.eigenvalues i)
    simpa only [Fin.sum_univ_three] using h

  have expectedBinomialOutput_isHermitian : expectedBinomialOutput.IsHermitian := by
    rw [Matrix.IsHermitian.ext_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [expectedBinomialOutput, Complex.conj_ofReal]
  have expectedKappaOutput_isHermitian : expectedKappaOutput.IsHermitian := by
    rw [Matrix.IsHermitian.ext_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [expectedKappaOutput, Complex.conj_ofReal]
  have witness_exp_eps_t : Real.exp (-((6/7 : ℝ) * ((7/2 : ℝ) * Real.log 2))) = (1/8 : ℝ) := by
    rw [show -((6/7 : ℝ) * ((7/2 : ℝ) * Real.log 2)) = -(3 * Real.log 2) by ring]
    rw [Real.exp_neg]
    have hlog : (3 : ℝ) * Real.log 2 = Real.log (2 ^ 3) := by
      rw [Real.log_pow]
      norm_num
    rw [hlog, Real.exp_log (by norm_num : (0:ℝ) < 2 ^ 3)]
    norm_num
  have witness_f : 1 - Real.exp (-2 * (1 - (6/7 : ℝ)) * ((7/2 : ℝ) * Real.log 2)) = (1/2 : ℝ) := by
    rw [show -2 * (1 - (6/7 : ℝ)) * ((7/2 : ℝ) * Real.log 2) = -(Real.log 2) by ring]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  have witness_phase_four :
      Real.exp (-((6/7 : ℝ) * ((7/2 : ℝ) * Real.log 2)) * (4 : ℝ)) = (1/4096 : ℝ) := by
    rw [show -((6/7 : ℝ) * ((7/2 : ℝ) * Real.log 2)) * (4 : ℝ) = -(12 * Real.log 2) by ring]
    rw [Real.exp_neg]
    have hlog : (12 : ℝ) * Real.log 2 = Real.log (2 ^ 12) := by
      rw [Real.log_pow]
      norm_num
    rw [hlog, Real.exp_log (by norm_num : (0:ℝ) < 2 ^ 12)]
    norm_num
  have psi_rankOneDensity_matrix :
      rankOneDensity psiKet = !![0, 0, 0; 0, 1/2, 1/2; 0, 1/2, 1/2] := by
    have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply, psiKet, Complex.conj_ofReal]
    all_goals apply Complex.ext <;> norm_num [hs] <;> field_simp <;> nlinarith [hs]
  have psi_energy : (Matrix.trace (rankOneDensity psiKet * numberOperator 2)).re = (3/2 : ℝ) := by
    rw [psi_rankOneDensity_matrix]
    norm_num [Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      numberOperator, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne,
      Fin.sum_univ_succ]
    simp [Matrix.diagonal_apply_ne]
    norm_num
  have dephasing_series (eta m n : ℝ) :
      HasSum (fun k : ℕ => (2*eta*m*n)^k/(k.factorial : ℝ) *
        Real.exp (-eta*(m^2+n^2))) (Real.exp (-eta*(m-n)^2)) := by
    have hexp : HasSum (fun k : ℕ => (2*eta*m*n)^k/(k.factorial : ℝ))
        (Real.exp (2*eta*m*n)) := by
      simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (2*eta*m*n))
    have h := hexp.mul_right (Real.exp (-eta*(m^2+n^2)))
    have he : Real.exp (2*eta*m*n) * Real.exp (-eta*(m^2+n^2)) =
        Real.exp (-eta*(m-n)^2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at h
    exact h
  have sqrt_phase_product (eta m n : ℝ) (he : 0 ≤ eta) (hm : 0 ≤ m) (hn : 0 ≤ n) (k : ℕ) :
      Real.sqrt ((2*m^2*eta)^k/(k.factorial : ℝ)) *
        Real.sqrt ((2*n^2*eta)^k/(k.factorial : ℝ)) =
        (2*eta*m*n)^k/(k.factorial : ℝ) := by
    have h1 : 0 ≤ (2*m^2*eta)^k/(k.factorial : ℝ) :=
      div_nonneg (pow_nonneg (by positivity) _) (by positivity)
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    rw [← Real.sqrt_mul h1]
    have hs : (2*m^2*eta)^k/(k.factorial : ℝ) *
        ((2*n^2*eta)^k/(k.factorial : ℝ)) =
        ((2*eta*m*n)^k/(k.factorial : ℝ))^2 := by
      rw [div_mul_div_comm, ← mul_pow, div_pow]
      rw [show 2*m^2*eta*(2*n^2*eta)=(2*eta*m*n)^2 by ring]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
      rw [sq]
    rw [hs, Real.sqrt_sq (by positivity)]
  have phaseKraus_eq_diagonal {K : ℕ} (k : ℕ) (eta : ℝ) :
      phaseKraus (K:=K) k eta = Matrix.diagonal (fun r : Index K =>
        ((Real.sqrt ((2*(r.val : ℝ)^2*eta)^k/(k.factorial : ℝ)) *
          Real.exp (-(r.val : ℝ)^2*eta) : ℝ) : ℂ)) := by
    ext r c
    simp [phaseKraus, Matrix.diagonal_apply]
  have phaseKraus_entry {K : ℕ} (k : ℕ) (eta : ℝ) (he : 0 ≤ eta)
      (ρ : State K) (m n : Index K) :
      (phaseKraus (K:=K) k eta * ρ * (phaseKraus (K:=K) k eta)ᴴ) m n =
        (((2*eta*(m.val : ℝ)*(n.val : ℝ))^k/(k.factorial : ℝ) *
          Real.exp (-eta*((m.val : ℝ)^2+(n.val : ℝ)^2)) : ℝ) : ℂ) * ρ m n := by
    simp only [phaseKraus_eq_diagonal, Matrix.diagonal_conjTranspose,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    change ((Real.sqrt ((2*(m.val:ℝ)^2*eta)^k/(k.factorial:ℝ)) *
        Real.exp (-(m.val:ℝ)^2*eta) : ℝ) : ℂ) * ρ m n *
        star (((Real.sqrt ((2*(n.val:ℝ)^2*eta)^k/(k.factorial:ℝ)) *
        Real.exp (-(n.val:ℝ)^2*eta) : ℝ) : ℂ)) = _
    simp only [Complex.star_def, Complex.conj_ofReal]
    have hp := sqrt_phase_product eta (m.val : ℝ) (n.val : ℝ) he
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) k
    have heq : Real.exp (-(m.val : ℝ)^2*eta) * Real.exp (-(n.val : ℝ)^2*eta) =
        Real.exp (-eta*((m.val : ℝ)^2+(n.val : ℝ)^2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hp' := congrArg Complex.ofReal hp
    have heq' := congrArg Complex.ofReal heq
    simp only [Complex.ofReal_mul] at hp' heq' ⊢
    calc
      _ = ((Real.sqrt ((2*(m.val:ℝ)^2*eta)^k/(k.factorial:ℝ)) : ℂ) *
          (Real.sqrt ((2*(n.val:ℝ)^2*eta)^k/(k.factorial:ℝ)) : ℂ)) *
          ((Real.exp (-(m.val:ℝ)^2*eta) : ℂ) *
          (Real.exp (-(n.val:ℝ)^2*eta) : ℂ)) * ρ m n := by ring
      _ = _ := by rw [hp',heq']
  have phaseChannel_eq_closedForm {K : ℕ} (eta : ℝ) (he : 0 ≤ eta) (ρ : State K) :
      phaseChannel eta ρ = phaseClosedForm eta ρ := by
    apply HasSum.tsum_eq
    apply Pi.hasSum.mpr
    intro m
    apply Pi.hasSum.mpr
    intro n
    simp only [phaseClosedForm, Matrix.of_apply]
    have h := (Complex.hasSum_ofReal.mpr
      (dephasing_series eta (m.val:ℝ) (n.val:ℝ))).mul_right (ρ m n)
    simpa only [phaseKraus_entry _ _ he] using h
  have phaseKraus_hasSum {K : ℕ} (eta : ℝ) (he : 0 ≤ eta) (ρ : State K) :
      HasSum (fun k : ℕ => phaseKraus k eta * ρ * (phaseKraus k eta)ᴴ)
        (phaseChannel eta ρ) := by
    rw [phaseChannel_eq_closedForm eta he ρ]
    apply Pi.hasSum.mpr
    intro m
    apply Pi.hasSum.mpr
    intro n
    simp only [phaseClosedForm, Matrix.of_apply]
    have h := (Complex.hasSum_ofReal.mpr
      (dephasing_series eta (m.val:ℝ) (n.val:ℝ))).mul_right (ρ m n)
    simpa only [phaseKraus_entry _ _ he] using h
  have lossDephasingChannel_composed {K : ℕ} (ε t : ℝ) (he : 0 ≤ ε*t) (ρ : State K) :
      lossDephasingChannel ε t ρ =
        ∑ j : Index K, amplitudeKraus j (1-Real.exp (-2*(1-ε)*t)) *
          phaseChannel (ε*t) ρ * (amplitudeKraus j (1-Real.exp (-2*(1-ε)*t)))ᴴ := by
    unfold lossDephasingChannel
    apply Finset.sum_congr rfl
    intro j hj
    have h := ((phaseKraus_hasSum (ε*t) he ρ).mul_left
      (amplitudeKraus j (1-Real.exp (-2*(1-ε)*t)))).mul_right
      (amplitudeKraus j (1-Real.exp (-2*(1-ε)*t)))ᴴ
    convert h.tsum_eq using 1
    simp only [Matrix.conjTranspose_mul, mul_assoc]
  have sqrt_half : Real.sqrt (1/2 : ℝ) = Real.sqrt 2 / 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)
    have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hp := Real.sqrt_nonneg (1/2 : ℝ)
    have hp2 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have sqrt_two_sq_complex : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have sqrt_two_inv_complex : (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ)/2 := by
    apply inv_eq_of_mul_eq_one_right
    ring_nf
    rw [sqrt_two_sq_complex]
    norm_num
  have amplitude_half_zero : amplitudeKraus (K:=2) 0 (1/2) =
      !![1,0,0; 0,(Real.sqrt 2:ℂ)/2,0; 0,0,1/2] := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      norm_num [amplitudeKraus, sqrt_half, pow_two,
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2),
        Complex.ofReal_mul, Complex.ofReal_inv, sqrt_two_inv_complex]
    all_goals ring_nf
    all_goals rw [sqrt_two_sq_complex] <;> norm_num
  have amplitude_half_one : amplitudeKraus (K:=2) 1 (1/2) =
      !![0,(Real.sqrt 2:ℂ)/2,0; 0,0,(Real.sqrt 2:ℂ)/2; 0,0,0] := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      norm_num [amplitudeKraus, sqrt_half, pow_two]
    all_goals try simp only [Complex.ofReal_mul, Complex.ofReal_inv, sqrt_two_inv_complex]
    all_goals ring_nf
    all_goals rw [sqrt_two_sq_complex] <;> norm_num
  have amplitude_half_two : amplitudeKraus (K:=2) 2 (1/2) =
      !![0,0,1/2; 0,0,0; 0,0,0] := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      norm_num [amplitudeKraus, sqrt_half, pow_two,
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2),
        Complex.ofReal_mul, Complex.ofReal_inv, sqrt_two_inv_complex]
    all_goals ring_nf
    all_goals rw [sqrt_two_sq_complex] <;> norm_num
  have amplitude_half_entries (σ : State 2) :
      (∑ j : Fin 3, amplitudeKraus j (1/2) * σ * (amplitudeKraus j (1/2))ᴴ) =
        !![σ 0 0 + σ 1 1/2 + σ 2 2/4,
            (Real.sqrt 2:ℂ)/2 * σ 0 1 + σ 1 2/2, σ 0 2/2;
           (Real.sqrt 2:ℂ)/2 * σ 1 0 + σ 2 1/2,
            σ 1 1/2 + σ 2 2/2, (Real.sqrt 2:ℂ)/4 * σ 1 2;
           σ 2 0/2, (Real.sqrt 2:ℂ)/4 * σ 2 1, σ 2 2/4] := by
    change Fin 3 → Fin 3 → ℂ at σ
    have hf2 : (⟨2, by decide⟩ : Fin 3)=2 := by decide
    rw [Fin.sum_univ_three]
    rw [amplitude_half_zero, amplitude_half_one, amplitude_half_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]
    all_goals norm_num [Matrix.cons_val_two, hf2, Fin.sum_univ_succ]
    all_goals ring_nf
    all_goals (try simp only [sqrt_two_sq_complex]; ring)
  have witness_phase_matrix (ρ : State 2) :
      phaseChannel ((6/7 : ℝ)*((7/2 : ℝ)*Real.log 2)) ρ =
        !![ρ 0 0, ρ 0 1/8, ρ 0 2/4096;
           ρ 1 0/8, ρ 1 1, ρ 1 2/8;
           ρ 2 0/4096, ρ 2 1/8, ρ 2 2] := by
    change Fin 3 → Fin 3 → ℂ at ρ
    have hf2 : (⟨2, by decide⟩ : Fin 3)=2 := by decide
    rw [phaseChannel_eq_closedForm _ (by positivity)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [phaseClosedForm, -Complex.ofReal_exp, Matrix.cons_val_two, hf2]
    all_goals ring_nf
    all_goals first
      | rfl
      | (have h3 : Real.exp (-(Real.log 2 * 3)) = (1/8:ℝ) := by
           convert witness_exp_eps_t using 1 <;> congr 1 <;> ring
         rw [h3]; norm_num; (try simp only [hf2]); ring)
      | (have h12 : Real.exp (-(Real.log 2 * 12)) = (1/4096:ℝ) := by
           convert witness_phase_four using 1 <;> congr 1 <;> ring
         rw [h12]; norm_num; (try simp only [hf2]); ring)
  have witness_channel_matrix (ρ : State 2) :
      lossDephasingChannel (6/7) ((7/2)*Real.log 2) ρ =
        !![ρ 0 0+ρ 1 1/2+ρ 2 2/4,
            (Real.sqrt 2:ℂ)/16*ρ 0 1+ρ 1 2/16,ρ 0 2/8192;
           (Real.sqrt 2:ℂ)/16*ρ 1 0+ρ 2 1/16,
            ρ 1 1/2+ρ 2 2/2,(Real.sqrt 2:ℂ)/32*ρ 1 2;
           ρ 2 0/8192,(Real.sqrt 2:ℂ)/32*ρ 2 1,ρ 2 2/4] := by
    rw [lossDephasingChannel_composed _ _ (by positivity)]
    rw [witness_f, amplitude_half_entries, witness_phase_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  have psi_output : lossDephasingChannel (6/7) ((7/2)*Real.log 2) (rankOneDensity psiKet) =
      expectedPsiOutput := by
    rw [witness_channel_matrix, psi_rankOneDensity_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [expectedPsiOutput, Matrix.cons_val_two] <;> ring
  have sqrt_three_eighths : Real.sqrt (3/8:ℝ) = Real.sqrt 6/4 := by
    have h1 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/8)
    have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
    nlinarith [Real.sqrt_nonneg (3/8:ℝ),Real.sqrt_nonneg 6]
  have sqrt_three_quarters : Real.sqrt (3/4:ℝ) = Real.sqrt 3/2 := by
    have h1 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/4)
    have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg (3/4:ℝ),Real.sqrt_nonneg 3]
  have binomial_witness_ket : binomialKet (K:=2) 2 (3/4) =
      ![(1/4:ℂ),(Real.sqrt 6:ℂ)/4,3/4] := by
    ext i
    fin_cases i <;> norm_num [binomialKet, Matrix.cons_val_two, sqrt_three_eighths, -Real.sqrt_div, -Real.sqrt_div', -Real.sqrt_inv]
  have binomial_rankOneDensity_matrix : rankOneDensity (binomialKet (K:=2) 2 (3/4)) =
      !![1/16,(Real.sqrt 6:ℂ)/16,3/16;
         (Real.sqrt 6:ℂ)/16,3/8,3*(Real.sqrt 6:ℂ)/16;
         3/16,3*(Real.sqrt 6:ℂ)/16,9/16] := by
    rw [binomial_witness_ket]
    have h6 : (Real.sqrt 6:ℂ)^2 = 6 := by norm_cast; exact Real.sq_sqrt (by norm_num)
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply,Matrix.cons_val_two,Complex.conj_ofNat]
    all_goals ring_nf
    all_goals (try rw [h6]); norm_num
  have sqrt_two_six : Real.sqrt 2 * Real.sqrt 6 = 2*Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (2:ℝ)*6=(2:ℝ)^2*3 by norm_num,
      Real.sqrt_mul (by positivity),Real.sqrt_sq (by norm_num)]
  have binomial_output :
      lossDephasingChannel (6/7) ((7/2)*Real.log 2) (rankOneDensity (binomialKet (K:=2) 2 (3/4))) =
        expectedBinomialOutput := by
    rw [witness_channel_matrix,binomial_rankOneDensity_matrix]
    have h26 : (Real.sqrt 2:ℂ)*(Real.sqrt 6:ℂ) = 2*(Real.sqrt 3:ℂ) := by
      exact_mod_cast sqrt_two_six
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [expectedBinomialOutput,Matrix.cons_val_two]
    all_goals ring_nf
    all_goals (try simp only [h26]); ring
  have kappa_witness_ket (α : ℝ) : kappaKet 2 (3/2) α =
      ![(1/2:ℂ),0,(Real.sqrt 3:ℂ)/2*kappaPhase α] := by
    ext i
    fin_cases i <;> norm_num [kappaKet,kappaPhase,Matrix.cons_val_two,sqrt_three_quarters, -Real.sqrt_div, -Real.sqrt_div', -Real.sqrt_inv]
  have kappaPhase_mul_star (α : ℝ) : kappaPhase α * star (kappaPhase α) = 1 := by
    unfold kappaPhase
    rw [Complex.star_def,←Complex.exp_conj,←Complex.exp_add]
    have h : Complex.I*(α*2:ℂ)+starRingEnd ℂ (Complex.I*(α*2:ℂ))=0 := by simp [Complex.conj_ofNat]
    rw [h,Complex.exp_zero]
  have kappa_rankOneDensity_matrix (α : ℝ) : rankOneDensity (kappaKet 2 (3/2) α) =
      !![1/4,0,(Real.sqrt 3:ℂ)/4*star (kappaPhase α);
         0,0,0;
         (Real.sqrt 3:ℂ)/4*kappaPhase α,0,3/4] := by
    rw [kappa_witness_ket]
    have h3 : (Real.sqrt 3:ℂ)^2=3 := by norm_cast; exact Real.sq_sqrt (by norm_num)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply,Matrix.cons_val_two,Complex.conj_ofNat]
    all_goals (try ring_nf)
    all_goals (try simp only [h3,starRingEnd_apply])
    all_goals (try ring_nf)
    all_goals first | rfl | (rw [kappaPhase_mul_star]; norm_num) | ring
  have kappa_output_matrix (α : ℝ) :
      lossDephasingChannel (6/7) ((7/2)*Real.log 2) (rankOneDensity (kappaKet 2 (3/2) α)) =
        !![7/16,0,(Real.sqrt 3:ℂ)/32768*star (kappaPhase α);
           0,3/8,0;
           (Real.sqrt 3:ℂ)/32768*kappaPhase α,0,3/16] := by
    rw [witness_channel_matrix,kappa_rankOneDensity_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.cons_val_two] <;> ring
  have kappaRotation_unitary (α : ℝ) : kappaRotation α ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    change kappaRotation α * (kappaRotation α)ᴴ = 1
    unfold kappaRotation
    rw [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply,Matrix.one_apply,Matrix.cons_val_two,kappaPhase_mul_star]
    all_goals first
      | exact kappaPhase_mul_star α
      | (rw [←Complex.exp_conj,←Complex.exp_add]; simp)
  have kappa_output_covariance (α : ℝ) :
      lossDephasingChannel (6/7) ((7/2)*Real.log 2) (rankOneDensity (kappaKet 2 (3/2) α)) =
        kappaRotation α * expectedKappaOutput * (kappaRotation α)ᴴ := by
    rw [kappa_output_matrix]
    have hz : Complex.exp (Complex.I*(α:ℂ)) * star (Complex.exp (Complex.I*(α:ℂ))) = 1 := by
      rw [Complex.star_def,←Complex.exp_conj,←Complex.exp_add]
      simp
    ext i j
    simp only [kappaRotation,Matrix.diagonal_conjTranspose,Matrix.mul_diagonal,Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;> norm_num [expectedKappaOutput,Matrix.cons_val_two]
    all_goals (try ring_nf)
    all_goals (try simp only [kappaPhase_mul_star,starRingEnd_apply,hz])
    all_goals first | rfl | (rw [kappaPhase_mul_star]; norm_num) | (rw [hz]; norm_num) | ring
  have symmetric_three_posDef (a b c p q r : ℝ)
      (ha : 0 < a) (hab : 0 < a*b-p^2)
      (hdet : 0 < a*b*c+2*p*q*r-a*r^2-b*q^2-c*p^2) :
      (!![(a:ℂ),p,q; p,b,r; q,r,c] : Matrix (Fin 3) (Fin 3) ℂ).PosDef := by
    let d := b-p^2/a
    let s := r-p*q/a
    let e := c-q^2/a-s^2/d
    have hdEq : d = (a*b-p^2)/a := by dsimp [d]; field_simp <;> ring
    have hd : 0 < d := hdEq ▸ div_pos hab ha
    have heEq : e = (a*b*c+2*p*q*r-a*r^2-b*q^2-c*p^2)/(a*b-p^2) := by
      dsimp [e,s]
      rw [hdEq]
      field_simp
      ring
    have he : 0 < e := heEq ▸ div_pos hdet hab
    have hm : (!![(a:ℂ),p,q; p,b,r; q,r,c] : Matrix (Fin 3) (Fin 3) ℂ) =
        !![(a:ℂ),p,q; p,(p^2/a+d:ℝ),(p*q/a+s:ℝ);
           q,(p*q/a+s:ℝ),(q^2/a+s^2/d+e:ℝ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [d,s,e] <;> ring
    rw [hm]
    exact ldl_posDef a d e p q s ha hd he
  have radical_identities : (Real.sqrt 3)^2=3 ∧ (Real.sqrt 6)^2=6 ∧
      Real.sqrt 3 * Real.sqrt 6 = 3*Real.sqrt 2 := by
    refine ⟨Real.sq_sqrt (by norm_num),Real.sq_sqrt (by norm_num),?_⟩
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    have h : (18:ℝ) = 3^2*2 := by norm_num
    rw [show (3:ℝ)*6=18 by norm_num,h,Real.sqrt_mul (by positivity),Real.sqrt_sq (by norm_num)]
  have binomial_lower_posDef :
      (expectedBinomialOutput - (1/8:ℂ) • (1:State 2)).PosDef := by
    have hm : expectedBinomialOutput - (1/8:ℂ) • (1:State 2) =
        !![(17/64:ℂ),(Real.sqrt 3:ℂ)/128+3*(Real.sqrt 6:ℂ)/256,3/131072;
           (Real.sqrt 3:ℂ)/128+3*(Real.sqrt 6:ℂ)/256,11/32,3*(Real.sqrt 3:ℂ)/256;
           3/131072,3*(Real.sqrt 3:ℂ)/256,1/64] := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [expectedBinomialOutput,Matrix.one_apply] <;> ring
    rw [hm]
    convert symmetric_three_posDef (17/64) (11/32) (1/64)
      (Real.sqrt 3/128+3*Real.sqrt 6/256) (3/131072) (3*Real.sqrt 3/256)
      ?_ ?_ ?_ using 1
    · norm_num
    · have h := radical_identities
      have ht : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
      nlinarith [h.1,h.2.1,h.2.2]
    · have h := radical_identities
      have ht : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
      nlinarith [h.1,h.2.1,h.2.2]
    · have h := radical_identities
      have ht : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
      nlinarith [h.1,h.2.1,h.2.2]
  have binomial_upper_posDef :
      ((1/2:ℂ) • (1:State 2)-expectedBinomialOutput).PosDef := by
    have hm : (1/2:ℂ) • (1:State 2)-expectedBinomialOutput =
        !![(7/64:ℂ),-((Real.sqrt 3:ℂ)/128+3*(Real.sqrt 6:ℂ)/256),-3/131072;
           -((Real.sqrt 3:ℂ)/128+3*(Real.sqrt 6:ℂ)/256),1/32,-3*(Real.sqrt 3:ℂ)/256;
           -3/131072,-3*(Real.sqrt 3:ℂ)/256,23/64] := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [expectedBinomialOutput,Matrix.one_apply] <;> ring
    rw [hm]
    convert symmetric_three_posDef (7/64) (1/32) (23/64)
      (-(Real.sqrt 3/128+3*Real.sqrt 6/256)) (-3/131072) (-3*Real.sqrt 3/256)
      ?_ ?_ ?_ using 1
    · norm_num
    · have h := radical_identities
      have ht : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
      nlinarith [h.1,h.2.1,h.2.2]
    · have h := radical_identities
      have ht : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
      nlinarith [h.1,h.2.1,h.2.2]
    · have h := radical_identities
      have ht : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
      nlinarith [h.1,h.2.1,h.2.2]
  have kappa_lower_posDef : (expectedKappaOutput - (1/8:ℂ) • (1:State 2)).PosDef := by
    have hm : expectedKappaOutput - (1/8:ℂ) • (1:State 2) =
        !![(5/16:ℂ),0,(Real.sqrt 3:ℂ)/32768;0,1/4,0;(Real.sqrt 3:ℂ)/32768,0,1/16] := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [expectedKappaOutput,Matrix.one_apply] <;> ring
    rw [hm]
    convert symmetric_three_posDef (5/16) (1/4) (1/16) 0 (Real.sqrt 3/32768) 0
      ?_ ?_ ?_ using 1
    · norm_num
    · norm_num
    · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have kappa_upper_posDef : ((1/2:ℂ) • (1:State 2)-expectedKappaOutput).PosDef := by
    have hm : (1/2:ℂ) • (1:State 2)-expectedKappaOutput =
        !![(1/16:ℂ),0,-(Real.sqrt 3:ℂ)/32768;0,1/8,0;-(Real.sqrt 3:ℂ)/32768,0,5/16] := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [expectedKappaOutput,Matrix.one_apply] <;> ring
    rw [hm]
    convert symmetric_three_posDef (1/16) (1/8) (5/16) 0 (-Real.sqrt 3/32768) 0
      ?_ ?_ ?_ using 1
    · norm_num
    · norm_num
    · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have psi_admissible : admissible (3/2) (rankOneDensity psiKet) := by
    refine ⟨?_,?_,psi_energy⟩
    · exact Matrix.posSemidef_vecMulVec_self_star psiKet
    · rw [psi_rankOneDensity_matrix]
      norm_num [Matrix.trace,Fin.sum_univ_succ,Matrix.cons_val_two]
  have binomial_entropy_gt :
      vonNeumannEntropy (lossDephasingChannel (6/7) ((7/2)*Real.log 2) (rankOneDensity psiKet)) <
        vonNeumannEntropy (lossDephasingChannel (6/7) ((7/2)*Real.log 2)
          (rankOneDensity (binomialKet (K:=2) 2 (3/4)))) := by
    rw [psi_output,binomial_output]
    apply entropy_comparison expectedBinomialOutput_isHermitian
      (by norm_num [expectedBinomialOutput,Matrix.trace,Fin.sum_univ_succ,Matrix.cons_val_two])
      binomial_lower_posDef binomial_upper_posDef
  have conjugate_bounds (U : Matrix.unitaryGroup (Fin 3) ℂ) {M : State 2}
      (hM : M.IsHermitian) (ht : Matrix.trace M=1)
      (hlo : (M-(1/8:ℂ) • (1:State 2)).PosDef)
      (hhi : ((1/2:ℂ) • (1:State 2)-M).PosDef) :
      ((U:State 2)*M*(U:State 2)ᴴ).IsHermitian ∧
      Matrix.trace ((U:State 2)*M*(U:State 2)ᴴ)=1 ∧
      (((U:State 2)*M*(U:State 2)ᴴ)-(1/8:ℂ) • (1:State 2)).PosDef ∧
      ((1/2:ℂ) • (1:State 2)-((U:State 2)*M*(U:State 2)ᴴ)).PosDef := by
    have hu : (U:State 2)*(U:State 2)ᴴ=1 := Unitary.coe_mul_star_self U
    have hu' : (U:State 2)ᴴ*(U:State 2)=1 := Unitary.coe_star_mul_self U
    refine ⟨Matrix.isHermitian_mul_mul_conjTranspose _ hM,?_,?_,?_⟩
    · rw [Matrix.trace_mul_cycle,hu',Matrix.one_mul,ht]
    · have h := (Unitary.isUnit_coe (U:=U)).posDef_star_right_conjugate_iff.mpr hlo
      change (((U:State 2) * _ * (U:State 2)ᴴ)).PosDef at h
      simpa [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,hu] using h
    · have h := (Unitary.isUnit_coe (U:=U)).posDef_star_right_conjugate_iff.mpr hhi
      change (((U:State 2) * _ * (U:State 2)ᴴ)).PosDef at h
      simpa [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,hu] using h
  have kappa_entropy_gt (α : ℝ) :
      vonNeumannEntropy (lossDephasingChannel (6/7) ((7/2)*Real.log 2) (rankOneDensity psiKet)) <
        vonNeumannEntropy (lossDephasingChannel (6/7) ((7/2)*Real.log 2) (rankOneDensity (kappaKet 2 (3/2) α))) := by
    rw [psi_output,kappa_output_covariance]
    let U : Matrix.unitaryGroup (Fin 3) ℂ := ⟨kappaRotation α,kappaRotation_unitary α⟩
    have h := conjugate_bounds U expectedKappaOutput_isHermitian
      (by norm_num [expectedKappaOutput,Matrix.trace,Fin.sum_univ_succ,Matrix.cons_val_two])
      kappa_lower_posDef kappa_upper_posDef
    exact entropy_comparison h.1 h.2.1 h.2.2.1 h.2.2.2
  intro hc
  have ht : 0 ≤ (7/2:ℝ)*Real.log 2 := by positivity
  obtain ⟨φ,hφ,hopt⟩ := hc 2 (3/2) (6/7) ((7/2)*Real.log 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht
  have hle := hopt (rankOneDensity psiKet) psi_admissible
  rcases hφ with hb | hk
  · rcases hb with ⟨M,hM1,hM2,μ,hμ0,hμ1,hE,hφ⟩
    have hM : M=2 := by
      have hcases : M=1 ∨ M=2 := by omega
      rcases hcases with h | h
      · subst M
        norm_num at hE
        linarith
      · exact h
    subst M
    have hμ : μ=3/4 := by norm_num at hE; linarith
    subst μ
    rw [hφ] at hle
    exact (not_le_of_gt binomial_entropy_gt) hle
  · rcases hk with ⟨α,hφ⟩
    rw [hφ] at hle
    exact (not_le_of_gt (kappa_entropy_gt α)) hle


end D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
