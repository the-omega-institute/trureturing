/- GID: D5/S3/Quantum/Entanglement/SectorChannels/UniformBinarySchmidtOverlap
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorChannels/UniformBinarySchmidtOverlap
   mirror-E: none(waiver:exact-uniform-binary-overlap)
   anchors: []
   utility: none
   digest: The exact largest matched Born overlap-to-score ratio at two labels holds at arbitrary finite Schmidt rank and is attained at rank two. -/

import D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace D5.S3.Quantum.Entanglement.SectorChannels.UniformBinarySchmidtOverlap
open scoped BigOperators ComplexConjugate
open D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap.RTOverlap

namespace RTTwoLabelRayleigh
/-- Scalar two-block test: the Frobenius-normalized comparison bounds the sum
of the matched block norms by the top norm plus the remaining spectral norm. -/
private theorem trace_le_of_test {d₀ d₁ e a b x y : ℝ}
    (hF : d₀ ^ 2 + d₁ ^ 2 + 2 * e ^ 2 = 2)
    (hv : a ^ 2 + b ^ 2 = 1) (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hs : x ^ 2 + y ^ 2 = 2)
    (htest : x ≤ d₀ * a ^ 2 + d₁ * b ^ 2 + 2 * e * a * b) :
    d₀ + d₁ ≤ x + y := by
  let T := d₀ + d₁
  let W := (d₀ - d₁) * (a ^ 2 - b ^ 2) + 4 * e * a * b
  have huv : (a ^ 2 - b ^ 2) ^ 2 + (2 * a * b) ^ 2 = 1 := by
    calc
      _ = (a ^ 2 + b ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hv]; norm_num
  have htW : W ^ 2 ≤ 4 - T ^ 2 := by
    have heq : W ^ 2 + ((d₀ - d₁) * (2 * a * b) - (2 * e) * (a ^ 2 - b ^ 2)) ^ 2 =
        ((d₀ - d₁) ^ 2 + (2 * e) ^ 2) * ((a ^ 2 - b ^ 2) ^ 2 + (2 * a * b) ^ 2) := by
      dsimp [W]
      ring
    rw [huv, mul_one] at heq
    dsimp [T]
    nlinarith [sq_nonneg ((d₀ - d₁) * (2 * a * b) - (2 * e) * (a ^ 2 - b ^ 2))]
  have ht₂ : T ≤ 2 := by
    by_contra! h
    nlinarith [mul_pos (show 0 < T - 2 by linarith) (show 0 < T + 2 by linarith),
      sq_nonneg W]
  have hp : 0 ≤ 2 * x - T := by linarith
  have hm : 2 * x - T ≤ W := by
    have hident : T + W = 2 * (d₀ * a ^ 2 + d₁ * b ^ 2 + 2 * e * a * b) := by
      calc
        _ = 2 * (d₀ * a ^ 2 + d₁ * b ^ 2 + 2 * e * a * b) +
            (d₀ + d₁) * (1 - (a ^ 2 + b ^ 2)) := by dsimp [T, W]; ring
        _ = _ := by rw [hv]; ring
    linarith
  have hsq : (2 * x - T) ^ 2 ≤ W ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ W - (2 * x - T) by linarith)
      (show 0 ≤ W + (2 * x - T) by linarith)]
  have hfactor : (2 * x - T) ^ 2 - (4 - T ^ 2) = 2 * ((T - x - y) * (T - x + y)) := by
    calc
      _ = 2 * ((T - x - y) * (T - x + y)) + 2 * (x ^ 2 + y ^ 2 - 2) := by ring
      _ = _ := by rw [hs]; ring
  change T ≤ x + y
  by_contra! h
  have hpos : 0 < (T - x - y) * (T - x + y) := mul_pos (by linarith) (by linarith)
  linarith
/-- Exact two-label cap reduction from the block norm comparison, with no
simple-eigenvalue premise and no restriction on the underlying Schmidt rank. -/
private theorem two_label_cap_of_test {d₀ d₁ e a b x y : ℝ}
    (h₀ : 0 ≤ d₀) (h₁ : 0 ≤ d₁)
    (hF : d₀ ^ 2 + d₁ ^ 2 + 2 * e ^ 2 = 2)
    (hv : a ^ 2 + b ^ 2 = 1) (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hs : x ^ 2 + y ^ 2 = 2)
    (htest : x ≤ d₀ * a ^ 2 + d₁ * b ^ 2 + 2 * e * a * b) :
    min 1 (d₀ ^ 2) + min 1 (d₁ ^ 2) ≤ 1 + (x + y - 1) ^ 2 := by
  have hmin (d : ℝ) (hd : 0 ≤ d) : min 1 (d ^ 2) = (min 1 d) ^ 2 := by
    by_cases h : d ≤ 1
    · have hsq : d ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 1 + d by linarith)]
      rw [min_eq_right hsq, min_eq_right h]
    · have h' : 1 ≤ d := by linarith
      have hsq : 1 ≤ d ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h') (show 0 ≤ d + 1 by linarith)]
      rw [min_eq_left hsq, min_eq_left h']
      norm_num
  rw [hmin d₀ h₀, hmin d₁ h₁]
  let p := min 1 d₀
  let q := min 1 d₁
  change p ^ 2 + q ^ 2 ≤ 1 + (x + y - 1) ^ 2
  have hp : 0 ≤ p := le_min (by norm_num) h₀
  have hq : 0 ≤ q := le_min (by norm_num) h₁
  by_cases h : p + q ≤ 1
  · nlinarith [mul_nonneg hp hq, sq_nonneg (x + y - 1),
      mul_nonneg (show 0 ≤ 1 - (p + q) by linarith) (show 0 ≤ 1 + (p + q) by linarith)]
  · have ht := trace_le_of_test hF hv hx hy hs htest
    have hpt : p ≤ d₀ := min_le_right ..
    have hqt : q ≤ d₁ := min_le_right ..
    have hp₁ : p ≤ 1 := min_le_left ..
    have hq₁ : q ≤ 1 := min_le_left ..
    nlinarith [mul_nonneg (sub_nonneg.mpr hp₁) (sub_nonneg.mpr hq₁),
      mul_nonneg (show 0 ≤ (x + y - 1) - (p + q - 1) by linarith)
        (show 0 ≤ (x + y - 1) + (p + q - 1) by linarith)]
end RTTwoLabelRayleigh
namespace RTBinary
noncomputable section
variable {I O K V : Type*} [Fintype I] [DecidableEq I] [Fintype O] [Fintype K] [Fintype V]
private def half : ℂ := (Real.sqrt (1/2:ℝ) : ℝ)
private theorem half_conj : conj half = half := by exact Complex.conj_ofReal _
private theorem half_sq : half * half = 1/2 := by
  unfold half
  rw [← pow_two]
  rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2),Complex.ofReal_div]
  norm_num
private def effect {E : Type*} [Fintype E] (A : LocalColumns I O E) (i : O) (a b : I) : ℂ :=
  ∑ k, conj (A.entry a i k) * A.entry b i k
private def pairedEntry (A : LocalColumns I O K) (B : LocalColumns I O V) (a : I) (i : O) :
    K ⊕ V → ℂ
  | .inl k => half * A.entry a i k
  | .inr v => half * conj (B.entry a i v)
omit [Fintype I] in
private theorem pairedGramAt (A : LocalColumns I O K) (B : LocalColumns I O V) (i : O) (a b : I) :
    (∑ k, conj (pairedEntry A B a i k) * pairedEntry A B b i k) =
      (effect A i a b + conj (effect B i a b))/2 := by
  have hl (k : K) : conj (pairedEntry A B a i (.inl k)) * pairedEntry A B b i (.inl k) =
      (1/2:ℂ)*(conj (A.entry a i k)*A.entry b i k) := by
    simp only [pairedEntry,map_mul,half_conj]
    rw [← half_sq]
    ring
  have hr (v : V) : conj (pairedEntry A B a i (.inr v)) * pairedEntry A B b i (.inr v) =
      (1/2:ℂ)*conj (conj (B.entry a i v)*B.entry b i v) := by
    simp only [pairedEntry,map_mul,half_conj]
    rw [← half_sq]
    ring
  simp only [Fintype.sum_sum_type,hl,hr,← Finset.mul_sum,effect,map_sum]
  ring
private def paired (A : LocalColumns I O K) (B : LocalColumns I O V) :
    LocalColumns I O (K ⊕ V) where
  entry := pairedEntry A B
  gram a b := by
    simp only [pairedGramAt,div_eq_mul_inv,← Finset.sum_mul,Finset.sum_add_distrib,
      ← map_sum,effect,A.gram,B.gram]
    split_ifs <;> norm_num
private def dual {E : Type*} [Fintype E] (A : LocalColumns I O E) : LocalColumns I O E where
  entry a i k := conj (A.entry a i k)
  gram a b := by
    have h := congrArg conj (A.gram a b)
    by_cases hh : a=b <;> simpa only [map_sum,map_mul,ite_eq_left,ite_eq_right,hh,
      not_false_eq_true,map_one,map_zero] using h
omit [Fintype I] in
private theorem effect_paired (A : LocalColumns I O K) (B : LocalColumns I O V) (i : O) (a b : I) :
    effect (paired A B) i a b = (effect A i a b + conj (effect B i a b))/2 :=
  pairedGramAt A B i a b
omit [Fintype I] in
private theorem effect_dual {E : Type*} [Fintype E] (A : LocalColumns I O E) (i : O) (a b : I) :
    effect (dual A) i a b = conj (effect A i a b) := by
  simp only [effect,dual,map_sum,map_mul]
private theorem lsqGram {E : Type*} [Fintype E] (f : E → ℂ) :
    ((lsquare f : ℝ) : ℂ) = ∑ i, conj (f i)*f i := by
  unfold lsquare
  change Complex.ofRealHom _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm,Complex.mul_conj,← Complex.sq_norm]
  rfl
private theorem born_lsq_effect (A : LocalColumns I O K) (B : LocalColumns I O V)
    (x : I → ℝ) (i j : O) :
    ((lsquare (bornVector A B (fun a => (x a : ℂ)) i j) : ℝ) : ℂ) =
      ∑ a, ∑ b, ((x a*x b : ℝ):ℂ) * (effect A i a b * effect B j a b) := by
  classical
  rw [lsqGram]
  have h (kv : K × V) :
      conj (bornVector A B (fun a => (x a : ℂ)) i j kv) *
        bornVector A B (fun a => (x a : ℂ)) i j kv =
      ∑ a, ∑ b, ((x a*x b : ℝ):ℂ) *
        ((conj (A.entry a i kv.1)*A.entry b i kv.1) *
         (conj (B.entry a j kv.2)*B.entry b j kv.2)) := by
    simp only [bornVector,map_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [map_mul, Complex.conj_ofReal,Complex.ofReal_mul]
    ring
  simp only [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [effect, Fintype.sum_prod_type, Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
private def reHom : ℂ →+ ℝ := ⟨⟨Complex.re,rfl⟩,Complex.add_re⟩
private theorem born_effect_re (A : LocalColumns I O K) (B : LocalColumns I O V)
    (x : I → ℝ) (i j : O) :
    lsquare (bornVector A B (fun a => (x a : ℂ)) i j) =
      ∑ a, ∑ b, (x a*x b) * (effect A i a b * effect B j a b).re := by
  have h := congrArg reHom (born_lsq_effect A B x i j)
  simp only [map_sum] at h
  simpa only [reHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Complex.ofReal_re,
    Complex.mul_re,Complex.ofReal_im,zero_mul, sub_zero] using h
/-- Averaging paired effects increases each measured-label match by an explicit
sum of squares. The realized columns use coherent direct-sum environments;
there is no new correlated classical draw. -/
private theorem symmetrization_gain (A : LocalColumns I O K) (B : LocalColumns I O V)
    (x : I → ℝ) (i : O) :
    lsquare (bornVector (paired A B) (dual (paired A B)) (fun a => (x a : ℂ)) i i) =
    lsquare (bornVector A B (fun a => (x a : ℂ)) i i) +
      ∑ a, ∑ b, (x a*x b) *
        Complex.normSq (effect A i a b - conj (effect B i a b))/4 := by
  rw [born_effect_re,born_effect_re, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [effect_dual,effect_paired]
  generalize effect A i a b = e
  generalize effect B i a b = f
  have h : ((e + conj f)/2 * conj ((e+conj f)/2)).re =
      (e*f).re + Complex.normSq (e-conj f)/4 := by
    rw [Complex.mul_conj, Complex.ofReal_re,Complex.normSq_apply,Complex.normSq_apply]
    simp only [Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im,Complex.mul_re]
    ring
  rw [h]
  ring
private theorem symmetrization_dominates (A : LocalColumns I O K) (B : LocalColumns I O V)
    (x : I → ℝ) (hx : ∀ a, 0 ≤ x a) (i : O) :
    lsquare (bornVector A B (fun a => (x a : ℂ)) i i) ≤
      lsquare (bornVector (paired A B) (dual (paired A B)) (fun a => (x a : ℂ)) i i) := by
  rw [symmetrization_gain]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => div_nonneg (mul_nonneg (mul_nonneg (hx a) (hx b)) (Complex.normSq_nonneg _)) (by norm_num))))
private theorem conjugate_born_symmetric (A : LocalColumns I O K)
    (x : I → ℝ) (i j : O) :
    lsquare (bornVector A (dual A) (fun a => (x a : ℂ)) i j) =
      lsquare (bornVector A (dual A) (fun a => (x a : ℂ)) j i) := by
  rw [born_effect_re,born_effect_re]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [effect_dual,effect_dual]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring
variable {I O K V : Type*} [Fintype I] [DecidableEq I] [Fintype O] [Fintype K] [Fintype V]
private def reMap : ℂ →+ ℝ := ⟨⟨Complex.re,rfl⟩,Complex.add_re⟩
private theorem sqNorm {E : Type*} [Fintype E] (f : E → ℂ) :
    (lnorm f)^2 = lsquare f := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
private theorem norm_bound {E : Type*} [Fintype E] (f g : E → ℂ) :
    (∑ i, conj (f i) * g i).re ≤ lnorm f * lnorm g := by
  change reMap _ ≤ _
  rw [map_sum]
  calc
    _ ≤ ∑ i, ‖f i‖*‖g i‖ := Finset.sum_le_sum fun i _ => by
      change (conj (f i)*g i).re ≤ _
      simpa only [Complex.norm_mul, Complex.norm_conj] using Complex.re_le_norm (conj (f i)*g i)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖f i‖) (fun i => ‖g i‖)
private theorem outerNorm {E F : Type*} [Fintype E] [Fintype F] (f : E → ℂ) (g : F → ℂ) :
    lnorm (fun jk : E × F => f jk.1 * conj (g jk.2)) = lnorm f * lnorm g := by
  unfold lnorm lsquare
  simp only [Fintype.sum_prod_type, Complex.norm_mul,Complex.norm_conj,mul_pow,
    ← Finset.mul_sum, ← Finset.sum_mul]
  exact Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _) _
omit [Fintype I] in
private theorem column_sq_total (A : LocalColumns I O K) (a : I) :
    (∑ i, (lnorm (A.entry a i))^2) = 1 := by
  have h := congrArg reMap (A.gram a a)
  have hh : (∑ i, ∑ k, reMap (conj (A.entry a i k)*A.entry a i k)) = 1 := by
    simpa [reMap] using h
  rw [← hh]
  apply Finset.sum_congr rfl
  intro i _
  rw [sqNorm]
  unfold lsquare
  apply Finset.sum_congr rfl
  intro j _
  change ‖A.entry a i j‖^2 = (conj (A.entry a i j)*A.entry a i j).re
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
private def testBlock (A : LocalColumns I O K) (a : I) (i j : O) (uv : K × K) : ℂ :=
    A.entry a i uv.1 * conj (A.entry a j uv.2)
private theorem test_total (A : LocalColumns I O K) (x : I → ℝ) (a : I) :
    (∑ i, ∑ j, ∑ uv : K × K, conj (testBlock A a i j uv) *
      bornVector A (dual A) (fun b => (x b : ℂ)) i j uv) = x a := by
  classical
  have h (i j : O) (uv : K × K) :
    conj (testBlock A a i j uv) *
      bornVector A (dual A) (fun b => (x b : ℂ)) i j uv =
      ∑ b, (x b : ℂ) * ((conj (A.entry a i uv.1)*A.entry b i uv.1) *
        conj (conj (A.entry a j uv.2)*A.entry b j uv.2)) := by
    unfold bornVector
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [testBlock,dual,map_mul,Complex.conj_conj]
    ring
  simp only [h]
  have hX : ∀ b : I, (∑ i : O, ∑ j : O, ∑ uv : K × K,
      (x b:ℂ) * ((conj (A.entry a i uv.1)*A.entry b i uv.1) *
        conj (conj (A.entry a j uv.2)*A.entry b j uv.2))) =
    (x b:ℂ) * ((∑ i : O, ∑ k : K, conj (A.entry a i k)*A.entry b i k) *
      conj (∑ j : O, ∑ k : K, conj (A.entry a j k)*A.entry b j k)) := by
    intro b
    let g := fun i (k : K) => conj (A.entry a i k)*A.entry b i k
    let c := (x b : ℂ)
    change (∑ i, ∑ j, ∑ uv : K×K, c*(g i uv.1*conj (g j uv.2))) =
      c*((∑ i, ∑ k, g i k)*conj (∑ j, ∑ k, g j k))
    simp only [Fintype.sum_prod_type, map_sum]
    calc
      _ = ∑ i, ∑ j, ∑ k, c*(g i k * (∑ l, conj (g j l))) := by
        simp only [Finset.mul_sum]
      _ = ∑ i, ∑ j, c*((∑ k,g i k)*(∑ l,conj (g j l))) := by
        simp only [Finset.sum_mul,Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
      _ = ∑ i, c*((∑ k,g i k)*(∑ j,∑ l,conj (g j l))) := by
        simp only [Finset.mul_sum]
      _ = _ := by
        conv_rhs => rw [Finset.sum_mul,Finset.mul_sum]
  have move (i : O) :
      (∑ j : O, ∑ uv : K×K, ∑ b : I, (x b:ℂ) *
        ((conj (A.entry a i uv.1)*A.entry b i uv.1) *
          conj (conj (A.entry a j uv.2)*A.entry b j uv.2))) =
      (∑ b : I, ∑ j : O, ∑ uv : K×K, (x b:ℂ) *
        ((conj (A.entry a i uv.1)*A.entry b i uv.1) *
          conj (conj (A.entry a j uv.2)*A.entry b j uv.2))) := by
    calc
      _ = ∑ j : O, ∑ b : I, ∑ uv : K×K, (x b:ℂ) *
          ((conj (A.entry a i uv.1)*A.entry b i uv.1) *
            conj (conj (A.entry a j uv.2)*A.entry b j uv.2)) :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  simp only [move]
  rw [Finset.sum_comm]
  simp only [hX,A.gram]
  simp
private theorem actual_rayleigh (A : LocalColumns I O K) (x : I → ℝ) (a : I) :
    x a ≤ ∑ i, ∑ j,
      lnorm (bornVector A (dual A) (fun b => (x b : ℂ)) i j) *
        (lnorm (A.entry a i)*lnorm (A.entry a j)) := by
  have h : (∑ i, ∑ j, (∑ uv : K×K,
      conj (testBlock A a i j uv)*bornVector A (dual A) (fun b => (x b:ℂ)) i j uv).re) = x a := by
    change (∑ i, ∑ j, reMap (∑ uv : K×K,
      conj (testBlock A a i j uv)*bornVector A (dual A) (fun b => (x b:ℂ)) i j uv)) = x a
    calc
      _ = reMap (∑ i, ∑ j, ∑ uv : K×K,
          conj (testBlock A a i j uv)*bornVector A (dual A) (fun b => (x b:ℂ)) i j uv) := by
        simp only [map_sum]
      _ = _ := by rw [test_total]; exact Complex.ofReal_re _
  rw [←h]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hnorm := norm_bound (testBlock A a i j)
    (bornVector A (dual A) (fun b => (x b:ℂ)) i j)
  have ht : lnorm (testBlock A a i j) = lnorm (A.entry a i)*lnorm (A.entry a j) :=
    outerNorm _ _
  rw [ht,mul_comm] at hnorm
  exact hnorm
private theorem born_frobenius_total (A : LocalColumns I O K) (x : I → ℝ) :
    (∑ i, ∑ j, (lnorm (bornVector A (dual A) (fun a => (x a : ℂ)) i j))^2) =
      ∑ a, (x a)^2 := by
  classical
  let Y := bornVector A (dual A) (fun a => (x a : ℂ))
  change (∑ i, ∑ j, lnorm (Y i j)^2) = _
  have hG (f : K×K → ℂ) : (lnorm f)^2 = reMap (∑ uv, conj (f uv)*f uv) := by
    rw [sqNorm, map_sum]
    apply Finset.sum_congr rfl
    intro u _
    change ‖f u‖^2 = (conj (f u)*f u).re
    rw [mul_comm,Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]
  simp only [hG]
  have hY (i j : O) (uv : K×K) :
      conj (Y i j uv)*(Y i j uv) =
        ∑ a, (x a:ℂ)*(conj (testBlock A a i j uv)*(Y i j uv)) := by
    conv_lhs =>
      arg 1
      change conj (bornVector A (dual A) (fun a => (x a : ℂ)) i j uv)
      unfold bornVector
    rw [map_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    simp only [map_mul,Complex.conj_ofReal, testBlock,dual]
    ring
  have hmove (i j : O) :
      (∑ uv : K×K, ∑ a : I, (x a:ℂ)*(conj (testBlock A a i j uv)*(Y i j uv))) =
      ∑ a : I, ∑ uv : K×K, (x a:ℂ)*(conj (testBlock A a i j uv)*(Y i j uv)) :=
    Finset.sum_comm
  have hmove₂ (i : O) :
      (∑ j : O, ∑ a : I, ∑ uv : K×K, (x a:ℂ)*(conj (testBlock A a i j uv)*(Y i j uv))) =
      ∑ a : I, ∑ j : O, ∑ uv : K×K, (x a:ℂ)*(conj (testBlock A a i j uv)*(Y i j uv)) :=
    Finset.sum_comm
  calc
    _ = reMap (∑ i, ∑ j, ∑ uv, conj (Y i j uv)*(Y i j uv)) := by simp only [map_sum]
    _ = reMap (∑ a, (x a:ℂ)* (∑ i, ∑ j, ∑ uv, conj (testBlock A a i j uv)*(Y i j uv))) := by
      rw [show (∑ i, ∑ j, ∑ uv, conj (Y i j uv)*(Y i j uv)) =
          ∑ a, ∑ i, ∑ j, ∑ uv, (x a:ℂ)*(conj (testBlock A a i j uv)*(Y i j uv)) by
        simp only [hY, hmove,hmove₂]
        exact Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp only [Y,test_total,map_sum]
      apply Finset.sum_congr rfl
      intro a _
      change ((x a : ℂ)*(x a : ℂ)).re = _
      rw [← Complex.ofReal_mul,Complex.ofReal_re,pow_two]
/-- The arbitrary-rank two-label bound on the literal independently realized
Born mass. Only the selected resource amplitude needs to be at least one,
so the largest-amplitude version follows by finite maximization. -/
private theorem two_label_actual_cap (A : LocalColumns I (Fin 2) K) (B : LocalColumns I (Fin 2) V)
    (x : I → ℝ) (hx : ∀ a, 0 ≤ x a) (hs : ∑ a, (x a)^2 = 2)
    (a : I) (ha : 1 ≤ x a) :
    (∑ i : Fin 2, min 1 (lsquare (bornVector A B (fun a => (x a:ℂ)) i i))) ≤
      1+(x a+Real.sqrt (2-(x a)^2)-1)^2 := by
  let C := paired A B
  let Y := bornVector C (dual C) (fun b => (x b : ℂ))
  let a₀ := lnorm (C.entry a 0)
  let a₁ := lnorm (C.entry a 1)
  let d₀ := lnorm (Y 0 0)
  let d₁ := lnorm (Y 1 1)
  let e := lnorm (Y 0 1)
  have he : lnorm (Y 1 0) = e := by
    unfold e lnorm Y
    rw [conjugate_born_symmetric]
  have hcomp : (∑ i : Fin 2, min 1 (lsquare (bornVector A B (fun a => (x a:ℂ)) i i))) ≤
      ∑ i : Fin 2, min 1 (lsquare (Y i i)) :=
    Finset.sum_le_sum (fun i _ => min_le_min le_rfl (symmetrization_dominates A B x hx i))
  have hF := born_frobenius_total C x
  change (∑ i : Fin 2, ∑ j : Fin 2, (lnorm (Y i j))^2) = _ at hF
  rw [hs] at hF
  simp only [Fin.sum_univ_two,he] at hF
  have hF' : d₀^2+d₁^2+2*e^2=2 := by dsimp [d₀,d₁]; linarith
  have hv := column_sq_total C a
  simp only [Fin.sum_univ_two] at hv
  have ht := actual_rayleigh C x a
  change x a ≤ (∑ i : Fin 2, ∑ j : Fin 2, lnorm (Y i j) *
    (lnorm (C.entry a i)*lnorm (C.entry a j))) at ht
  simp only [Fin.sum_univ_two, he] at ht
  have ht' : x a ≤ d₀*a₀^2+d₁*a₁^2+2*e*a₀*a₁ := by
    dsimp [a₀,a₁,d₀,d₁]
    nlinarith only [ht]
  have hrem : 0 ≤ 2-(x a)^2 := by
    rw [sub_nonneg,←hs]
    exact Finset.single_le_sum (fun b _ => sq_nonneg (x b)) (Finset.mem_univ a)
  have hb := RTTwoLabelRayleigh.two_label_cap_of_test (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hF' hv ha (Real.sqrt_nonneg _) (by linarith [Real.sq_sqrt hrem]) ht'
  refine hcomp.trans ?_
  simp only [Fin.sum_univ_two,← sqNorm]
  exact hb
end
end RTBinary
namespace RTBinaryCritical
private def criticalPoly (u : ℝ) : ℝ :=
  1-6*u-7*u^2+20*u^3-9*u^4+10*u^5+15*u^6
private noncomputable def ratio (u : ℝ) : ℝ :=
  (1-2*u^2+5*u^4)/(1-u+u^2+3*u^3)
private noncomputable def smallProb (u : ℝ) : ℝ :=
  ((1-2*u-u^2)/(1+u^2))^2/2
private def cpDeriv (u : ℝ) : ℝ := -6-14*u+60*u^2-36*u^3+50*u^4+90*u^5
private theorem cpDeriv_eq (u : ℝ) : HasDerivAt criticalPoly (cpDeriv u) u := by
  let h := hasDerivAt_id u
  have hd := ((((((hasDerivAt_const u (1:ℝ)).sub (h.const_mul 6)).sub
    ((h.pow 2).const_mul 7)).add ((h.pow 3).const_mul 20)).sub
    ((h.pow 4).const_mul 9)).add ((h.pow 5).const_mul 10)).add ((h.pow 6).const_mul 15)
  convert hd using 1
  · rfl
  · simp [cpDeriv]; ring
private theorem cpDeriv_neg (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 5/12) :
    cpDeriv u ≤ -(179/144) := by
  have h2 : u^2 ≤ (5/12:ℝ)^2 := pow_le_pow_left₀ h0 h1 2
  have h3 : u^3 ≤ (5/12:ℝ)^3 := pow_le_pow_left₀ h0 h1 3
  have hm : 50*u^2+90*u^3 ≤ 16 := by linarith
  have ht := mul_le_mul_of_nonneg_right hm (sq_nonneg u)
  have hq : 76*u-36*u^2 ≤ 305/12 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0≤61-36*u by linarith)]
  have hg := mul_le_mul_of_nonneg_right hq h0
  dsimp [cpDeriv]
  nlinarith
private theorem cp_cont : Continuous criticalPoly := by unfold criticalPoly; fun_prop
private theorem cp_anti : StrictAntiOn criticalPoly (Set.Icc (0:ℝ) (5/12)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) cp_cont.continuousOn
  intro u hu
  rw [(cpDeriv_eq u).deriv]
  have hu' := interior_subset hu
  exact (cpDeriv_neg u hu'.1 hu'.2).trans_lt (by norm_num)
private noncomputable def L : ℝ := 150932116381/1000000000000
private noncomputable def U : ℝ := 150932116382/1000000000000
private theorem signs : 0 < criticalPoly L ∧ criticalPoly U < 0 := by
  norm_num [criticalPoly,L,U]
private theorem root_LU : ∃ u, L < u ∧ u < U ∧ criticalPoly u = 0 := by
  have hLU : L ≤ U := by norm_num [L,U]
  have hs : (0:ℝ) ∈ Set.Icc (criticalPoly U) (criticalPoly L) := ⟨signs.2.le, signs.1.le⟩
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc' hLU cp_cont.continuousOn hs
  refine ⟨u, lt_of_le_of_ne hu.1 ?_,lt_of_le_of_ne hu.2 ?_,he⟩
  · intro h
    rw [← h] at he
    exact signs.1.ne' he
  · intro h
    rw [h] at he
    exact signs.2.ne he
private theorem den_pos (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 5/12) :
    0 < 1-u+u^2+3*u^3 := by
  linarith [sq_nonneg u, pow_nonneg h0 3]
private theorem eval_brackets (u : ℝ) (hL : L ≤ u) (hU : u ≤ U) :
    (1084871396888/1000000000000:ℝ) < ratio u ∧
      ratio u < (1084871396892/1000000000000:ℝ) ∧
    (218006629439/1000000000000:ℝ) < smallProb u ∧
      smallProb u < (218006629441/1000000000000:ℝ) := by
  have hL0 : 0 ≤ L := by norm_num [L]
  have hu0 : 0 ≤ u := hL0.trans hL
  have hu1 : u ≤ 5/12 := hU.trans (by norm_num [U])
  have h2L : L^2 ≤ u^2 := pow_le_pow_left₀ hL0 hL 2
  have h2U : u^2 ≤ U^2 := pow_le_pow_left₀ hu0 hU 2
  have h3L : L^3 ≤ u^3 := pow_le_pow_left₀ hL0 hL 3
  have h3U : u^3 ≤ U^3 := pow_le_pow_left₀ hu0 hU 3
  have h4L : L^4 ≤ u^4 := pow_le_pow_left₀ hL0 hL 4
  have h4U : u^4 ≤ U^4 := pow_le_pow_left₀ hu0 hU 4
  have hD := den_pos u hu0 hu1
  have hloY : 0 ≤ 1-2*U-U^2 := by norm_num [U]
  have hyl : 1-2*U-U^2 ≤ 1-2*u-u^2 := by linarith
  have hyu : 1-2*u-u^2 ≤ 1-2*L-L^2 := by linarith
  have hy2l := pow_le_pow_left₀ hloY hyl 2
  have hy2u := pow_le_pow_left₀ (hloY.trans hyl) hyu 2
  have hd2l : (1+L^2)^2 ≤ (1+u^2)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hd2u : (1+u^2)^2 ≤ (1+U^2)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have wD : (1+u^2) ≠ 0 := by positivity
  have hwl : (1-2*U-U^2)^2 >
      (218006629439/1000000000000:ℝ) * (2*(1+U^2)^2) := by norm_num [U]
  have hwu : (1-2*L-L^2)^2 <
      (218006629441/1000000000000:ℝ) * (2*(1+L^2)^2) := by norm_num [L]
  have hrl : (1-2*U^2+5*L^4) >
      (1084871396888/1000000000000:ℝ)*(1-L+U^2+3*U^3) := by norm_num [L,U]
  have hru : (1-2*L^2+5*U^4) <
      (1084871396892/1000000000000:ℝ)*(1-U+L^2+3*L^3) := by norm_num [L,U]
  unfold ratio smallProb
  rw [div_pow,div_div]
  refine ⟨(lt_div_iff₀ hD).mpr ?_,(div_lt_iff₀ hD).mpr ?_,
    (lt_div_iff₀ (by positivity)).mpr ?_,(div_lt_iff₀ (by positivity)).mpr ?_⟩
  all_goals linarith
/-- A kernel-checked unique critical point and exact rational brackets for
the normalized binary overlap quotient and smaller Schmidt probability. -/
private theorem unique_critical_with_brackets :
    ∃! u : ℝ, u ∈ Set.Icc (0:ℝ) (Real.sqrt 2 - 1) ∧ criticalPoly u = 0 ∧
      150932116381/1000000000000 < u ∧ u < 150932116382/1000000000000 ∧
      1084871396888/1000000000000 < ratio u ∧ ratio u < 1084871396892/1000000000000 ∧
      218006629439/1000000000000 < smallProb u ∧ smallProb u < 218006629441/1000000000000 := by
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hnon := Real.sqrt_nonneg (2:ℝ)
  have hr1 : (6/5:ℝ) < Real.sqrt 2 := by nlinarith
  have hr2 : Real.sqrt 2 - 1 ≤ 5/12 := by nlinarith
  obtain ⟨u,huL,huU,hu⟩ := root_LU
  have huI : u ∈ Set.Icc (0:ℝ) (Real.sqrt 2 - 1) :=
    ⟨(show 0≤L by norm_num [L]).trans huL.le,
      huU.le.trans ((show U≤1/5 by norm_num [U]).trans (by linarith))⟩
  refine ⟨u, ⟨huI,hu,huL,huU,eval_brackets u huL.le huU.le⟩,?_⟩
  intro v hv
  exact cp_anti.injOn ⟨hv.1.1,hv.1.2.trans hr2⟩ ⟨huI.1,huI.2.trans hr2⟩ (hv.2.1.trans hu.symm)
private def num (u : ℝ) : ℝ := 1-2*u^2+5*u^4
private def den (u : ℝ) : ℝ := 1-u+u^2+3*u^3
private theorem ratio_deriv (u : ℝ) (hu : 0≤u) (hu' : u≤5/12) :
    HasDerivAt ratio (criticalPoly u/(den u)^2) u := by
  let h := hasDerivAt_id u
  have hN : HasDerivAt num (-4*u+20*u^3) u := by
    have hR := ((hasDerivAt_const u (1:ℝ)).sub ((h.pow 2).const_mul 2)).add ((h.pow 4).const_mul 5)
    convert hR using 1
    · rfl
    · simp; ring
  have hD : HasDerivAt den (-1+2*u+9*u^2) u := by
    have hR := (((hasDerivAt_const u (1:ℝ)).sub h).add (h.pow 2)).add ((h.pow 3).const_mul 3)
    convert hR using 1
    · rfl
    · simp; ring
  have hd : den u ≠ 0 := (den_pos u hu hu').ne'
  convert (hN.div hD hd) using 1
  · rfl
  · congr 1
    unfold num den criticalPoly
    ring
private theorem ratio_contOn (a b : ℝ) (ha : 0≤a) (hb : b≤5/12) :
    ContinuousOn ratio (Set.Icc a b) := by
  intro u hu
  exact (ratio_deriv u (ha.trans hu.1) (hu.2.trans hb)).continuousAt.continuousWithinAt
/-- The unique bracketed critical point actually strictly maximizes the
two-label scalar overlap ratio on the full normalized quarter arc. -/
private theorem unique_global_scalar_maximum :
    ∃ u : ℝ, u ∈ Set.Icc (0:ℝ) (Real.sqrt 2-1) ∧ criticalPoly u = 0 ∧
      150932116381/1000000000000 < u ∧ u < 150932116382/1000000000000 ∧
      1084871396888/1000000000000 < ratio u ∧ ratio u < 1084871396892/1000000000000 ∧
      218006629439/1000000000000 < smallProb u ∧ smallProb u < 218006629441/1000000000000 ∧
      ∀ v ∈ Set.Icc (0:ℝ) (Real.sqrt 2-1), v ≠ u → ratio v < ratio u := by
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hnon := Real.sqrt_nonneg (2:ℝ)
  have hr2 : Real.sqrt 2-1 ≤ 5/12 := by nlinarith
  obtain ⟨u,hu,_⟩ := unique_critical_with_brackets
  refine ⟨u,hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,hu.2.2.2.2.1,hu.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.1,hu.2.2.2.2.2.2.2,?_⟩
  have hu0 := hu.1.1
  have hu1 := hu.1.2
  have hcrit := hu.2.1
  have hinc : StrictMonoOn ratio (Set.Icc 0 u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (ratio_contOn _ _ le_rfl (hu1.trans hr2))
    intro v hv
    rw [interior_Icc] at hv
    have hv1 : v≤5/12 := hv.2.le.trans (hu1.trans hr2)
    rw [(ratio_deriv v hv.1.le hv1).deriv]
    have hp := cp_anti ⟨hv.1.le,hv1⟩ ⟨hu0,hu1.trans hr2⟩ hv.2
    rw [hcrit] at hp
    exact div_pos hp (pow_pos (den_pos v hv.1.le hv1) _)
  have hdec : StrictAntiOn ratio (Set.Icc u (Real.sqrt 2-1)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (ratio_contOn _ _ hu0 hr2)
    intro v hv
    rw [interior_Icc] at hv
    have hv0 : 0≤v := hu0.trans hv.1.le
    have hv1 : v≤5/12 := hv.2.le.trans hr2
    rw [(ratio_deriv v hv0 hv1).deriv]
    have hp := cp_anti ⟨hu0,hu1.trans hr2⟩ ⟨hv0,hv1⟩ hv.1
    rw [hcrit] at hp
    exact div_neg_of_neg_of_pos hp (pow_pos (den_pos v hv0 hv1) _)
  intro v hv hne
  rcases lt_or_gt_of_ne hne with h|h
  · exact hinc ⟨hv.1,h.le⟩ ⟨hu0,le_rfl⟩ h
  · exact hdec ⟨le_rfl,hu1⟩ ⟨h.le,hv.2⟩ h
private noncomputable def arcX (u : ℝ) : ℝ := (1+2*u-u^2)/(1+u^2)
private noncomputable def arcY (u : ℝ) : ℝ := (1-2*u-u^2)/(1+u^2)
/-- Explicit coordinates take the entire admissible arc into normalized
Schmidt pairs and give the exact scalar quotient in those coordinates. -/
private theorem arc_evaluation (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) (Real.sqrt 2-1)) :
    1≤arcX u ∧ 0≤arcY u ∧ arcY u≤1 ∧
      (arcX u)^2+(arcY u)^2=2 ∧ smallProb u=(arcY u)^2/2 ∧
      ratio u = (1+(arcX u+arcY u-1)^2)/(arcX u+(arcY u)^2) := by
  have hsq := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hnon := Real.sqrt_nonneg (2:ℝ)
  have h5 : Real.sqrt 2 - 1 ≤ 5/12 := by nlinarith
  have hu1 : u≤1 := hu.2.trans (h5.trans (by norm_num))
  have hD : (0:ℝ)<1+u^2 := by positivity
  have huY := pow_le_pow_left₀ (show 0≤u+1 by linarith [hu.1])
    (show u+1≤Real.sqrt 2 by linarith [hu.2]) 2
  unfold arcX arcY
  refine ⟨(le_div_iff₀ hD).mpr ?_,div_nonneg ?_ hD.le,(div_le_iff₀ hD).mpr ?_,?_,rfl,?_⟩
  · nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu1)]
  · nlinarith
  · nlinarith [hu.1,sq_nonneg u]
  · field_simp
    ring
  · unfold ratio
    have hden : (1-u+u^2+3*u^3)≠0 := (den_pos u hu.1 (hu.2.trans h5)).ne'
    have hx' : 1 ≤ (1+2*u-u^2)/(1+u^2) :=
      (le_div_iff₀ hD).mpr (by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu1)])
    have hQ : (1+2*u-u^2)/(1+u^2) + ((1-2*u-u^2)/(1+u^2))^2 ≠ 0 := by
      nlinarith [sq_nonneg ((1-2*u-u^2)/(1+u^2))]
    apply (div_eq_div_iff hden hQ).mpr
    field_simp
    ring
/-- The rational parameter covers every admissible sorted normalized
two-amplitude spectrum, endpoints included. -/
private theorem arc_surjects (x y : ℝ) (hx : 1≤x) (hy : 0≤y) (hy1 : y≤1)
    (hxy : x^2+y^2=2) :
    ∃ u ∈ Set.Icc (0:ℝ) (Real.sqrt 2-1), arcX u=x ∧ arcY u=y := by
  let u := (x-y)/(2+x+y)
  have hD : 0<2+x+y := by linarith
  have h0 : 0≤u := div_nonneg (by linarith) hD.le
  have hsq := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hnon := Real.sqrt_nonneg (2:ℝ)
  have hx' : x≤Real.sqrt 2 := by
    by_contra! hh
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0<x+Real.sqrt 2 by linarith)]
  have hs' : Real.sqrt 2≤x+y := by
    by_contra! hh
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0<Real.sqrt 2+(x+y) by linarith),
      mul_nonneg (show 0≤x by linarith) hy]
  have hh' : (Real.sqrt 2 - 1)*(2+x+y) ≥ Real.sqrt 2 := by
    have hpos : 0≤Real.sqrt 2-1 := by nlinarith
    nlinarith [mul_nonneg hpos (sub_nonneg.mpr hs')]
  have h1 : u≤Real.sqrt 2-1 := (div_le_iff₀ hD).mpr (by linarith)
  refine ⟨u,⟨h0,h1⟩,?_,?_⟩
  · unfold arcX
    have hd : 0<1+u^2 := by positivity
    apply (div_eq_iff hd.ne').mpr
    dsimp only [u]
    field_simp
    have hm := congrArg (fun z : ℝ => z*(x+1)) hxy
    nlinarith [hm]
  · unfold arcY
    have hd : 0<1+u^2 := by positivity
    apply (div_eq_iff hd.ne').mpr
    dsimp only [u]
    field_simp
    have hm := congrArg (fun z : ℝ => z*(y+1)) hxy
    nlinarith [hm]
end RTBinaryCritical
namespace RTBinaryAttainment
private def rot (c s : ℝ) (a i : Fin 2) : ℝ :=
  if a=0 then (if i=0 then c else s) else (if i=0 then -s else c)
private def columns (c s : ℝ) (hn : c^2+s^2=1) : LocalColumns (Fin 2) (Fin 2) (Fin 1) where
  entry := fun a i _ => (rot c s a i : ℂ)
  gram := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [rot,Fin.sum_univ_two,pow_two] at * <;>
      norm_cast <;> nlinarith
private noncomputable def spec (x y : ℝ) (a : Fin 2) : ℝ :=
  if a=0 then x^2/2 else y^2/2
private theorem amp (x : ℝ) (h : 0≤x) : Real.sqrt (x^2/2)= x/Real.sqrt 2 := by
  rw [Real.sqrt_div (sq_nonneg x),Real.sqrt_sq h]
private theorem sum_cap_square {t : ℝ} (ht : 0≤t) (h1 : t≤1) :
    min (1/2:ℝ) ((t / Real.sqrt 2)^2) = t^2/2 := by
  have he : (t/Real.sqrt 2)^2 = t^2/2 := by
    rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [he,min_eq_right (by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0≤1+t by linarith)])]
private theorem measured_attains (x y : ℝ) (hx0 : 0≤x) (hy0 : 0≤y)
    (hxy : x^2+y^2=2) (c s : ℝ) (hn : c^2+s^2=1) (hd : x*c^2+y*s^2=1) :
    measuredCap 1 ⟨2,2,1,1,spec x y,columns c s hn,columns c s hn⟩
      = (1+(x+y-1)^2)/2 := by
  have hsd : x*s^2+y*c^2=x+y-1 := by
    nlinarith [congrArg (x*·) hn,congrArg (y*·) hn]
  have hsum0 : 0≤x+y-1 := by
    rw [← hsd]
    positivity
  have hsum1 : x+y-1≤1 := by
    by_contra! hc
    nlinarith [sq_nonneg (x-y), mul_pos (sub_pos.mpr (show 2<x+y by linarith))
      (show 0<x+y+2 by linarith)]
  have hf (z : ℂ) (V : Fin 1 × Fin 1 → ℂ) (hV : ∀ i,V i=z) : (lnorm V)^2=‖z‖^2 := by
    have he : lsquare V = ‖z‖^2 := by simp [lsquare,hV]
    unfold lnorm
    rw [he,Real.sq_sqrt (sq_nonneg _)]
  have eq0 (kl : Fin 1 × Fin 1) :
      bornVector (columns c s hn) (columns c s hn)
        (fun a => (Real.sqrt (spec x y a) : ℂ)) 0 0 kl = ((1/Real.sqrt 2 : ℝ) : ℂ) := by
    simp [bornVector,Fin.sum_univ_two,columns,rot,spec,amp x hx0,amp y hy0]
    have hd' : (x / Real.sqrt 2)*c*c + (y / Real.sqrt 2)*(-s)*(-s) = 1 / Real.sqrt 2 := by
      have hR : Real.sqrt 2 ≠ 0 := by positivity
      field_simp
      nlinarith [hd]
    exact_mod_cast (by simpa only [mul_assoc,neg_mul_neg,one_div] using hd')
  have eq1 (kl : Fin 1 × Fin 1) :
      bornVector (columns c s hn) (columns c s hn)
        (fun a => (Real.sqrt (spec x y a) : ℂ)) 1 1 kl = (((x+y-1)/Real.sqrt 2 : ℝ) : ℂ) := by
    simp [bornVector,Fin.sum_univ_two,columns,rot,spec,amp x hx0,amp y hy0]
    have hd' : (x / Real.sqrt 2)*s*s + (y / Real.sqrt 2)*c*c = (x+y-1) / Real.sqrt 2 := by
      have hR : Real.sqrt 2 ≠ 0 := by positivity
      field_simp
      nlinarith [hsd]
    exact_mod_cast (by simpa only [mul_assoc,neg_mul_neg,one_div] using hd')
  unfold measuredCap
  simp only [Fin.sum_univ_two]
  rw [hf _ _ eq0,hf _ _ eq1]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  norm_num
  rw [sum_cap_square hsum0 hsum1]
  ring
/-- An actual rank-two, single-environment-dimensional local Kraus witness
for the cap envelope in the physical binary model. -/
private theorem rank_two_binary_attainment (x y : ℝ) (hx : 1≤x) (hy0 : 0≤y) (hy1 : y≤1)
    (hn : x^2+y^2=2) :
    ∃ A : LocalColumns (Fin 2) (Fin 2) (Fin 1),
      measuredCap 1 ⟨2,2,1,1,fun a => if a=0 then x^2/2 else y^2/2,A,A⟩ =
        (1+(x+y-1)^2)/2 := by
  obtain ⟨t,ht0,ht1,ht⟩ : ∃ t : ℝ, 0≤t ∧ t≤1 ∧ x*t+y*(1-t)=1 := by
    by_cases he : x=y
    · exact ⟨0,by norm_num,by norm_num,by nlinarith⟩
    have hxy : 0 < x-y := by
      have hh : y < x := lt_of_le_of_ne (hy1.trans hx) (Ne.symm he)
      linarith
    refine ⟨(1-y)/(x-y),div_nonneg (by linarith) hxy.le,
      (div_le_iff₀ hxy).mpr (by linarith),?_⟩
    field_simp
    ring
  let c := Real.sqrt t
  let s := Real.sqrt (1-t)
  have hcs := Real.sq_sqrt ht0
  have hss := Real.sq_sqrt (sub_nonneg.mpr ht1)
  have hrot : c^2+s^2=1 := by dsimp [c,s]; rw [hcs,hss]; ring
  have hdiag : x*c^2+y*s^2=1 := by dsimp [c,s]; rwa [hcs,hss]
  exact ⟨columns c s hrot,measured_attains x y (by linarith) hy0 hn c s hrot hdiag⟩
private theorem score_identity (x y : ℝ) (hx : 1≤x) (hy0 : 0≤y) (hy1 : y≤1) :
    RTCriticalOverlap.spectralScore 2 (fun a : Fin 2 => if a=0 then x^2/2 else y^2/2) =
      (x+y^2)/2 := by
  have hhalfSqrt (z : ℝ) (hz : 0≤z) : Real.sqrt ((z^2/2)/2)=z/2 := by
    have h : (z^2/2)/2=(z/2)^2 := by ring
    rw [h,Real.sqrt_sq (by linarith)]
  have hx' : x/2≤x^2/2 := by nlinarith [mul_nonneg (show 0≤x by linarith) (sub_nonneg.mpr hx)]
  have hy' : y^2/2≤y/2 := by nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  unfold RTCriticalOverlap.spectralScore
  rw [Fin.sum_univ_two]
  change min (x^2/2) (Real.sqrt ((x^2/2)/2)) +
    min (y^2/2) (Real.sqrt ((y^2/2)/2)) = (x+y^2)/2
  rw [hhalfSqrt x (by linarith),hhalfSqrt y hy0,min_eq_right hx',min_eq_left hy']
  ring
/-- Each admissible scalar coefficient is realized exactly by the same
physical source/column/cap map as in the protected overlap theorem. -/
private theorem arc_ratio_realized (u : ℝ) (hu : u∈Set.Icc (0:ℝ) (Real.sqrt 2-1)) :
    let x := RTBinaryCritical.arcX u
    let y := RTBinaryCritical.arcY u
    let p : Fin 2 → ℝ := fun a => if a=0 then x^2/2 else y^2/2
    (∑ a,p a)=1 ∧
      ∃ A : LocalColumns (Fin 2) (Fin 2) (Fin 1),
        measuredCap 1 ⟨2,2,1,1,p,A,A⟩ /
          RTCriticalOverlap.spectralScore 2 p = RTBinaryCritical.ratio u := by
  dsimp only
  let x := RTBinaryCritical.arcX u
  let y := RTBinaryCritical.arcY u
  obtain ⟨hx,hy0,hy1,hn,_,hR⟩ := RTBinaryCritical.arc_evaluation u hu
  change 1≤x at hx
  change 0≤y at hy0
  change y≤1 at hy1
  change x^2+y^2=2 at hn
  change RTBinaryCritical.ratio u = (1+(x+y-1)^2)/(x+y^2) at hR
  obtain ⟨A,hA⟩ := rank_two_binary_attainment x y hx hy0 hy1 hn
  refine ⟨?_,⟨A,?_⟩⟩
  · simp [Fin.sum_univ_two]
    linarith
  · rw [hA,score_identity x y hx hy0 hy1,hR]
    have hz : x+y^2≠0 := by nlinarith
    field_simp
end RTBinaryAttainment
namespace RTSharp.Flat
noncomputable section
private theorem scale_min (m a b : ℝ) (hm : 0 ≤ m) :
    m * min a b = min (m*a) (m*b) := by
  rcases le_total a b with h|h
  · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h hm)]
  · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h hm)]
private theorem spectral_normalize {I : Type*} [Fintype I] (m : ℕ) (hm : m > 0)
    (amplitude : I → ℝ) (h : ∀ i, 0 ≤ amplitude i) :
    (m:ℝ) * RTCriticalOverlap.spectralScore m (fun i => amplitude i ^ 2 / (m:ℝ)) =
      ∑ i, min (amplitude i ^ 2) (amplitude i) := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  unfold RTCriticalOverlap.spectralScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs : Real.sqrt (amplitude i ^ 2 / (m:ℝ) / (m:ℝ)) = amplitude i / (m:ℝ) := by
    rw [div_div, ← sq, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (h i),
      Real.sqrt_sq hm'.le]
  rw [hs, scale_min _ _ _ hm'.le]
  congr 1 <;> field_simp
end
end RTSharp.Flat
open RTBinaryCritical RTBinary
noncomputable section
private theorem two_cap_normalization {I K V : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [Fintype V]
    (A : LocalColumns I (Fin 2) K) (B : LocalColumns I (Fin 2) V)
    (p : I → ℝ) (_hp : ∀ a, 0 ≤ p a) :
    (2:ℝ)*(∑ i : Fin 2, min (1/2) ((lnorm (bornVector A B
      (fun a => (Real.sqrt (p a):ℂ)) i i))^2)) =
      ∑ i : Fin 2, min 1 (lsquare (bornVector A B
        (fun a => (Real.sqrt (2*p a):ℂ)) i i)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [RTSharp.Flat.scale_min _ _ _ (by norm_num),sqNorm]
  norm_num only
  congr 1
  have hs (uv : K×V) : bornVector A B (fun a => (Real.sqrt (2*p a):ℂ)) i i uv =
      ((Real.sqrt 2:ℝ):ℂ)*bornVector A B (fun a => (Real.sqrt (p a):ℂ)) i i uv := by
    simp only [bornVector,Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Complex.ofReal_mul,
      mul_assoc,Finset.mul_sum]
  simp only [lsquare,hs,Complex.norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),
    Finset.mul_sum]
private theorem normalized_score_formula {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, (x i)^2 = 2) (j : I) (hj : 1 ≤ x j) :
    (∑ i, min ((x i)^2) (x i)) = x j + (2-(x j)^2) := by
  classical
  have hl (i : I) (hne : i≠j) : x i ≤ 1 := by
    have hpair : (x i)^2+(x j)^2 ≤ (2:ℝ) := by
      rw [← hs]
      calc
        _ = ∑ a ∈ ({i,j} : Finset I), (x a)^2 := by simp [hne]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => sq_nonneg _)
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < x i+1 by linarith [hx i]),
      mul_nonneg (sub_nonneg.mpr hj) (show 0 ≤ x j+1 by linarith)]
  have hterm (i : I) : min ((x i)^2) (x i) = (x i)^2 + (if i=j then x j-(x j)^2 else 0) := by
    by_cases hh : i=j
    · subst i
      rw [min_eq_right (by nlinarith : x j ≤ (x j)^2), ite_eq_left rfl]
      ring
    · have hi : x i ≤ 1 := hl i hh
      rw [min_eq_left (by nlinarith [mul_nonneg (hx i) (sub_nonneg.mpr hi)]),ite_eq_right hh,add_zero]
  simp only [hterm,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hs]
  ring
def BinaryCapLaw (observed : CapExperiment → ℝ) : Prop :=
    ∃ u : ℝ, u ∈ Set.Icc (0:ℝ) (Real.sqrt 2-1) ∧ criticalPoly u = 0 ∧
      1084871396888/1000000000000 < ratio u ∧
      ratio u < 1084871396892/1000000000000 ∧
      (∀ X : CapExperiment, X.labels=2 → (∀ a, 0 < X.spectrum a) →
        (∑ a, X.spectrum a)=1 →
        observed X ≤ ratio u*RTCriticalOverlap.spectralScore 2 X.spectrum) ∧
      ∃ X : CapExperiment, X.labels=2 ∧ X.rank=2 ∧ (∀ a, 0 < X.spectrum a) ∧
        (∑ a,X.spectrum a)=1 ∧ observed X=ratio u*RTCriticalOverlap.spectralScore 2 X.spectrum
/-- The exact largest coherent overlap-to-score ratio at two labels, including
the attaining rank-two finite local isometries. -/
theorem actual_binary_maximum :
    let observed := measuredCap 1
    BinaryCapLaw observed := by
  change BinaryCapLaw (measuredCap 1)
  unfold BinaryCapLaw
  obtain ⟨u,hu,hP,_,_,hR0,hR1,hpl,hpu,hmax⟩ := unique_global_scalar_maximum
  refine ⟨u,hu,hP,hR0,hR1,?_,?_⟩
  · rintro ⟨r,n,K,V,p,A,B⟩ hn hp hps
    change n=2 at hn
    subst n
    let x : Fin r → ℝ := fun i => Real.sqrt (2*p i)
    have hx (i : Fin r) : 0 ≤ x i := Real.sqrt_nonneg _
    have hsq (i : Fin r) : (x i)^2 = 2*p i := Real.sq_sqrt (by linarith [hp i])
    have hxt : ∑ i, (x i)^2 = 2 := by simp only [hsq,← Finset.mul_sum,hps,mul_one]
    have his : (fun i => (x i)^2/(2:ℝ))=p := by
      funext i
      rw [hsq]
      ring
    have hZ := RTSharp.Flat.spectral_normalize 2 (by decide) x hx
    change (2:ℝ)*RTCriticalOverlap.spectralScore 2 (fun i => (x i)^2 / (2:ℝ)) = _ at hZ
    rw [his] at hZ
    have hO := two_cap_normalization A B p (fun a => (hp a).le)
    have hO' : (2:ℝ) * measuredCap 1 ⟨r,2,K,V,p,A,B⟩ =
        ∑ i : Fin 2, min 1 (lsquare (bornVector A B (fun a => (x a:ℂ)) i i)) := by
      simpa only [measuredCap, Nat.cast_one, show (1:ℝ)+1=2 by norm_num, x] using hO
    change measuredCap 1 ⟨r,2,K,V,p,A,B⟩ ≤ ratio u*RTCriticalOverlap.spectralScore 2 p
    apply le_of_mul_le_mul_left _ (by norm_num : (0:ℝ)<2)
    rw [hO',mul_left_comm,hZ]
    by_cases hh : ∃ j, 1 ≤ x j
    · obtain ⟨j,hj⟩ := hh
      let y := Real.sqrt (2-(x j)^2)
      have hrem : 0 ≤ 2-(x j)^2 := by
        rw [sub_nonneg,←hxt]
        exact Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ j)
      have hy0 : 0 ≤ y := Real.sqrt_nonneg _
      have hys : y^2=2-(x j)^2 := Real.sq_sqrt hrem
      have hy : y ≤ 1 := by nlinarith only [hys, hj, sq_nonneg (x j-1), sq_nonneg (y-1), hy0]
      obtain ⟨v,hv,hvx,hvy⟩ := arc_surjects (x j) y hj hy0 hy (by linarith)
      have hvr : ratio v ≤ ratio u := by
        by_cases hh : v=u
        · simp [hh]
        · exact (hmax v hv hh).le
      have hve := (arc_evaluation v hv).2.2.2.2.2
      rw [hvx,hvy] at hve
      have hpz : 0 < x j+y^2 := by nlinarith [sq_nonneg y]
      have hb : 1+(x j+y-1)^2 ≤ ratio u*(x j+y^2) :=
        (div_le_iff₀ hpz).mp (hve ▸ hvr)
      have hc := two_label_actual_cap A B x hx hxt j hj
      rw [normalized_score_formula x hx hxt j hj, ← hys]
      exact hc.trans hb
    · push Not at hh
      have hZ' : (∑ i, min ((x i)^2) (x i)) = 2 := by
        rw [←hxt]
        apply Finset.sum_congr rfl
        intro i _
        exact min_eq_left (by nlinarith [mul_nonneg (hx i) (sub_nonneg.mpr (hh i).le)])
      rw [hZ']
      have hcap : (∑ i : Fin 2, min 1 (lsquare (bornVector A B (fun a => (x a:ℂ)) i i))) ≤ 2 := by
        simp only [Fin.sum_univ_two]
        exact (add_le_add (min_le_left _ _) (min_le_left _ _)).trans (by norm_num)
      linarith
  · let x := arcX u
    let y := arcY u
    let p : Fin 2 → ℝ := fun a => if a=0 then x^2/2 else y^2/2
    obtain ⟨hx,hy,_,_,hpY,_⟩ := arc_evaluation u hu
    obtain ⟨hN,A,hA⟩ := RTBinaryAttainment.arc_ratio_realized u hu
    change (∑ a,p a)=1 at hN
    change measuredCap 1 ⟨2,2,1,1,p,A,A⟩ / RTCriticalOverlap.spectralScore 2 p = ratio u at hA
    have hp (i : Fin 2) : 0 < p i := by
      dsimp [p]
      split_ifs with hh
      · change 1 ≤ x at hx
        exact div_pos (sq_pos_of_pos (by linarith : 0<x)) (by norm_num)
      · change smallProb u=y^2/2 at hpY
        rw [← hpY]
        linarith
    have hZ : 0 < RTCriticalOverlap.spectralScore 2 p := by
      unfold RTCriticalOverlap.spectralScore
      refine Finset.sum_pos (fun a _ => lt_min (hp a) (Real.sqrt_pos_of_pos (div_pos (hp a) (by norm_num)))) ?_
      exact Finset.univ_nonempty
    refine ⟨⟨2,2,1,1,p,A,A⟩,rfl,rfl,hp,hN,?_⟩
    exact (div_eq_iff hZ.ne').mp hA
end
end D5.S3.Quantum.Entanglement.SectorChannels.UniformBinarySchmidtOverlap
