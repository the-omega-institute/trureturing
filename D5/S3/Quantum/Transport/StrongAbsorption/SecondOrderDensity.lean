/- GID: D5/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity
   generality: G
   mirror-B: D5/B/S3/Quantum/Transport/StrongAbsorption/SecondOrderDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic cross-density estimates. -/

/-
admission_basis: escape-witness
escape_witness: finiteProduct_quadratic_remainder_precise; crossIntegral_secondOrder
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19485
proof_shape: bind-only for quadraticSum_insert, quadraticSum_abs_nonneg, quadraticSum_abs_bound, product_budget_two, quadraticDensityPoly, quadraticDensityPoly_eval, cross_squared_sum, quadraticSum_cross, cross_absolute_product_bound, integral_cubic_bigO, exponential_tail_power, crossIntegral_tail_power, quotient_constant_secondOrder.
proof_shape: content for finiteProduct_quadratic_remainder_precise, finiteProduct_quadratic_remainder, crossProduct_secondOrder_bound, crossIntegral_secondOrder, cutoffIntegral_secondOrder, law_polynomial_secondOrder.
Consumers: each helper is used by the later estimates or moment assembly; result is terminal.
Frozen dependency identities at merged base (declaration statement_id; publicized names correspond to their original private declarations): D5.S3.Quantum.Transport.StrongAbsorption.Density.basePolynomial_integrable = sha256:0db1c7d896c7af185e002ed8398e75cf169d275a3d5712a7d65ae6607ecbe8d6; D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight = sha256:d96d00410d62d0396fa5f38bce6c50b759eb11b615d463ac7dca53e02a2db8ef; D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_eq_zero_off_orthant = sha256:e961e3166d1030f27fac872a3825253ddd24c5b966694a098f2ef15bee5ac663; D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_mass = sha256:a8fde99342f74b451374925bfab2d86e62f9a360cea356718612c5a7aaaaf322; D5.S3.Quantum.Transport.StrongAbsorption.Density.baseWeight_nonneg = sha256:913f42546ef9347276bddeff402ec1d793054c584bb44f6f0f2e64ee5c2f041e; D5.S3.Quantum.Transport.StrongAbsorption.Density.budgetPoly = sha256:4c541a4d04a8d5a26474bdad91a91c9059ad8137f4144a6c336ce99ad5f1b14d; D5.S3.Quantum.Transport.StrongAbsorption.Density.budgetPoly_eval = sha256:4dbd2cfee317204a8c01ef2dd1cf1e97f00a529f7b582a2512b027c31aaede0c; D5.S3.Quantum.Transport.StrongAbsorption.Density.budgetPoly_nonneg = sha256:24c1ec53838b9333ad61c93c495186b0100d3fc715e11a6156329fdec7b66f04; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossIntegral = sha256:a83281407227967bab7c49a37db404fa3e23a47b5f222d8a2692e4620217d08c; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossIntegrand_integrable = sha256:4e861e34a0c66536fcabeba4d468cf6d6f5356a7cc0d78b4d62f2826f12d93a5; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossProduct = sha256:90840c7537cfd9a02e1abb8a2049d58bcb65d94e52a7ad37831668f465836dac; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossProduct_abs_bound = sha256:2e8512e2c0ef3b1243dca6a74e07d48850540916680bfc979b3a0a2b8eb02c4a; D5.S3.Quantum.Transport.StrongAbsorption.Density.crossProduct_firstOrder = sha256:a7fc0bfa3a4fcecd92f2e5a788bf812977c20034fa4a26fde87f6e9a297fdd68; D5.S3.Quantum.Transport.StrongAbsorption.Density.cutoffIntegral = sha256:9c176103775259e2c2aadd2065acc6ea8f69b0a3aebe9cfe01eb769953e931c3; D5.S3.Quantum.Transport.StrongAbsorption.Density.cutoffIntegral_eq_sub = sha256:8a98afcac2020d8555494797bc90eb90257f94455a1bba9105d1acf0fd52abf9; D5.S3.Quantum.Transport.StrongAbsorption.Density.cutoffIntegral_firstOrder = sha256:09952645d6123ec0a13b1cacdabdd4fc28d8678d099ea66c48c8700f14c75234; D5.S3.Quantum.Transport.StrongAbsorption.Density.jointSum = sha256:e601501386bd621533f446a63c1f11643b99f719c59f8b84c21c169e4d143bcc; D5.S3.Quantum.Transport.StrongAbsorption.Density.law_polynomial_ratio = sha256:fb5e31de612d0a99059f93046298c707d053488f868a2c679156663640b260f1; D5.S3.Quantum.Transport.StrongAbsorption.Density.linearDensityIntegral_zero = sha256:5867026755d3e1a2d5d7f7e2ec7b1e04c8a1029c34c6af7917c902fbee0ad1df; D5.S3.Quantum.Transport.StrongAbsorption.Density.linearDensityPoly = sha256:33e1d063c468969aaae34e14f1d799a5f10bed07712cd895b5a6e910bdfbb96a; D5.S3.Quantum.Transport.StrongAbsorption.Density.linearDensityPoly_eval = sha256:5d6654e44de6dd05bf279eb8114e4c404e9d4816beea39e955900735ea4c35b9; D5.S3.Quantum.Transport.StrongAbsorption.Density.tailSet = sha256:9e7b8c0441bcc3719db366bac6de23c71949f8172f493897b7aaa01ee7ae79e9; D5.S3.Quantum.Transport.StrongAbsorption.Density.tail_family_exponential_bound = sha256:5e332bf574285f956b157411ad2a74c0689d4ceea3650b45b423e2df7e1e5f24; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.FirstOrder = sha256:b464864096def8aa1bad012b7955b44cf3f4e556a523d4905b952b7c4baa6c8d; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.FirstOrder.tendsto = sha256:458b3da540ff254b6898c6742b4f4a61aeeb9265697d2d54787d7ad02be4c896; D5.S3.Quantum.Transport.StrongAbsorption.Foundations.law = sha256:234165c5a68f4041955a51a3f8cb7722d9ba23a543b735e842287b1f79724b97; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition = sha256:db7289f09641ff884c230527f9df4880ff3fc29a942837cf011b5ba39670daf1; D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments.partition_pos = sha256:d09595e6e604883819d6f3859e5f7bcdc2510a00edcf51645c7a340cd12a5bea.
-/

import D5.S3.Quantum.Transport.StrongAbsorption.Foundations
import D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments
import D5.S3.Quantum.Transport.StrongAbsorption.Density

namespace D5.S3.Quantum.Transport.StrongAbsorption.SecondOrderDensity
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations
open D5.S3.Quantum.Transport.StrongAbsorption.LaguerreMoments
open D5.S3.Quantum.Transport.StrongAbsorption.Density
open MeasureTheory ProbabilityTheory Set Real Finset Filter Asymptotics MvPolynomial
open scoped Topology
set_option maxHeartbeats 2000000

private theorem quadraticSum_insert {σ : Type*} [DecidableEq σ] (s : Finset σ) (a : σ → ℝ)
    (i : σ) (hi : i ∉ s) :
    (((∑ k ∈ (insert i s), (a) k)^2 - ∑ k ∈ (insert i s), ((a) k)^2)/2) = (((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2)+a i*(∑ j ∈ s, a j) := by
  simp only [sum_insert hi]
  ring

private theorem quadraticSum_abs_nonneg {σ : Type*} (s : Finset σ) (a : σ → ℝ) :
    0 ≤ (((∑ k ∈ s, ((fun i => |a i|)) k)^2 - ∑ k ∈ s, (((fun i => |a i|)) k)^2)/2) := by
  exact div_nonneg (sub_nonneg.mpr (sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg (a i)))) (by norm_num)

private theorem quadraticSum_abs_bound {σ : Type*} (s : Finset σ) (a : σ → ℝ) :
    |(((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2)| ≤ (((∑ k ∈ s, ((fun i => |a i|)) k)^2 - ∑ k ∈ s, (((fun i => |a i|)) k)^2)/2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp []
  | @insert i s hi ih =>
    rw [quadraticSum_insert s a i hi, quadraticSum_insert s (fun i => |a i|) i hi]
    calc
      _ ≤ |(((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2)|+|a i*(∑ j ∈ s, a j)| := abs_add_le _ _
      _ ≤ (((∑ k ∈ s, ((fun i => |a i|)) k)^2 - ∑ k ∈ s, (((fun i => |a i|)) k)^2)/2)+|a i| *(∑ j ∈ s, |a j|) := by
        rw [abs_mul]
        exact add_le_add ih (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _))

private theorem product_budget_two {σ : Type*} (s : Finset σ) (a : σ → ℝ) :
    1+(∑ i ∈ s, |a i|)+(((∑ k ∈ s, ((fun i => |a i|)) k)^2 - ∑ k ∈ s, (((fun i => |a i|)) k)^2)/2) ≤ ∏ i ∈ s, (1+|a i|) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp []
  | @insert i s hi ih =>
    rw [quadraticSum_insert s (fun i => |a i|) i hi, Finset.sum_insert hi, Finset.prod_insert hi]
    have hm := mul_le_mul_of_nonneg_left ih (show 0 ≤ 1+|a i| by positivity)
    have hq := mul_nonneg (abs_nonneg (a i)) (quadraticSum_abs_nonneg s a)
    nlinarith

private theorem finiteProduct_quadratic_remainder_precise {σ : Type*} (s : Finset σ) (a : σ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |(∏ i ∈ s, (1+t*a i))-1-t*(∑ i ∈ s, a i)-t^2*(((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2)| ≤
      t^3*((∏ i ∈ s, (1+|a i|))-1-(∑ i ∈ s, |a i|)-(((∑ k ∈ s, ((fun i => |a i|)) k)^2 - ∑ k ∈ s, (((fun i => |a i|)) k)^2)/2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp []
  | @insert i s hi ih =>
    rw [quadraticSum_insert s a i hi, quadraticSum_insert s (fun i => |a i|) i hi,
      Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    let E := (∏ j ∈ s, (1+t*a j))-1-t*(∑ j ∈ s, a j)-t^2*(((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2)
    let B := (∏ j ∈ s, (1+|a j|))-1-(∑ j ∈ s, |a j|)-(((∑ k ∈ s, ((fun j => |a j|)) k)^2 - ∑ k ∈ s, (((fun j => |a j|)) k)^2)/2)
    have hB : 0 ≤ B := by have := product_budget_two s a; dsimp [B]; linarith
    have hfactor : |1+t*a i| ≤ 1+|a i| := by
      calc
        _ ≤ |(1 : ℝ)|+|t*a i| := abs_add_le _ _
        _ = 1+t*|a i| := by rw [abs_one, abs_mul, abs_of_nonneg ht]
        _ ≤ _ := by nlinarith [abs_nonneg (a i)]
    have he : (1+t*a i)*(∏ j ∈ s, (1+t*a j))-1-t*(a i+∑ j ∈ s, a j)-
        t^2*((((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2)+a i*(∑ j ∈ s, a j)) =
        E*(1+t*a i)+t^3*a i*(((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2) := by dsimp [E]; ring
    rw [he]
    calc
      _ ≤ |E*(1+t*a i)|+|t^3*a i*(((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2)| := abs_add_le _ _
      _ = |E| *|1+t*a i|+t^3*|a i| *|(((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2)| := by
        simp only [abs_mul,abs_of_nonneg (pow_nonneg ht 3)]
      _ ≤ (t^3*B)*(1+|a i|)+t^3*|a i| *(((∑ k ∈ s, ((fun j => |a j|)) k)^2 - ∑ k ∈ s, (((fun j => |a j|)) k)^2)/2) := by
        apply add_le_add
        · exact mul_le_mul ih hfactor (abs_nonneg _) (mul_nonneg (pow_nonneg ht 3) hB)
        · exact mul_le_mul_of_nonneg_left (quadraticSum_abs_bound s a) (by positivity)
      _ = _ := by dsimp [B]; ring

private theorem finiteProduct_quadratic_remainder {σ : Type*} (s : Finset σ) (a : σ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |(∏ i ∈ s, (1+t*a i))-1-t*(∑ i ∈ s, a i)-t^2*(((∑ k ∈ s, (a) k)^2 - ∑ k ∈ s, ((a) k)^2)/2)| ≤
      t^3*(∏ i ∈ s, (1+|a i|)) := by
  apply (finiteProduct_quadratic_remainder_precise s a ht ht1).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht 3)
  have hs := Finset.sum_nonneg (s := s) (fun i _ => abs_nonneg (a i))
  have hq := quadraticSum_abs_nonneg s a
  linarith

noncomputable def quadraticDensityPoly (M : ℕ) : MvPolynomial (Fin M ⊕ Fin M) ℝ :=
  C (1/2 : ℝ)*((linearDensityPoly M)^2-
    C (M : ℝ)*((∑ i : Fin M, (X (Sum.inl i))^2)+(∑ j : Fin M, (X (Sum.inr j))^2))+
    C 2*(∑ i : Fin M, X (Sum.inl i))*(∑ j : Fin M, X (Sum.inr j)))

private theorem quadraticDensityPoly_eval (M : ℕ) (p : (Fin M → ℝ) × (Fin M → ℝ)) :
    eval (Sum.elim p.1 p.2) (quadraticDensityPoly M) =
      (((M : ℝ)*((∑ i, p.1 i)-(∑ j, p.2 j)))^2-
        (M : ℝ)*((∑ i, p.1 i^2)+(∑ j, p.2 j^2))+2*(∑ i, p.1 i)*(∑ j, p.2 j))/2 := by
  simp [quadraticDensityPoly,linearDensityPoly_eval,map_sum]
  ring

private theorem cross_squared_sum (M : ℕ) (x y : Fin M → ℝ) :
    (∑ p : Fin M × Fin M, (x p.1-y p.2)^2) =
      (M : ℝ)*((∑ i, x i^2)+(∑ j, y j^2))-2*(∑ i, x i)*(∑ j, y j) := by
  rw [Fintype.sum_prod_type]
  simp only [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, sum_const, card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

private theorem quadraticSum_cross (M : ℕ) (x y : Fin M → ℝ) :
    (((∑ k ∈ univ, ((fun p : Fin M × Fin M => x p.1-y p.2)) k)^2 - ∑ k ∈ univ, (((fun p : Fin M × Fin M => x p.1-y p.2)) k)^2)/2) =
      eval (Sum.elim x y) (quadraticDensityPoly M) := by
  rw [crossProduct_firstOrder, cross_squared_sum,quadraticDensityPoly_eval M (x,y)]
  ring

private theorem cross_absolute_product_bound {M : ℕ} (x y : Fin M → ℝ)
    (hx : ∀ i, 0≤x i) (hy : ∀ j, 0≤y j) :
    (∏ p : Fin M × Fin M, (1+|x p.1-y p.2|)) ≤ (1+(∑ i, x i)+(∑ j, y j))^(M^2) := by
  have hf (p : Fin M × Fin M) : 1+|x p.1-y p.2| ≤ 1+(∑ i, x i)+(∑ j, y j) := by
    have hxi := Finset.single_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) => hx i) (mem_univ p.1)
    have hyj := Finset.single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin M))) => hy j) (mem_univ p.2)
    have ha : |x p.1-y p.2| ≤ x p.1+y p.2 := abs_le.mpr ⟨by linarith [hx p.1],by linarith [hy p.2]⟩
    linarith
  calc
    _ ≤ ∏ _p : Fin M × Fin M, (1+(∑ i, x i)+(∑ j, y j)) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun p _ => hf p)
    _ = _ := by simp [Fintype.card_prod,pow_two]

private theorem crossProduct_secondOrder_bound {M : ℕ} {t : ℝ} (ht : 0≤t) (ht1 : t≤1)
    (p : (Fin M → ℝ) × (Fin M → ℝ)) (hx : ∀ i, 0≤p.1 i) (hy : ∀ j, 0≤p.2 j) :
    |crossProduct M t p.1 p.2-1-t*eval (Sum.elim p.1 p.2) (linearDensityPoly M)-
        t^2*eval (Sum.elim p.1 p.2) (quadraticDensityPoly M)| ≤
      t^3*(1+(∑ i, p.1 i)+(∑ j, p.2 j))^(M^2) := by
  have h := finiteProduct_quadratic_remainder univ (fun q : Fin M × Fin M => p.1 q.1-p.2 q.2) ht ht1
  rw [quadraticSum_cross, crossProduct_firstOrder, ← linearDensityPoly_eval] at h
  have he : (∏ q : Fin M × Fin M, (1+t*(p.1 q.1-p.2 q.2))) = crossProduct M t p.1 p.2 := by
    rw [Fintype.prod_prod_type]
    rfl
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (cross_absolute_product_bound p.1 p.2 hx hy) (pow_nonneg ht 3))

private theorem integral_cubic_bigO {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ℝ → Ω → ℝ) (g : Ω → ℝ) (hg : Integrable g μ)
    (h : ∀ᶠ γ : ℝ in atTop, ∀ᵐ p ∂μ, |f γ p|≤γ⁻¹^3*g p) :
    (fun γ => ∫ p, f γ p ∂μ) =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
  apply IsBigO.of_bound (∫ p, g p ∂μ)
  filter_upwards [h,eventually_ge_atTop (1 : ℝ)] with γ hγ hG
  have ht : 0≤γ⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hG)
  have hi := norm_integral_le_of_norm_le (f := f γ) (hg.const_mul (γ⁻¹^3))
    (by simpa only [Real.norm_eq_abs] using hγ)
  rw [integral_const_mul] at hi
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht 3),mul_comm] using hi

private theorem crossIntegral_secondOrder {M : ℕ} {a : ℝ} (ha : 0<a)
    (P : MvPolynomial (Fin M ⊕ Fin M) ℝ) :
    (fun γ => crossIntegral M a γ⁻¹ P-
      (∫ p, baseWeight M a p*eval (Sum.elim p.1 p.2) P)-
      γ⁻¹*(∫ p, baseWeight M a p*eval (Sum.elim p.1 p.2) (P*linearDensityPoly M))-
      γ⁻¹^2*(∫ p, baseWeight M a p*eval (Sum.elim p.1 p.2) (P*quadraticDensityPoly M)))
       =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
  let R := fun γ p => baseWeight M a p*eval (Sum.elim p.1 p.2) P*
    (crossProduct M γ⁻¹ p.1 p.2-1-γ⁻¹*eval (Sum.elim p.1 p.2) (linearDensityPoly M)-
      γ⁻¹^2*eval (Sum.elim p.1 p.2) (quadraticDensityPoly M))
  let g := fun p : (Fin M → ℝ) × (Fin M → ℝ) => baseWeight M a p*|eval (Sum.elim p.1 p.2) (P*budgetPoly M)|
  have hg : Integrable g := by
    simpa only [g,abs_mul,abs_of_nonneg (baseWeight_nonneg M a _)] using
      (basePolynomial_integrable ha (P*budgetPoly M)).abs
  have hR : (fun γ => ∫ p, R γ p) =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
    apply integral_cubic_bigO R g hg
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
    apply Eventually.of_forall
    intro p
    have hpos : 0<γ := lt_of_lt_of_le zero_lt_one hγ
    by_cases hp : p ∈ Set.Ici (0 : (Fin M → ℝ) × (Fin M → ℝ))
    · have hs : (∀ i, 0≤p.1 i) ∧ ∀ j, 0≤p.2 j := by
        simpa only [Function.const,Prod.le_def,Pi.le_def,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,Set.mem_Ici,forall_true_left] using hp
      have hb := crossProduct_secondOrder_bound (inv_nonneg.mpr hpos.le) ((inv_le_one₀ hpos).mpr hγ) p hs.1 hs.2
      dsimp only [R,g]
      rw [abs_mul,abs_mul,abs_of_nonneg (baseWeight_nonneg M a p),map_mul,abs_mul,
        abs_of_nonneg (budgetPoly_nonneg p hp),budgetPoly_eval]
      have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg (baseWeight_nonneg M a p) (abs_nonneg (eval (Sum.elim p.1 p.2) P)))
      simpa only [jointSum,mul_assoc,mul_left_comm,add_assoc] using hh
    · simp [R,g,baseWeight_eq_zero_off_orthant hp]
  apply hR.congr_left
  intro γ
  have he : R γ = fun p : (Fin M → ℝ) × (Fin M → ℝ) =>
    ((baseWeight M a p*eval (Sum.elim p.1 p.2) P*crossProduct M γ⁻¹ p.1 p.2-
      baseWeight M a p*eval (Sum.elim p.1 p.2) P)-
      γ⁻¹*(baseWeight M a p*eval (Sum.elim p.1 p.2) (P*linearDensityPoly M)))-
      γ⁻¹^2*(baseWeight M a p*eval (Sum.elim p.1 p.2) (P*quadraticDensityPoly M)) := by
    funext p
    simp only [R,map_mul]
    ring
  rw [he,integral_sub,integral_sub,integral_sub,integral_const_mul,integral_const_mul]
  · rfl
  all_goals first
    | exact crossIntegrand_integrable ha γ⁻¹ P
    | exact basePolynomial_integrable ha P
    | exact (basePolynomial_integrable ha (P*linearDensityPoly M)).const_mul γ⁻¹
    | exact (basePolynomial_integrable ha (P*quadraticDensityPoly M)).const_mul (γ⁻¹^2)
    | exact (crossIntegrand_integrable ha γ⁻¹ P).sub (basePolynomial_integrable ha P)
    | exact ((crossIntegrand_integrable ha γ⁻¹ P).sub (basePolynomial_integrable ha P)).sub
        ((basePolynomial_integrable ha (P*linearDensityPoly M)).const_mul γ⁻¹)

private theorem exponential_tail_power {c : ℝ} (hc : 0<c) (k : ℕ) :
    (fun γ : ℝ => Real.exp (-c*γ)) =O[atTop] (fun γ : ℝ => γ⁻¹^k) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hc (-(k : ℝ))).isBigO
  refine h.congr' Filter.EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with γ hγ
  simp only [Real.rpow_neg hγ,Real.rpow_natCast,inv_pow]

private theorem crossIntegral_tail_power {M : ℕ} {a : ℝ} (ha : 0<a)
    (P : MvPolynomial (Fin M ⊕ Fin M) ℝ) (k : ℕ) :
    (fun γ => ∫ p in tailSet M γ,
      baseWeight M a p*eval (Sum.elim p.1 p.2) P*crossProduct M γ⁻¹ p.1 p.2) =O[atTop]
       (fun γ : ℝ => γ⁻¹^k) := by
  let C := ∫ p, baseWeight M (a/2) p*|eval (Sum.elim p.1 p.2) (P*budgetPoly M)|
  have h : (fun γ => ∫ p in tailSet M γ,
      baseWeight M a p*eval (Sum.elim p.1 p.2) P*crossProduct M γ⁻¹ p.1 p.2)
      =O[atTop] (fun γ : ℝ => Real.exp (-(a/2)*γ)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
    have hpos : 0<γ := lt_of_lt_of_le zero_lt_one hγ
    have hh := tail_family_exponential_bound ha γ (P*budgetPoly M)
      (fun p => baseWeight M a p*eval (Sum.elim p.1 p.2) P*crossProduct M γ⁻¹ p.1 p.2) ?_
    · simpa [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),C,mul_comm,mul_left_comm,
        div_eq_mul_inv,mul_assoc] using hh
    · intro p
      by_cases hp : p ∈ Set.Ici (0 : (Fin M → ℝ) × (Fin M → ℝ))
      · have hs : (∀ i, 0≤p.1 i) ∧ ∀ j, 0≤p.2 j := by
          simpa only [Function.const,Prod.le_def,Pi.le_def,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,Set.mem_Ici,forall_true_left] using hp
        rw [abs_mul,abs_mul,abs_of_nonneg (baseWeight_nonneg M a p),map_mul,abs_mul,
          abs_of_nonneg (budgetPoly_nonneg p hp),budgetPoly_eval]
        have hb := crossProduct_abs_bound (inv_nonneg.mpr hpos.le) ((inv_le_one₀ hpos).mpr hγ) p.1 p.2 hs.1 hs.2
        simpa only [jointSum,mul_assoc,add_assoc] using mul_le_mul_of_nonneg_left hb
          (mul_nonneg (baseWeight_nonneg M a p) (abs_nonneg (eval (Sum.elim p.1 p.2) P)))
      · simp [baseWeight_eq_zero_off_orthant hp]
  exact h.trans (exponential_tail_power (by positivity : 0<a/2) k)

private theorem cutoffIntegral_secondOrder {M : ℕ} {a : ℝ} (ha : 0<a)
    (P : MvPolynomial (Fin M ⊕ Fin M) ℝ) :
    (fun γ => cutoffIntegral M a γ P-
      (∫ p, baseWeight M a p*eval (Sum.elim p.1 p.2) P)-
      γ⁻¹*(∫ p, baseWeight M a p*eval (Sum.elim p.1 p.2) (P*linearDensityPoly M))-
      γ⁻¹^2*(∫ p, baseWeight M a p*eval (Sum.elim p.1 p.2) (P*quadraticDensityPoly M)))
       =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
  have h := (crossIntegral_secondOrder ha P).sub (crossIntegral_tail_power ha P 3)
  apply h.congr_left
  intro γ
  rw [cutoffIntegral_eq_sub ha γ P]
  ring

private theorem quotient_constant_secondOrder {N D : ℝ → ℝ} {a b c z : ℝ} (hz : z≠0)
    (hDt : Tendsto D atTop (𝓝 z))
    (hD : (fun γ => D γ-z) =O[atTop] (fun γ : ℝ => γ⁻¹^3))
    (hN : (fun γ => N γ-a-b*γ⁻¹-c*γ⁻¹^2) =O[atTop] (fun γ : ℝ => γ⁻¹^3)) :
    (fun γ => N γ/D γ-a/z-(b/z)*γ⁻¹-(c/z)*γ⁻¹^2) =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
  let p := fun γ : ℝ => a/z+(b/z)*γ⁻¹+(c/z)*γ⁻¹^2
  have hpT : Tendsto p atTop (𝓝 (a/z)) := by
    have ht : Tendsto (fun γ : ℝ => γ⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
    simpa only [mul_zero,zero_pow (by omega : (2 : ℕ)≠0),add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul ht)).add (tendsto_const_nhds.mul (ht.pow 2))
  have hp : p =O[atTop] (fun _ => (1 : ℝ)) := isBigO_const_of_tendsto hpT one_ne_zero
  have hi : (fun γ => (D γ)⁻¹) =O[atTop] (fun _ => (1 : ℝ)) :=
    isBigO_const_of_tendsto (hDt.inv₀ hz) one_ne_zero
  have hDp : (fun γ => (D γ-z)*p γ) =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
    simpa only [mul_one] using hD.mul hp
  have h := (hN.sub hDp).mul hi
  refine h.congr' ?_ (Eventually.of_forall (fun _ => by simp))
  filter_upwards [hDt.eventually_ne hz] with γ hγ
  dsimp only [p]
  field_simp [hz,hγ]
  <;> ring

theorem law_polynomial_secondOrder {M : ℕ} (hM : 1≤M)
    (hD2 : (∫ p, baseWeight M M p*eval (Sum.elim p.1 p.2) (quadraticDensityPoly M)) = 0)
    (P : MvPolynomial (Fin M ⊕ Fin M) ℝ) :
    (fun γ => (∫ p, eval (Sum.elim p.1 p.2) P ∂law M γ)-
      (∫ p, baseWeight M M p*eval (Sum.elim p.1 p.2) P)/(partition M M)^2-
      γ⁻¹*((∫ p, baseWeight M M p*eval (Sum.elim p.1 p.2) (P*linearDensityPoly M))/(partition M M)^2)-
      γ⁻¹^2*((∫ p, baseWeight M M p*eval (Sum.elim p.1 p.2) (P*quadraticDensityPoly M))/(partition M M)^2))
       =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
  have hm : 0<(M : ℝ) := Nat.cast_pos'.mpr hM
  have hz : (partition M M)^2 ≠ 0 := pow_ne_zero _ (partition_pos M hm).ne'
  have hdt := cutoffIntegral_firstOrder hm (1 : MvPolynomial (Fin M ⊕ Fin M) ℝ)
  simp only [map_one,mul_one,one_mul,baseWeight_mass,linearDensityIntegral_zero] at hdt
  have hd := cutoffIntegral_secondOrder hm (1 : MvPolynomial (Fin M ⊕ Fin M) ℝ)
  simp only [map_one,mul_one,one_mul,baseWeight_mass,linearDensityIntegral_zero,hD2,mul_zero,sub_zero] at hd
  have hN : (fun γ => cutoffIntegral M M γ P-
    (∫ p, baseWeight M M p*eval (Sum.elim p.1 p.2) P)-
    (∫ p, baseWeight M M p*eval (Sum.elim p.1 p.2) (P*linearDensityPoly M))*γ⁻¹-
    (∫ p, baseWeight M M p*eval (Sum.elim p.1 p.2) (P*quadraticDensityPoly M))*γ⁻¹^2)
    =O[atTop] (fun γ : ℝ => γ⁻¹^3) := by
    simpa only [mul_comm] using cutoffIntegral_secondOrder hm P
  have h := quotient_constant_secondOrder hz hdt.tendsto hd hN
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with γ hγ
  rw [law_polynomial_ratio hM (lt_of_lt_of_le zero_lt_one hγ) P]
  ring

end D5.S3.Quantum.Transport.StrongAbsorption.SecondOrderDensity
