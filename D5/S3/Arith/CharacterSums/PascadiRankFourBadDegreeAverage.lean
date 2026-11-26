/- GID: D5/S3/Arith/CharacterSums/PascadiRankFourBadDegreeAverage
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiRankFourBadDegreeAverage
   mirror-E: none(waiver:rank-four-original-average)
   anchors: []
   utility: none
   digest: The rank-four stratum supplies the original maximum bad-degree average. -/

import D5.S3.Arith.CharacterSums.PascadiRankFourFactor
import D5.S3.Arith.CharacterSums.PascadiZeroDBadDegreeAverage

/-! Common rank-four factors put the actual maximizing family in the
zero Dixon stratum, where the full physical-weight average applies. -/

open Matrix Polynomial
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private def nonzeroBadPartners (p : ℕ) (q R V : Coordinate) (E : Finset Endpoint)
    (base : Endpoint) : Finset Endpoint :=
  (actualRecordBadPartners p q R V E base).filter
    (fun e => (pencil q base e).map (Int.castRingHom (ZMod p)) ≠ 0)

private def endpointRow (q : Coordinate) (e : Endpoint) : Fin 5 → ℤ :=
  ![coeffQ e, coeffR e, coeffS e, coeffL q e, coeffM q e]

private def selectedRows (q : Coordinate) (base : Endpoint) (S : Finset Endpoint) :
    Matrix (Option {e // e ∈ S}) (Fin 5) ℤ :=
  fun i => endpointRow q (i.elim base Subtype.val)

/-- One maximizing baseline, together with all its nonzero-reduction
derivative-zero partners, spans a rank-four rational row space. Empty
endpoint families satisfy the condition. -/
def actualRecordRankFour (p : ℕ) (q R V : Coordinate) (E : Finset Endpoint) : Prop :=
  E.Nonempty → ∃ base ∈ E,
    actualRecordBadDegree p q R V E = (actualRecordBadPartners p q R V E base).card ∧
    ((selectedRows q base (nonzeroBadPartners p q R V E base)).map (Int.castRingHom ℚ)).rank = 4

/-- The uniform height constant for the rank-four long-chart average. -/
def rankFourHeightConstant : ℝ := sixthHeightConstant ^ 2

private theorem rank_four_gaps (p B J : ℝ) (hp : 0 < p) (hB : 1 ≤ B)
    (hJ : 0 ≤ J) (hJB : J^2 ≤ B)
    (hgap : rankFourHeightConstant*B^13 < p^10) :
    2160*B^4 < p^4 ∧ 233280*B^6 < p^5 ∧ 93312*B^6*J < p^5 ∧
      sixthHeightConstant*B^6 < p^5 := by
  have hK : sixthHeightConstant = 10319560704 := by norm_num [sixthHeightConstant]
  have hK' : rankFourHeightConstant = 106493333123540975616 := by
    norm_num [rankFourHeightConstant, hK]
  have hpow (m n : ℕ) (h : m ≤ n) : B^m ≤ B^n := pow_le_pow_right₀ hB h
  have h6 : sixthHeightConstant*B^6 < p^5 := by
    apply (pow_lt_pow_iff_left₀ (by rw [hK]; positivity) (by positivity) (by decide : 2 ≠ 0)).mp
    calc
      (sixthHeightConstant*B^6)^2 = rankFourHeightConstant*B^12 := by
        unfold rankFourHeightConstant
        ring
      _ ≤ rankFourHeightConstant*B^13 :=
        mul_le_mul_of_nonneg_left (hpow 12 13 (by decide)) (by rw [hK']; norm_num)
      _ < (p^5)^2 := by convert hgap using 1 <;> ring
  refine ⟨?_, ?_, ?_, h6⟩
  · apply (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 5 ≠ 0)).mp
    calc
      (2160*B^4)^5 = 2160^5*B^20 := by ring
      _ ≤ rankFourHeightConstant^2*B^26 := mul_le_mul
        (by rw [hK']; norm_num) (hpow 20 26 (by decide)) (by positivity) (sq_nonneg _)
      _ = (rankFourHeightConstant*B^13)^2 := by ring
      _ < (p^10)^2 := pow_lt_pow_left₀ hgap (by rw [hK']; positivity) (by decide)
      _ = (p^4)^5 := by ring
  · exact (mul_le_mul_of_nonneg_right (by rw [hK]; norm_num) (by positivity : 0 ≤ B^6)).trans_lt h6
  · apply (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 2 ≠ 0)).mp
    calc
      (93312*B^6*J)^2 = (93312 : ℝ)^2*B^12*J^2 := by ring
      _ ≤ (93312 : ℝ)^2*B^12*B := mul_le_mul_of_nonneg_left hJB (by positivity)
      _ = (93312 : ℝ)^2*B^13 := by ring
      _ ≤ rankFourHeightConstant*B^13 :=
        mul_le_mul_of_nonneg_right (by rw [hK']; norm_num) (by positivity)
      _ < (p^5)^2 := by convert hgap using 1 <;> ring

private theorem residual_of_common_value (l m q r s : Fin 3 → ℤ) (θ χ : ℚ)
    (h : ∀ i, (q i : ℚ)+(r i : ℚ)*θ+(s i : ℚ)*θ^2 =
      χ*((l i : ℚ)+(m i : ℚ)*θ)) :
    PrimeCube.residual l m q r s = 0 := by
  let D {K : Type} [CommRing K] (a b c : Fin 3 → K) : K :=
    (!![a 0,b 0,c 0; a 1,b 1,c 1; a 2,b 2,c 2] : Matrix (Fin 3) (Fin 3) K).det
  let K {F : Type} [CommRing F] (l m q r s : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
    !![D r q l, D s q l+D r q m, D s q m;
       D s q l, D s r l+D s q m, D s r m;
       D m q l, D m r l, D m s l]
  change (K l m q r s).det = 0
  let L (i : Fin 3) : ℚ := l i
  let M (i : Fin 3) : ℚ := m i
  let Q (i : Fin 3) : ℚ := q i
  let R (i : Fin 3) : ℚ := r i
  let S (i : Fin 3) : ℚ := s i
  have hmap : (Int.castRingHom ℚ).mapMatrix (K l m q r s) = K L M Q R S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [K, D, L, M, Q, R, S, Matrix.det_fin_three]
  have hq : Q = fun i => χ*(L i+θ*M i)-θ*R i-θ^2*S i := by
    funext i
    change (q i : ℚ) = _
    dsimp [L, M, R, S]
    linear_combination h i
  have hmul : K L M Q R S *ᵥ ![1, θ, θ^2] = 0 := by
    funext i
    fin_cases i <;>
      simp [K, D, hq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.det_fin_three] <;>
      ring
  have hdet := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hmul
    (i := (0 : Fin 3)) (show (1 : ℚ) ∈ nonZeroDivisors ℚ from one_mem _)
  have hc : (Int.castRingHom ℚ) (K l m q r s).det = 0 := by
    rw [RingHom.map_det, hmap, hdet]
  exact Int.cast_eq_zero.mp (show ((K l m q r s).det : ℚ) = 0 from hc)

private theorem common_value_and_derivative (p : ℕ) (hp : p.Prime)
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (R V q : Coordinate) (base : Endpoint) (S : Finset Endpoint)
    (hr : IsUnit (R.1 : ZMod (p^3))) (ht : IsUnit (-(physical R V q).2 : ZMod (p^3)))
    (hbase : WordSolution (p^3) a₁ a₂ R V q base)
    (hword : ∀ e ∈ S, WordSolution (p^3) a₁ a₂ R V q e)
    (hx : IsUnit ((physical R V base.1).1 : ZMod (p^3)))
    (hy : IsUnit ((physical R V base.2).1 : ZMod (p^3)))
    (hk : IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical R V q).1 : ZMod (p^3))))
    (hder : ∀ e ∈ S, (pencil q base e).derivative.eval₂ (Int.castRingHom (ZMod p))
      ((ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)) (recordBeta (p^3) R V)) = 0) :
    ∃ b lam d : ℤ,
      IsUnit (((endpointL q base).eval b : ℤ) : ZMod p) ∧
      ∀ i : Option {e // e ∈ S},
        let e := i.elim base Subtype.val
        (p : ℤ)^3 ∣ (endpointQ e).eval b - lam*(endpointL q e).eval b ∧
        (p : ℤ) ∣ (endpointQ e).derivative.eval b - lam*(endpointL q e).derivative.eval b -
          d*(endpointL q e).eval b := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let β := (V.1 : ZMod (p^3))*(↑hr.unit⁻¹ : ZMod (p^3))
  let γ := (↑((ha₁.unit * ha₂.unit * ht.unit * hr.unit)⁻¹) : ZMod (p^3))
  let f := ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  let b : ℤ := β.val
  let lam : ℤ := γ.val
  have hb : (b : ZMod (p^3)) = β := by
    simpa only [b, Int.cast_natCast] using ZMod.natCast_zmod_val β
  have hl : (lam : ZMod (p^3)) = γ := by
    simpa only [lam, Int.cast_natCast] using ZMod.natCast_zmod_val γ
  have hb' : (b : ZMod p) = f β := by simpa only [map_intCast] using congrArg f hb
  have hl' : (lam : ZMod p) = f γ := by simpa only [map_intCast] using congrArg f hl
  have hβ : recordBeta (p^3) R V = β := by
    simp only [recordBeta, β, ← ZMod.inv_coe_unit, hr.unit_spec]
  have hL := (original_singular_unit_observations a₁ a₂ ha₁ ha₂ R V q base
    hr ht hbase hx hy hk).1.map f
  let ev (P : ℤ[X]) : ZMod p := P.eval₂ (Int.castRingHom (ZMod p)) (f β)
  let L (e : Endpoint) := ev (endpointL q e)
  let Q (e : Endpoint) := ev (endpointQ e)
  let L' (e : Endpoint) := ev (endpointL q e).derivative
  let Q' (e : Endpoint) := ev (endpointQ e).derivative
  have heval (P : ℤ[X]) : (Int.castRingHom (ZMod p)) (P.eval b) = ev P := by
    rw [← eval₂_at_apply]
    simp only [ev, Int.coe_castRingHom, hb']
  have heval₃ (P : ℤ[X]) :
      (Int.castRingHom (ZMod (p^3))) (P.eval b) =
        P.eval₂ (Int.castRingHom (ZMod (p^3))) β := by
    rw [← eval₂_at_apply]
    simp only [Int.coe_castRingHom, hb]
  have hLb : IsUnit (((endpointL q base).eval b : ℤ) : ZMod p) := by
    rw [← reduce_eval_at_lift f (endpointL q base) β b hb']
    exact hL
  have hLu : IsUnit (L base) := by
    change IsUnit ((Int.castRingHom (ZMod p)) ((endpointL q base).eval b)) at hLb
    rw [heval] at hLb
    exact hLb
  have hzero (e : Endpoint) (he : WordSolution (p^3) a₁ a₂ R V q e) :
      (endpointQ e).eval₂ (Int.castRingHom (ZMod (p^3))) β =
        γ * (endpointL q e).eval₂ (Int.castRingHom (ZMod (p^3))) β := by
    have hh := original_endpoint_identity a₁ a₂ ha₁ ha₂ R V q e hr ht he
    change -γ * _ + _ = 0 at hh
    linear_combination hh
  have hval (e : Endpoint) (he : WordSolution (p^3) a₁ a₂ R V q e) :
      Q e = f γ*L e := by
    have h := congrArg f (hzero e he)
    rw [map_mul, reduce_eval_at_lift f _ β b hb', reduce_eval_at_lift f _ β b hb'] at h
    change (Int.castRingHom (ZMod p)) ((endpointQ e).eval b) =
      f γ * (Int.castRingHom (ZMod p)) ((endpointL q e).eval b) at h
    simpa only [heval] using h
  let δ := (Q' base-f γ*L' base)/(L base)
  let d : ℤ := δ.val
  have hd : (d : ZMod p) = δ := by
    simpa only [d, Int.cast_natCast] using ZMod.natCast_zmod_val δ
  have hδ : δ*L base = Q' base-f γ*L' base :=
    div_mul_cancel₀ _ hLu.ne_zero
  refine ⟨b,lam,d,hLb,?_⟩
  · intro i
    dsimp only
    let e := i.elim base Subtype.val
    change (p : ℤ)^3 ∣ (endpointQ e).eval b - lam*(endpointL q e).eval b ∧
      (p : ℤ) ∣ (endpointQ e).derivative.eval b - lam*(endpointL q e).derivative.eval b -
        d*(endpointL q e).eval b
    have he : WordSolution (p^3) a₁ a₂ R V q e := by
      cases i with
      | none => exact hbase
      | some u => exact hword u.val u.property
    have hD : ev (pencil q base e).derivative = 0 := by
      cases i with
      | none => simp [e, pencil, ev]
      | some u => simpa only [hβ, e, ev, f, Option.elim_some] using hder u.val u.property
    have hDc : L' base*Q e+L base*Q' e-(L' e*Q base+L e*Q' base) = 0 := by
      simpa only [ev, pencil, derivative_sub, derivative_mul, eval₂_sub, eval₂_add,
        eval₂_mul, L, L', Q, Q'] using hD
    have heδ : Q' e-f γ*L' e-δ*L e = 0 := by
      have h := hDc
      rw [hval e he, hval base hbase] at h
      apply (mul_eq_zero.mp (show L base * (Q' e-f γ*L' e-δ*L e) = 0 by
        linear_combination h - L e*hδ)).resolve_left hLu.ne_zero
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      change (Int.castRingHom (ZMod (p^3))) ((endpointQ e).eval b) -
        (lam : ZMod (p^3)) * (Int.castRingHom (ZMod (p^3))) ((endpointL q e).eval b) = 0
      rw [heval₃, heval₃, hl, sub_eq_zero]
      exact hzero e he
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      change (Int.castRingHom (ZMod p)) ((endpointQ e).derivative.eval b) -
        (lam : ZMod p) * (Int.castRingHom (ZMod p)) ((endpointL q e).derivative.eval b) -
        (d : ZMod p) * (Int.castRingHom (ZMod p)) ((endpointL q e).eval b) = 0
      rw [heval, heval, heval, hl', hd]
      exact heδ

private theorem zero_dixon_of_rank_four_coordinates (p : ℕ) (hp : p.Prime)
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (q R V : Coordinate) (E : Finset Endpoint)
    (hr : IsUnit (R.1 : ZMod (p^3))) (ht : IsUnit (-(physical R V q).2 : ZMod (p^3)))
    (hk : IsUnit (1-a₁*a₂*(ht.unit : ZMod (p^3))*((physical R V q).1 : ZMod (p^3))))
    (I J : ℝ) (hJI : J ≤ I) (hJ : 1 ≤ J) (hq : CoordinateBound I J q)
    (hcoord : ∀ e ∈ E, CoordinateBound I J e.1 ∧ CoordinateBound I J e.2)
    (hword : ∀ e ∈ E, WordSolution (p^3) a₁ a₂ R V q e)
    (hunit : ∀ e ∈ E, IsUnit ((physical R V e.1).1 : ZMod (p^3)) ∧
      IsUnit ((physical R V e.2).1 : ZMod (p^3)))
    (hrank : actualRecordRankFour p q R V E)
    (hg₁ : 2160*(I*J)^4 < (p : ℝ)^4)
    (hg₂ : 233280*(I*J)^6 < (p : ℝ)^5)
    (hg₃ : 93312*(I*J)^6*J < (p : ℝ)^5) :
    actualRecordZeroDixon p q R V E := by
  classical
  intro hne
  obtain ⟨base, hbase, hmax, h4⟩ := hrank hne
  let S := nonzeroBadPartners p q R V E base
  let A := selectedRows q base S
  have hS (e : Endpoint) (he : e ∈ S) : e ∈ actualRecordBadPartners p q R V E base :=
    (Finset.mem_filter.mp he).1
  have hmem (e : Endpoint) (he : e ∈ S) : e ∈ E := (Finset.mem_filter.mp (hS e he)).1
  obtain ⟨b,lam,d,hL,hconditions⟩ := common_value_and_derivative p hp a₁ a₂ ha₁ ha₂ R V q
    base S hr ht (hword base hbase) (fun e he => hword e (hmem e he))
    (hunit base hbase).1 (hunit base hbase).2 hk
    (fun e he => (Finset.mem_filter.mp (hS e he)).2)
  have hbnd (i : Option {e // e ∈ S}) :=
    actual_coefficient_bounds I J q (i.elim base Subtype.val) hq
      (by cases i with
          | none => exact (hcoord base hbase).1
          | some e => exact (hcoord e.val (hmem e.val e.property)).1)
      (by cases i with
          | none => exact (hcoord base hbase).2
          | some e => exact (hcoord e.val (hmem e.val e.property)).2)
  obtain ⟨a,n,ha,_,_,_,hLn,_,_,hfactor⟩ :=
    (PrimeCube.rank_four_root_relevant_factor A p hp b lam d I J hJI hJ
      (fun i => (hbnd i).2.2.1) (fun i => (hbnd i).2.2.2.1)
      (fun i => (hbnd i).2.2.2.2) (fun i => (hbnd i).1) (fun i => (hbnd i).2.1)
      (fun i => by
        simpa [A,selectedRows,endpointRow,endpointL,endpointQ,PrimeCube.linear,PrimeCube.quadratic]
          using (hconditions i).1)
      (fun i => by
        convert (hconditions i).2 using 1
        simp [A,selectedRows,endpointRow,endpointL,endpointQ,PrimeCube.linear,PrimeCube.quadratic,
          derivative_pow]
        ring)
      hg₁ hg₂ hg₃).2 h4 none (by
        simpa [A,selectedRows,endpointRow,endpointL,PrimeCube.linear] using hL)
  let θ : ℚ := (n : ℚ)/(a : ℚ)
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  let ev := eval₂RingHom (Int.castRingHom ℚ) θ
  have hev (P : ℤ[X]) : ev P = P.eval₂ (Int.castRingHom ℚ) θ := rfl
  have hLQ : ev (endpointL q base) ≠ 0 := by
    intro hz
    have hz' : (coeffL q base : ℚ)+(coeffM q base : ℚ)*θ = 0 := by
      simpa only [hev, endpointL, PrimeCube.linear, eval₂_add,
        eval₂_mul, eval₂_C, eval₂_X, Int.coe_castRingHom] using hz
    have hneg : (a : ℚ)*(coeffL q base : ℚ)+(n : ℚ)*(coeffM q base : ℚ) = 0 := by
      dsimp [θ] at hz'
      field_simp at hz'
      linear_combination hz'
    apply hLn
    exact_mod_cast hneg
  have hf0 : ev (C a * X - C n) = 0 := by
    simp only [hev, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X,
      Int.coe_castRingHom, θ]
    field_simp
    ring
  let χ := ev (endpointQ base) / ev (endpointL q base)
  have hχ (e : Endpoint) (he : e = base ∨ e ∈ S) :
      ev (endpointQ e) = χ*ev (endpointL q e) := by
    rcases he with rfl | he
    · exact (div_mul_cancel₀ _ hLQ).symm
    · have hf : C a * X - C n ∣ pencil q base e := hfactor (some ⟨e, he⟩)
      obtain ⟨F,hF⟩ := hf
      have hz : ev (pencil q base e) = 0 := by
        rw [hF]
        change (eval₂RingHom (Int.castRingHom ℚ) θ) ((C a * X - C n)*F) = 0
        rw [map_mul]
        exact mul_eq_zero_of_left hf0 _
      simp only [pencil, map_sub, map_mul] at hz
      dsimp [χ]
      field_simp
      linear_combination hz
  have hχ' (x : Endpoint) (hx : x = base ∨ x ∈ S) :
      (coeffQ x : ℚ)+(coeffR x : ℚ)*θ+(coeffS x : ℚ)*θ^2 =
        χ*((coeffL q x : ℚ)+(coeffM q x : ℚ)*θ) := by
    simpa only [hev, endpointQ, endpointL, PrimeCube.quadratic,
      PrimeCube.linear, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow,
      Int.coe_castRingHom] using hχ x hx
  refine ⟨base,hbase,hmax,?_⟩
  intro e he e' he'
  apply residual_of_common_value _ _ _ _ _ θ χ
  intro j
  fin_cases j
  · exact hχ' base (.inl rfl)
  · exact hχ' e (.inr he)
  · exact hχ' e' (.inr he')

private theorem long_rank_four_bridge (p : ℕ) (hp : p.Prime) (X Y H : ℝ) (t w : ℤ)
    (B : ReducedMiddleBasis (p^3) t w X Y)
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (q : Coordinate) (E : Finset Endpoint)
    (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 < H) (hHsq : H^2 = X*Y) (hparameter : (w,t) ∈ literalBox X Y)
    (hq : physical B.R B.V q = (-w,-t))
    (hlong : ((p^3 : ℕ) : ℝ)^2 < H^2*weightedSq X Y B.R)
    (hr : IsUnit (B.R.1 : ZMod (p^3))) (ht : IsUnit (t : ZMod (p^3)))
    (hk : IsUnit (1+a₁*a₂*(t : ZMod (p^3))*(w : ZMod (p^3))))
    (hword : ∀ e ∈ E, WordSolution (p^3) a₁ a₂ B.R B.V q e)
    (heunit : ∀ e ∈ E, IsUnit ((physical B.R B.V e.1).1 : ZMod (p^3)) ∧
      IsUnit ((physical B.R B.V e.2).1 : ZMod (p^3)))
    (hebox : ∀ e ∈ E, physical B.R B.V e.1 ∈ literalBox X Y ∧
      physical B.R B.V e.2 ∈ literalBox X Y)
    (hrank : actualRecordRankFour p q B.R B.V E)
    (hgap : rankFourHeightConstant*(32*(X*Y/(p : ℝ)^3))^13 < (p : ℝ)^10) :
    actualRecordZeroDixon p q B.R B.V E ∧
      sixthHeightConstant*(32*(X*Y/(p : ℝ)^3))^6 < (p : ℝ)^5 := by
  have hc : 0 < p^3 := pow_pos hp.pos _
  let σ := Real.sqrt (weightedSq X Y B.R)
  have hQ : 0 < weightedSq X Y B.R := weightedSq_pos hX hY (B.first_ne_zero hc)
  have hσ : 0 < σ := Real.sqrt_pos.mpr hQ
  have hσsq : σ^2 = weightedSq X Y B.R := Real.sq_sqrt hQ.le
  have hσhi : weightedSq X Y B.R < 4*σ^2 := by rw [hσsq]; linarith
  let I := 8*H/σ
  let J := 4*H*σ/(p : ℝ)^3
  obtain ⟨horder, hJ₂, hprod, _⟩ := B.long_scale_bounds hc hX hY H σ
    hH hHsq hσ hσsq.le hσhi hlong
  have hJI : J ≤ I := by simpa only [I,J,Nat.cast_pow] using horder
  have hJ : 1 ≤ J := by
    have hh : 2 < J := by simpa only [J,Nat.cast_pow] using hJ₂
    linarith
  have hprod' : I*J = 32*(X*Y/(p : ℝ)^3) := by
    simpa only [I,J,Nat.cast_pow] using hprod
  have hcoord (z : Coordinate) (hz : physical B.R B.V z ∈ literalBox X Y) :
      CoordinateBound I J z := by
    simpa only [I,J,Nat.cast_pow] using
      B.coordinate_bound hc hX hY H σ hH hHsq hσ hσsq.le hσhi z hz
  have hqc : CoordinateBound I J q := by
    apply hcoord
    rw [hq]
    exact anchor_mem_literalBox hparameter.1 hparameter.2
  have ht' : IsUnit (-(physical B.R B.V q).2 : ZMod (p^3)) := by simpa [hq] using ht
  have hk' : IsUnit (1-a₁*a₂*(ht'.unit : ZMod (p^3))*
      ((physical B.R B.V q).1 : ZMod (p^3))) := by
    rw [ht'.unit_spec]
    simpa only [hq, Int.cast_neg, neg_neg, mul_neg, sub_neg_eq_add] using hk
  have hB : 1 ≤ I*J := one_le_mul_of_one_le_of_one_le (hJ.trans hJI) hJ
  have hJNonneg : 0 ≤ J := zero_le_one.trans hJ
  have hJProd : J^2 ≤ I*J := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hJI hJNonneg
  obtain ⟨hg₁,hg₂,hg₃,hg₆⟩ := rank_four_gaps p (I*J) J (by exact_mod_cast hp.pos) hB
    hJNonneg hJProd (hprod'.symm ▸ hgap)
  refine ⟨zero_dixon_of_rank_four_coordinates p hp a₁ a₂ ha₁ ha₂ q B.R B.V E
    hr ht' hk' I J hJI hJ hqc ?_ hword heunit hrank hg₁ hg₂ hg₃, hprod' ▸ hg₆⟩
  intro e he
  exact ⟨hcoord _ (hebox e he).1, hcoord _ (hebox e he).2⟩

/-- The full finite original maximum bad-degree average on the rank-four stratum. -/
theorem actual_long_bad_degree_average_rank_four (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ)
      (a₁ a₂ : ZMod (p^3)) (q : Coordinate → Coordinate)
      (RV : Coordinate → Coordinate × Coordinate)
      (s : Finset Coordinate) (E : Coordinate → Finset Endpoint),
      1 ≤ X → X ≤ Y → 2*Y < (p : ℝ)^3 → X*Y < 2*(p : ℝ)^4 →
      0 < H → H^2 = X*Y → (p : ℝ) ≤ H → IsUnit a₁ → IsUnit a₂ →
      (∀ wt ∈ s, wt ∈ literalBox X Y) →
      (∀ wt ∈ s, ∃ B : ReducedMiddleBasis (p^3) wt.2 wt.1 X Y,
        B.R = (RV wt).1 ∧ B.V = (RV wt).2) →
      (∀ wt ∈ s, physical (RV wt).1 (RV wt).2 (q wt) = -wt) →
      (∀ wt ∈ s, (p^3 : ℝ)^2 < (X*Y)*weightedSq X Y (RV wt).1) →
      (∀ wt ∈ s, IsUnit ((RV wt).1.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (wt.2 : ZMod (p^3)) ∧ IsUnit (wt.1 : ZMod (p^3))) →
      (∀ wt ∈ s, IsUnit (1+a₁*a₂*(wt.2 : ZMod (p^3))*(wt.1 : ZMod (p^3)))) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        WordSolution (p^3) a₁ a₂ (RV wt).1 (RV wt).2 (q wt) e) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        IsUnit ((physical (RV wt).1 (RV wt).2 e.1).1 : ZMod (p^3)) ∧
        IsUnit ((physical (RV wt).1 (RV wt).2 e.2).1 : ZMod (p^3))) →
      (∀ wt ∈ s, ∀ e ∈ E wt,
        physical (RV wt).1 (RV wt).2 e.1 ∈ literalBox X Y ∧
        physical (RV wt).1 (RV wt).2 e.2 ∈ literalBox X Y) →
      (∀ wt ∈ s, actualRecordRankFour p (q wt) (RV wt).1 (RV wt).2 (E wt)) →
      rankFourHeightConstant*(32*(X*Y/(p : ℝ)^3))^13 < (p : ℝ)^10 →
      (∑ wt ∈ s, (actualRecordBadDegree p (q wt) (RV wt).1 (RV wt).2 (E wt) : ℝ)) ≤
        C*(p : ℝ)^ε*(X*Y+(X*Y/p)*(1+Real.log (2*p)/Real.log 2)+
          (X*Y)^2/(p : ℝ)^4) := by
  obtain ⟨C,hC,havg⟩ := actual_long_bad_degree_average_zero_dixon ε hε
  refine ⟨C,hC,?_⟩
  intro p hp X Y H a₁ a₂ q RV s E hX hXY hYcut hAcut hH hHsq hHp ha₁ ha₂
    hsbox hred hanchor hlong hr hunit hk hword heunit hebox hrank hgap
  by_cases hs : s.Nonempty
  · have hlocal (wt : Coordinate) (hw : wt ∈ s) :
        actualRecordZeroDixon p (q wt) (RV wt).1 (RV wt).2 (E wt) ∧
          sixthHeightConstant*(32*(X*Y/(p : ℝ)^3))^6 < (p : ℝ)^5 := by
      obtain ⟨B,hBR,hBV⟩ := hred wt hw
      have hq : physical B.R B.V (q wt) = (-wt.1,-wt.2) := by
        rw [hBR,hBV]
        exact (hanchor wt hw).trans (Prod.ext (Prod.fst_neg wt) (Prod.snd_neg wt))
      have hlongB : ((p^3 : ℕ) : ℝ)^2 < H^2*weightedSq X Y B.R := by
        rw [hHsq,hBR]
        simpa only [Nat.cast_pow] using hlong wt hw
      have hh := long_rank_four_bridge p hp X Y H wt.2 wt.1 B a₁ a₂ ha₁ ha₂
        (q wt) (E wt) (by linarith) (by linarith) hH hHsq (hsbox wt hw) hq hlongB
        (by simpa only [hBR] using hr wt hw) (hunit wt hw).1 (hk wt hw)
        (by simpa only [hBR,hBV] using hword wt hw)
        (by simpa only [hBR,hBV] using heunit wt hw)
        (by simpa only [hBR,hBV] using hebox wt hw)
        (by simpa only [hBR,hBV] using hrank wt hw) hgap
      simpa only [hBR,hBV] using hh
    obtain ⟨wt,hwt⟩ := hs
    exact havg p hp X Y H a₁ a₂ q RV s E hX hXY hYcut hAcut hH hHsq hHp ha₁ ha₂
      hsbox hred hanchor hlong hr hunit hk hword heunit hebox
      (fun u hu => (hlocal u hu).1) (hlocal wt hwt).2
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hl : 0 ≤ Real.log (2*p) := Real.log_nonneg (by linarith)
    have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hX0 : 0 ≤ X := by linarith
    have hY0 : 0 ≤ Y := hX0.trans hXY
    positivity

end
end D5.S3.Arith.CharacterSums.Original
