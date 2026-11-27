/- GID: D5/S3/Combinatorics/MatrixOrbits/SymmetricRepresentativeSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatrixOrbits/SymmetricRepresentativeSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The series for symmetric-representative matrix orbits. -/

import D5.S3.Combinatorics.MatrixOrbits.TwistedOrbits
import D5.S3.Combinatorics.MatrixOrbits.IdentityCycle

/-! # The series for symmetric-representative matrix orbits.

The other four twisted series and the identity twist combine by their
cycle multiplicities. Clearing unit denominators gives the rational
series over the rational numbers, including its constant term.
-/

open scoped BigOperators

namespace A333886




local notation "x" => (PowerSeries.X : PS)

private abbrev G3 := Graded.nats 3
private abbrev G4 := Graded.nats 4

private theorem rows2 (n : ℕ) (v : Fin 4 → ℕ) :
    pattern2.rows n v ↔ 2*v 0+v 1+v 2=n ∧ v 0=v 3 := by
  rw [four_rows]
  simp only [Fin.sum_univ_four]
  change (v 0+v 0+v 1+v 2=n ∧ v 0+v 0+v 2+v 1=n ∧
    v 2+v 1+v 3+v 3=n ∧ v 1+v 2+v 3+v 3=n) ↔ _
  omega

private theorem rows3 (n : ℕ) (v : Fin 4 → ℕ) :
    pattern3.rows n v ↔ 2*v 0+v 1+v 2=n ∧ 3*v 2+v 3=n := by
  rw [four_rows]
  simp only [Fin.sum_univ_four]
  change (v 0+v 0+v 1+v 2=n ∧ v 1+v 0+v 0+v 2=n ∧
    v 0+v 1+v 0+v 2=n ∧ v 2+v 2+v 2+v 3=n) ↔ _
  omega

private theorem rows4 (n : ℕ) (v : Fin 2 → ℕ) :
    pattern4.rows n v ↔ 2*v 0+2*v 1=n := by
  rw [four_rows]
  simp only [Fin.sum_univ_four]
  change (v 0+v 0+v 1+v 1=n ∧ v 1+v 0+v 0+v 1=n ∧
    v 1+v 1+v 0+v 0=n ∧ v 0+v 1+v 1+v 0=n) ↔ _
  omega

private abbrev data2 : Graded := G2.prod (G1.prod G1)
private abbrev data3 : Graded := (G3.prod (G3.prod G1)).sum ((G3.prod (G2.prod G1)).shift 2)
private abbrev data4 : Graded := G2.prod G2

private def fibers2 (n : ℕ) : TwistMat rep2 n ≃ data2.Fiber n :=
  (pattern2.equiv n).trans <| (Equiv.subtypeEquivRight (rows2 n)).trans <|
    { toFun := fun ⟨v,hv⟩ => ⟨(v 0,v 1,v 2), by change 2*v 0+(1*v 1+1*v 2)=n; omega⟩
      invFun := fun ⟨⟨a,b,c⟩,h⟩ => ⟨![a,b,c,a], by
        change ℕ at a b c
        change 2*a+(1*b+1*c)=n at h
        change 2*a+b+c=n ∧ a=a
        exact ⟨by omega, rfl⟩⟩
      left_inv := by
        rintro ⟨v,hv⟩
        apply Subtype.ext
        funext i
        fin_cases i
        · rfl
        · rfl
        · rfl
        · exact hv.2
      right_inv := by rintro ⟨⟨a,b,c⟩,h⟩; rfl }

private def fibers4 (n : ℕ) : TwistMat rep4 n ≃ data4.Fiber n :=
  (pattern4.equiv n).trans <| (Equiv.subtypeEquivRight (rows4 n)).trans <|
    { toFun := fun ⟨v,hv⟩ => ⟨(v 0,v 1), hv⟩
      invFun := fun ⟨⟨a,b⟩,h⟩ => ⟨![a,b],h⟩
      left_inv := by
        rintro ⟨v,hv⟩
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      right_inv := by rintro ⟨⟨a,b⟩,h⟩; rfl }

private abbrev params3 (n : ℕ) := {v : Fin 4 → ℕ // 2*v 0+v 1+v 2=n ∧ 3*v 2+v 3=n}

private def encode3 (n : ℕ) (v : params3 n) : data3.Fiber n := by
  let a := v.val 0
  let b := v.val 1
  let c := v.val 2
  have ha : 2*a+b+c=n := v.property.1
  have hc : 3*c+v.val 3=n := v.property.2
  if h : a ≤ c then
    exact ⟨Sum.inl (a,c-a,b-2*(c-a)), by
      change 3*a+(3*(c-a)+1*(b-2*(c-a)))=n
      omega⟩
  else
    exact ⟨Sum.inr (c,a-c-1,b), by
      change 2+(3*c+(2*(a-c-1)+1*b))=n
      omega⟩

private def decode3 (n : ℕ) (w : data3.Fiber n) : params3 n := by
  rcases w with ⟨⟨a,r,b⟩ | ⟨c,r,b⟩, h⟩
  · change ℕ at a r b
    have hw : 3*a+(3*r+1*b)=n := h
    exact ⟨![a,2*r+b,a+r,b], by
      change 2*a+(2*r+b)+(a+r)=n ∧ 3*(a+r)+b=n
      constructor <;> omega⟩
  · change ℕ at c r b
    have hw : 2+(3*c+(2*r+1*b))=n := h
    exact ⟨![c+r+1,b,c,2+2*r+b], by
      change 2*(c+r+1)+b+c=n ∧ 3*c+(2+2*r+b)=n
      constructor <;> omega⟩

private def fibers3 (n : ℕ) : TwistMat rep3 n ≃ data3.Fiber n :=
  (pattern3.equiv n).trans <| (Equiv.subtypeEquivRight (rows3 n)).trans <|
  { toFun := encode3 n
    invFun := decode3 n
    left_inv := by
      rintro ⟨v,hv⟩
      have h0 := hv.1
      have h1 := hv.2
      apply Subtype.ext
      by_cases h : v 0 ≤ v 2
      · change (decode3 n (encode3 n ⟨v,hv⟩)).val = v
        unfold encode3
        rw [dite_eq_left h]
        dsimp only [decode3]
        funext i
        fin_cases i
        · rfl
        · change 2*(v 2-v 0)+(v 1-2*(v 2-v 0))=v 1; omega
        · change v 0+(v 2-v 0)=v 2; omega
        · change v 1-2*(v 2-v 0)=v 3; omega
      · change (decode3 n (encode3 n ⟨v,hv⟩)).val = v
        unfold encode3
        rw [dite_eq_right h]
        dsimp only [decode3]
        funext i
        fin_cases i
        · change v 2+(v 0-v 2-1)+1=v 0; omega
        · rfl
        · rfl
        · change 2+2*(v 0-v 2-1)+v 1=v 3; omega
    right_inv := by
      rintro ⟨⟨a,r,b⟩ | ⟨c,r,b⟩, h⟩
      · change ℕ at a r b
        have ha : a ≤ a+r := by omega
        apply Subtype.ext
        change (encode3 n (decode3 n ⟨Sum.inl (a,r,b),h⟩)).val = _
        unfold encode3
        simp [decode3, ha, id_eq]
      · change ℕ at c r b
        have ha : ¬c+r+1 ≤ c := by omega
        apply Subtype.ext
        change (encode3 n (decode3 n ⟨Sum.inr (c,r,b),h⟩)).val = _
        unfold encode3
        simp [decode3, ha, id_eq]
        omega }

private theorem twist2_series : twistSeries rep2 = geom 2 * geom 1^2 := by
  rw [twist_series_from_fibers rep2 data2 fibers2]
  simp [data2, pow_two]

private theorem twist3_series :
    twistSeries rep3 = geom 3^2 * geom 1 + x^2 * geom 3 * geom 2 * geom 1 := by
  rw [twist_series_from_fibers rep3 data3 fibers3]
  simp [data3]
  ring

private theorem twist4_series : twistSeries rep4 = geom 2^2 := by
  rw [twist_series_from_fibers rep4 data4 fibers4]
  simp [data4, pow_two]

private abbrev Graded.weightedFinite (α : Type) [Finite α] (weight : α → ℕ) : Graded where
  Space := α
  weight := weight
  finite_fiber _ := inferInstance

private lemma Graded.series_weightedFinite (α : Type) [Fintype α] (w : α → ℕ) :
    (Graded.weightedFinite α w).series = ∑ a : α, x^(w a) := by
  classical
  ext n
  have := Fintype.ofFinite {a : α // w a = n}
  rw [Graded.coeff_series, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [PowerSeries.coeff_X_pow, eq_comm]

private def bit (b : Bool) : ℕ := if b then 1 else 0

private lemma bit_le (b : Bool) : bit b ≤ 1 := by cases b <;> decide

private abbrev evenLabel : Graded := Graded.weightedFinite Bool (fun b => 2*bit b)

private abbrev unequalLabel : Graded := Graded.weightedFinite (Triple Bool)
  (fun a => if a.1 then 3 else 4+2*bit a.2.2)

private abbrev halves := G2.prod (G2.prod G2)
private abbrev equalModel := evenLabel.prod halves
private abbrev unequalModel := unequalLabel.prod (G4.prod halves)
private abbrev transModel := equalModel.sum unequalModel

@[ext] private structure TransData where
  m : ℕ
  d : Dir
  e : ℕ
  s : ℕ
  parity : (e+s)%2 = size d % 2

private def TransData.grade (a : TransData) : ℕ := 2*a.m+2*size a.d+a.e+a.s

private def toTransModel (a : TransData) : transModel.Space :=
  let b : Bool := decide (a.e % 2 = 1)
  if size a.d = 0 then
    Sum.inl (b,a.m,a.e/2,a.s/2)
  else
    Sum.inr ((decide (size a.d % 2 = 1), reversed a.d, b), (size a.d-1)/2,
      a.m,a.e/2,a.s/2)

private def fromTransModel : transModel.Space → TransData
  | .inl (b,m,r,t) =>
      ⟨m,.inl 0,2*r+bit b,2*t+bit b, by
        change ℕ at m r t
        have := bit_le b
        change (2*r+bit b+(2*t+bit b))%2=0
        omega⟩
  | .inr ((odd,rev,b),k,m,r,t) =>
      ⟨m, positiveDir rev (if odd then 2*k else 2*k+1),
        2*r+bit b, 2*t+bit (b ^^ odd), by
          change ℕ at k m r t
          rw [positiveDir_size]
          cases b <;> cases odd <;> simp [bit] <;> omega⟩

private lemma size_zero_dir (d : Dir) (h : size d = 0) : d = Sum.inl 0 := by
  cases d <;> simp_all [size, first, second]

private lemma bit_decide_one (n : ℕ) : bit (decide (n%2=1))=n%2 := by
  by_cases h : n%2=1
  · simp [bit,h]
  · simp [bit,h]
    omega

private lemma bit_xor_mod (b o : Bool) (e s d : ℕ)
    (hb : bit b=e%2) (ho : bit o=d%2) (h : (e+s)%2=d%2) :
    bit (b ^^ o)=s%2 := by
  rw [Nat.add_mod e s 2, ← hb, ← ho] at h
  cases b <;> cases o <;> simp [bit] at h ⊢ <;> omega

private lemma rebuild_positive (odd : Bool) (d : ℕ)
    (ho : bit odd=d%2) (hd : d≠0) :
    (if odd then 2*((d-1)/2) else 2*((d-1)/2)+1) = d-1 := by
  cases odd <;> simp [bit] at ho ⊢ <;> omega

private lemma trans_model_left_inverse (a : TransData) : fromTransModel (toTransModel a) = a := by
  rcases a with ⟨m,d,e,s,h⟩
  let b : Bool := decide (e%2=1)
  let odd : Bool := decide (size d%2=1)
  have hb : bit b = e%2 := bit_decide_one e
  have ho : bit odd = size d % 2 := bit_decide_one (size d)
  have hx : bit (b ^^ odd) = s%2 := bit_xor_mod b odd e s (size d) hb ho h
  by_cases hz : size d = 0
  · have hs : bit b = s%2 := by omega
    have hd := size_zero_dir d hz
    have he : 2*(e/2)+bit b=e := by omega
    have ht : 2*(s/2)+bit b=s := by omega
    unfold toTransModel
    simp only [ite_eq_left hz]
    change (⟨m, Sum.inl 0, 2*(e/2)+bit b, 2*(s/2)+bit b, _⟩ : TransData) = _
    simp [he,ht,hd]
  · have he : 2*(e/2)+bit b=e := by omega
    have ht : 2*(s/2)+bit (b ^^ odd)=s := by omega
    have hk := rebuild_positive odd (size d) ho hz
    unfold toTransModel
    simp only [ite_eq_right hz]
    change (⟨m, positiveDir (reversed d) (if odd then 2*((size d-1)/2) else 2*((size d-1)/2)+1),
      2*(e/2)+bit b, 2*(s/2)+bit (b ^^ odd), _⟩ : TransData) = _
    simp [he,ht,hk,positiveDir_rebuild d hz]

private lemma trans_model_right_inverse (v : transModel.Space) : toTransModel (fromTransModel v) = v := by
  rcases v with ⟨b,m,r,t⟩ | ⟨⟨odd,rev,b⟩,k,m,r,t⟩
  · change ℕ at m r t
    cases b
    · simp [toTransModel, fromTransModel, bit, size, first, second]
    · simp [toTransModel, fromTransModel, bit, size, first, second]
      omega
  · change ℕ at k m r t
    cases odd <;> cases rev <;> cases b <;>
      simp [toTransModel, fromTransModel, bit, positiveDir, size, first, second, reversed] <;> omega

private def transDataEquiv : TransData ≃ transModel.Space where
  toFun := toTransModel
  invFun := fromTransModel
  left_inv := trans_model_left_inverse
  right_inv := trans_model_right_inverse

private abbrev transDataGraded := transModel.ofEquiv transDataEquiv

private lemma trans_model_grade (v : transModel.Space) :
    (fromTransModel v).grade = transModel.weight v := by
  rcases v with ⟨b,m,r,t⟩ | ⟨⟨odd,rev,b⟩,k,m,r,t⟩
  · change ℕ at m r t
    cases b <;> simp [TransData.grade, fromTransModel, bit, size, first, second] <;> omega
  · change ℕ at k m r t
    cases odd <;> cases b <;> simp [TransData.grade, fromTransModel, bit] <;> omega

private lemma trans_data_grade (a : TransData) :
    transDataGraded.weight a = a.grade := by
  have h := trans_model_grade (toTransModel a)
  rw [trans_model_left_inverse] at h
  exact h.symm

private theorem rows1 (n : ℕ) (v : Fin 6 → ℕ) : pattern1.rows n v ↔
    2*v 0+v 1+v 2=n ∧ 2*v 1+v 3+v 4=n ∧ 2*v 2+v 4+v 5=n := by
  rw [four_rows]
  simp only [Fin.sum_univ_four]
  change (v 0+v 0+v 1+v 2=n ∧ v 0+v 0+v 1+v 2=n ∧
    v 1+v 1+v 3+v 4=n ∧ v 2+v 2+v 4+v 5=n) ↔ _
  omega

private abbrev params1 (n : ℕ) := {v : Fin 6 → ℕ //
    2*v 0+v 1+v 2=n ∧ 2*v 1+v 3+v 4=n ∧ 2*v 2+v 4+v 5=n}

private lemma direction_has_zero (d : Dir) : first d = 0 ∨ second d = 0 := by
  cases d <;> simp [first, second]

private def transRecordFiber (n : ℕ) : params1 n ≃ {a : TransData // a.grade = n} where
  toFun v := by
    let q := balancePair (v.val 1,v.val 2)
    let m := q.1
    let d := q.2
    let e := v.val 4
    have hq := balancePair.symm_apply_apply (v.val 1,v.val 2)
    change (m+first d,m+second d) = (v.val 1,v.val 2) at hq
    rcases Prod.mk.inj hq with ⟨hB,hC⟩
    have ⟨h0,h1,h2⟩ := v.property
    change 2*v.val 1+v.val 3+e=n at h1
    change 2*v.val 2+e+v.val 5=n at h2
    have hbd : 2*(m+size d)+e ≤ n := by
      unfold size
      rcases direction_has_zero d with hz|hz <;> omega
    let s := n-(2*(m+size d)+e)
    have hs : 2*(m+size d)+e+s=n := by dsimp [s]; omega
    have hp : (e+s)%2=size d%2 := by unfold size at *; omega
    exact ⟨⟨m,d,e,s,hp⟩, by change 2*m+2*size d+e+s=n; omega⟩
  invFun a := by
    let m := a.val.m
    let d := a.val.d
    let e := a.val.e
    let s := a.val.s
    let b := m+first d
    let c := m+second d
    have hp : (e+s)%2 = size d%2 := a.val.parity
    have hn : 2*m+2*size d+e+s=n := a.property
    refine ⟨![(n-b-c)/2,b,c,n-(2*b+e),e,n-(2*c+e)], ?_⟩
    change 2*((n-b-c)/2)+b+c=n ∧ 2*b+(n-(2*b+e))+e=n ∧ 2*c+e+(n-(2*c+e))=n
    dsimp [b,c]
    unfold size at *
    omega
  left_inv := by
    intro v
    let q := balancePair (v.val 1,v.val 2)
    let m := q.1
    let d := q.2
    let e := v.val 4
    have hq := balancePair.symm_apply_apply (v.val 1,v.val 2)
    change (m+first d,m+second d) = (v.val 1,v.val 2) at hq
    rcases Prod.mk.inj hq with ⟨hB,hC⟩
    have ⟨h0,h1,h2⟩ := v.property
    apply Subtype.ext
    funext i
    fin_cases i
    · change (n-(m+first d)-(m+second d))/2=v.val 0; omega
    · exact hB
    · exact hC
    · change n-(2*(m+first d)+e)=v.val 3
      change 2*v.val 1+v.val 3+e=n at h1
      omega
    · rfl
    · change n-(2*(m+second d)+e)=v.val 5
      change 2*v.val 2+e+v.val 5=n at h2
      omega
  right_inv := by
    rintro ⟨⟨m,d,e,s,hp⟩,hn⟩
    change 2*m+2*size d+e+s=n at hn
    let q := balancePair (m+first d,m+second d)
    have hq : q = (m,d) := balancePair.apply_symm_apply (m,d)
    have hm : q.1=m := congrArg Prod.fst hq
    have hd : q.2=d := congrArg Prod.snd hq
    apply Subtype.ext
    apply TransData.ext
    · exact hm
    · exact hd
    · rfl
    · change n-(2*(q.1+size q.2)+e)=s
      rw [hm,hd]
      omega

private def fibers1 (n : ℕ) : TwistMat rep1 n ≃ transDataGraded.Fiber n :=
  (pattern1.equiv n).trans <| (Equiv.subtypeEquivRight (rows1 n)).trans <|
    (transRecordFiber n).trans <| Equiv.subtypeEquivRight
      (fun a => by rw [trans_data_grade])

private lemma evenLabel_series : evenLabel.series = 1+x^2 := by
  rw [Graded.series_weightedFinite, Fintype.sum_bool]
  simp [bit, add_comm]

private lemma unequalLabel_series : unequalLabel.series = 2*x^4+2*x^6+4*x^3 := by
  rw [Graded.series_weightedFinite]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, bit]
  norm_num
  ring

private theorem twist1_series : twistSeries rep1 =
    ((1+x^4)*(1+x^2)+4*x^3)*geom 4*geom 2^3 := by
  rw [twist_series_from_fibers rep1 transDataGraded fibers1]
  simp only [transDataGraded, Graded.series_ofEquiv, transModel, equalModel, unequalModel, halves,
    Graded.series_sum, Graded.series_prod, Graded.series_nats, evenLabel_series, unequalLabel_series]
  have h := geom_mul 4 (by decide)
  linear_combination -((1+x^2)*geom 2^3) * h

local notation:max "D[" k "]" => (1-x^k)

private lemma clear0 :
    D[1]^7 * D[2] * twistSeries rep0 =
      D[2]*((1+x)^3-4*x^3)+4*x^2*(1-x^3) := by
  rw [twist0_series]
  calc
    _ = (D[1]*geom 1)^7 *
        (D[2]*((1+x)^3-4*x^3)+4*x^2*(1-x^3)*(D[2]*geom 2)) := by ring
    _ = _ := by rw [geom_mul 1 (by decide), geom_mul 2 (by decide)]; ring

private lemma clear1 :
    D[4] * D[2]^3 * twistSeries rep1 = (1+x^4)*(1+x^2)+4*x^3 := by
  rw [twist1_series]
  calc
    _ = (D[4]*geom 4)*(D[2]*geom 2)^3*((1+x^4)*(1+x^2)+4*x^3) := by ring
    _ = _ := by rw [geom_mul 4 (by decide), geom_mul 2 (by decide)]; ring

private lemma clear2 : D[2] * D[1]^2 * twistSeries rep2 = 1 := by
  rw [twist2_series]
  calc
    _ = (D[2]*geom 2)*(D[1]*geom 1)^2 := by ring
    _ = _ := by rw [geom_mul 2 (by decide), geom_mul 1 (by decide)]; ring

private lemma clear3 : D[3]^2 * D[2] * D[1] * twistSeries rep3 = 1-x^5 := by
  rw [twist3_series]
  calc
    _ = (D[3]*geom 3)^2*(D[1]*geom 1)*D[2] +
        x^2*(D[3]*geom 3)*(D[2]*geom 2)*(D[1]*geom 1)*D[3] := by ring
    _ = _ := by rw [geom_mul 3 (by decide), geom_mul 2 (by decide), geom_mul 1 (by decide)]; ring

private lemma clear4 : D[2]^2 * twistSeries rep4 = 1 := by
  rw [twist4_series, ← mul_pow, geom_mul 2 (by decide)]
  ring

noncomputable def publishedNumerator : PS :=
  1-2*x+4*x^2-x^3+9*x^4+x^5+12*x^6+6*x^8-x^9+x^10

noncomputable def publishedDenominator : PS :=
  (1-x)^3*(1-x^2)*(1-x^3)^2*(1-x^4)

noncomputable def publishedSeries : PS :=
  publishedNumerator * PowerSeries.invOfUnit publishedDenominator 1

private lemma publishedDenominator_const : PowerSeries.constantCoeff publishedDenominator = 1 := by
  simp [publishedDenominator]

lemma clearPublished : publishedDenominator * publishedSeries = publishedNumerator := by
  have h := PowerSeries.mul_invOfUnit publishedDenominator 1 publishedDenominator_const
  unfold publishedSeries
  calc
    _ = publishedNumerator * (publishedDenominator * publishedDenominator.invOfUnit 1) := by ring
    _ = _ := by rw [h, mul_one]

private lemma cycle_sum_explicit :
    twistSeries rep0 + 6*twistSeries rep1 + 3*twistSeries rep2 +
      8*twistSeries rep3 + 6*twistSeries rep4 = 24*countSeries a333886 := by
  have h := cycle_series
  rw [Fin.sum_univ_five] at h
  simpa [cycleMultiplicity, rep] using h

private lemma commonDenominator :
    D[1]^7 * D[2]^3 * D[3]^2 * D[4] * (24*countSeries a333886) =
      D[1]^4 * D[2]^2 * (24*publishedNumerator) := by
  unfold publishedNumerator
  linear_combination
    -(D[1]^7*D[2]^3*D[3]^2*D[4])*cycle_sum_explicit +
    (D[2]^2*D[3]^2*D[4])*clear0 +
    (6*D[1]^7*D[3]^2)*clear1 +
    (3*D[1]^5*D[2]^2*D[3]^2*D[4])*clear2 +
    (8*D[1]^6*D[2]^2*D[4])*clear3 +
    (6*D[1]^7*D[2]*D[3]^2*D[4])*clear4

private theorem published_identity : countSeries a333886 = publishedSeries := by
  let factor : PS := D[1]^4 * D[2]^2
  have hfactor : factor * (24 * publishedDenominator * countSeries a333886) =
      factor * (24 * publishedNumerator) := by
    dsimp [factor]
    unfold publishedDenominator
    linear_combination commonDenominator
  have hfactor_unit : IsUnit factor := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [factor]
  have hfinite : 24*publishedDenominator*countSeries a333886 =
      24*publishedDenominator*publishedSeries := by
    rw [mul_assoc (24 : PS) publishedDenominator publishedSeries, clearPublished]
    exact hfactor_unit.mul_left_cancel hfactor
  have hd : IsUnit publishedDenominator := by
    rw [PowerSeries.isUnit_iff_constantCoeff, publishedDenominator_const]
    exact isUnit_one
  have h24 : IsUnit (24 : PS) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    change IsUnit (PowerSeries.constantCoeff ((24 : ℕ) : PS))
    rw [map_natCast]
    norm_num [isUnit_iff_ne_zero]
  exact (h24.mul hd).mul_left_cancel hfinite

theorem source_identity_literal (n : ℕ) :
    (Nat.card {ω : Orbit n // ∃ B : Margin n,
      Quotient.mk _ B = ω ∧ ∀ i j : Fin 4, B.val i j = B.val j i} : ℚ) =
      PowerSeries.coeff n publishedSeries := by
  change (Nat.card (sourceClasses n) : ℚ) = PowerSeries.coeff n publishedSeries
  rw [← published_identity, coeff_countSeries, a333886, Nat.card_congr (sourceClassesEquiv n)]

end A333886
