/- GID: D5/S3/Combinatorics/MatrixOrbits/IdentityCycle
   generality: G
   mirror-B: none(waiver:covered-by-symmetric-representative-series-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The identity twist and its graded count. -/

import D5.S3.Combinatorics.MatrixOrbits.TwistedOrbits
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # The identity twist and its graded count.

Opposite edges of the complete graph on four vertices supply three
common weights. The residual maximum degree has a correction on four
triangular orientations. Graded fiber equivalences give the series.
-/

open scoped BigOperators

namespace A333886

open PowerSeries

local notation "x" => (PowerSeries.X : PowerSeries ℚ)

abbrev PS := PowerSeries ℚ

structure Graded where
  Space : Type
  weight : Space → ℕ
  finite_fiber : ∀ n, Finite {a : Space // weight a = n}

abbrev Graded.Fiber (A : Graded) (n : ℕ) := {a : A.Space // A.weight a = n}

instance (A : Graded) (n : ℕ) : Finite (A.Fiber n) := A.finite_fiber n

noncomputable def Graded.series (A : Graded) : PS :=
  PowerSeries.mk fun n => (Nat.card (A.Fiber n) : ℚ)

@[simp] lemma Graded.coeff_series (A : Graded) (n : ℕ) :
    coeff n A.series = (Nat.card (A.Fiber n) : ℚ) := coeff_mk _ _

private theorem Graded.series_congr {A B : Graded} (e : A.Space ≃ B.Space)
    (he : ∀ a, B.weight (e a) = A.weight a) : A.series = B.series := by
  ext n
  simp only [coeff_series]
  exact congrArg (Nat.cast : ℕ → ℚ) <|
    Nat.card_congr (e.subtypeEquiv fun a => by rw [he])

private def splitFiber {α β : Type} (w : α → ℕ) (v : β → ℕ) (n : ℕ) :
    {p : α × β // w p.1 + v p.2 = n} ≃
      Σ k : {k // k ∈ Finset.antidiagonal n},
        {a : α // w a = k.val.1} × {b : β // v b = k.val.2} where
  toFun p := ⟨⟨(w p.val.1, v p.val.2), Finset.mem_antidiagonal.mpr p.property⟩,
    ⟨⟨p.val.1,rfl⟩,⟨p.val.2,rfl⟩⟩⟩
  invFun p := ⟨(p.2.1.val,p.2.2.val), by rw [p.2.1.property,p.2.2.property]
                                         exact Finset.mem_antidiagonal.mp p.1.property⟩
  left_inv p := rfl
  right_inv := by
    rintro ⟨⟨⟨i,j⟩,h⟩,⟨⟨a,ha⟩,⟨b,hb⟩⟩⟩
    dsimp at ha hb
    subst i
    subst j
    rfl

abbrev Graded.prod (A B : Graded) : Graded where
  Space := A.Space × B.Space
  weight p := A.weight p.1 + B.weight p.2
  finite_fiber n := Finite.of_equiv _ (splitFiber A.weight B.weight n).symm

@[simp] theorem Graded.series_prod (A B : Graded) :
    (A.prod B).series = A.series * B.series := by
  classical
  ext n
  let e : (A.prod B).Fiber n ≃ _ := splitFiber A.weight B.weight n
  rw [coeff_series, coeff_mul, Nat.card_congr e, Nat.card_sigma, Nat.cast_sum, Finset.univ_eq_attach]
  simp only [Nat.card_prod, Nat.cast_mul, coeff_series]
  exact Finset.sum_attach _ (fun (k : ℕ × ℕ) => (Nat.card (A.Fiber k.1) : ℚ) * (Nat.card (B.Fiber k.2) : ℚ))

private def sumFiber {α β : Type} (w : α → ℕ) (v : β → ℕ) (n : ℕ) :
    {s : α ⊕ β // Sum.elim w v s = n} ≃
      {a : α // w a = n} ⊕ {b : β // v b = n} :=
  Equiv.subtypeSum

abbrev Graded.sum (A B : Graded) : Graded where
  Space := A.Space ⊕ B.Space
  weight := Sum.elim A.weight B.weight
  finite_fiber n := Finite.of_equiv _ (sumFiber A.weight B.weight n).symm

@[simp] theorem Graded.series_sum (A B : Graded) :
    (A.sum B).series = A.series + B.series := by
  ext n
  let e : (A.sum B).Fiber n ≃ A.Fiber n ⊕ B.Fiber n := sumFiber A.weight B.weight n
  rw [coeff_series, Nat.card_congr e, Nat.card_sum, Nat.cast_add]
  simp

abbrev Graded.shift (A : Graded) (d : ℕ) : Graded where
  Space := A.Space
  weight a := d + A.weight a
  finite_fiber n := by
    by_cases hd : d ≤ n
    · exact Finite.of_equiv (A.Fiber (n-d))
        (Equiv.refl _ |>.subtypeEquiv fun a => by dsimp; omega)
    · have : IsEmpty {a : A.Space // d + A.weight a = n} :=
        ⟨fun a => hd (by have := a.property; omega)⟩
      infer_instance

@[simp] theorem Graded.series_shift (A : Graded) (d : ℕ) :
    (A.shift d).series = x^d * A.series := by
  ext n
  rw [coeff_series, coeff_X_pow_mul']
  split
  · rename_i hd
    rw [Nat.card_congr (β := A.Fiber (n-d)) (Equiv.refl _ |>.subtypeEquiv fun a => by
      change d + A.weight a = n ↔ A.weight a = n-d
      omega), coeff_series]
  · rename_i hd
    let : IsEmpty ((A.shift d).Fiber n) := ⟨fun a => hd (by
      have h : d + A.weight a.val = n := a.property
      omega)⟩
    simp

abbrev Graded.nats (d : ℕ) (hd : 0 < d := by decide) : Graded where
  Space := ℕ
  weight a := d * a
  finite_fiber n := Finite.of_injective (β := Fin (n+1))
    (fun a => ⟨a.val, Nat.lt_succ_of_le <| calc
      a.val = 1 * a.val := (one_mul _).symm
      _ ≤ d * a.val := Nat.mul_le_mul_right _ hd
      _ = n := a.property⟩)
    (fun _ _ h => Subtype.ext (congrArg Fin.val h))

noncomputable def geom (d : ℕ) : PS := (1 - x^d).invOfUnit 1

theorem geom_mul (d : ℕ) (hd : 0 < d) : (1 - x^d) * geom d = 1 := by
  apply PowerSeries.mul_invOfUnit
  simp [Nat.ne_of_gt hd]

private lemma card_nats_mul (d n : ℕ) (hd : 0 < d) :
    Nat.card ((Graded.nats d hd).Fiber n) = if d ∣ n then 1 else 0 := by
  split
  · rename_i h
    obtain ⟨v, hv⟩ := h
    have e : (Graded.nats d hd).Fiber n ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨v, hv.symm⟩
        left_inv := fun a => Subtype.ext (Nat.eq_of_mul_eq_mul_left hd (a.property.trans hv)).symm
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]; simp
  · rename_i h
    have : IsEmpty ((Graded.nats d hd).Fiber n) := ⟨fun a => h ⟨a.val, a.property.symm⟩⟩
    simp

@[simp] theorem Graded.series_nats (d : ℕ) (hd : 0 < d) :
    (Graded.nats d hd).series = geom d := by
  have hg := geom_mul d hd
  have h : (1-x^d)*(Graded.nats d hd).series = 1 := by
    ext n
    simp only [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_series, card_nats_mul, coeff_one]
    by_cases hn : d ≤ n
    · have he : d ∣ n - d ↔ d ∣ n := by
        constructor
        · intro hh
          rw [← Nat.sub_add_cancel hn]
          exact dvd_add hh (dvd_refl _)
        · intro hh
          exact Nat.dvd_sub hh (dvd_refl _)
      have hne : n ≠ 0 := by omega
      simp [hn, he, hne]
    · have hnd : ¬ d ∣ n ↔ n ≠ 0 := by
        constructor
        · intro hh h0
          exact hh (h0 ▸ dvd_zero d)
        · intro hne hh
          exact hn (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hh)
      by_cases hz : n = 0 <;> simp [hn, hz, Nat.ne_of_gt hd, (hnd.mpr ·)]
  calc
    (Graded.nats d hd).series = (Graded.nats d hd).series * 1 := (mul_one _).symm
    _ = (1-x^d)*(Graded.nats d hd).series * geom d := by
      calc
        _ = (Graded.nats d hd).series * ((1-x^d) * geom d) :=
          congrArg ((Graded.nats d hd).series * ·) hg.symm
        _ = _ := by ring
    _ = geom d := by rw [h, one_mul]

abbrev Graded.ofEquiv {α : Type} (B : Graded) (e : α ≃ B.Space) : Graded where
  Space := α
  weight a := B.weight (e a)
  finite_fiber n := Finite.of_equiv (B.Fiber n) (e.subtypeEquiv (fun _ => Iff.rfl)).symm

@[simp] theorem Graded.series_ofEquiv {α : Type} (B : Graded) (e : α ≃ B.Space) :
    (B.ofEquiv e).series = B.series := Graded.series_congr e fun _ => rfl

private abbrev Graded.filter (A : Graded) (p : A.Space → Prop) : Graded where
  Space := Subtype p
  weight a := A.weight a.val
  finite_fiber n := Finite.of_injective (β := A.Fiber n)
    (fun a => ⟨a.val.val, a.property⟩)
    (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun (v : A.Fiber n) => v.val) h)))

private lemma Graded.series_partition (A : Graded) (p : A.Space → Prop) :
    A.series = (A.filter p).series + (A.filter (fun a => ¬p a)).series := by
  classical
  rw [← series_sum]
  symm
  exact series_congr (Equiv.sumCompl p) (fun a => by cases a <;> rfl)

private abbrev Graded.finite (α : Type) [Finite α] : Graded where
  Space := α
  weight _ := 0
  finite_fiber _ := inferInstance

@[simp] private theorem Graded.series_finite (α : Type) [Finite α] :
    (Graded.finite α).series = (Nat.card α : PS) := by
  ext n
  rw [coeff_series, ← map_natCast PowerSeries.C, coeff_C]
  by_cases hn : n = 0
  · subst n
    have e : (Graded.finite α).Fiber 0 ≃ α :=
      { toFun := Subtype.val
        invFun := fun a => ⟨a, rfl⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]; simp
  · let : IsEmpty ((Graded.finite α).Fiber n) := ⟨fun a => hn a.property.symm⟩
    simp [hn]

noncomputable def countSeries (a : ℕ → ℕ) : PS := PowerSeries.mk fun n => (a n : ℚ)

@[simp] lemma coeff_countSeries (a : ℕ → ℕ) (n : ℕ) :
    PowerSeries.coeff n (countSeries a) = (a n : ℚ) := PowerSeries.coeff_mk _ _

noncomputable def twistSeries (p : P) : PS := countSeries fun n => Nat.card (TwistMat p n)

theorem cycle_series :
    (∑ k : Fin 5, (cycleMultiplicity k : PS) * twistSeries (rep k)) = 24 * countSeries a333886 := by
  ext n
  rw [← Nat.cast_ofNat (n := 24) (R := PS), ← map_natCast PowerSeries.C]
  simp only [map_sum, ← map_natCast PowerSeries.C, PowerSeries.coeff_C_mul, twistSeries,
    coeff_countSeries]
  exact_mod_cast cycle_count n

lemma twist_series_from_fibers (p : P) (S : Graded) (e : ∀ n, TwistMat p n ≃ S.Fiber n) :
    twistSeries p = S.series := by
  ext n
  simp [twistSeries, Nat.card_congr (e n)]



abbrev G1 := Graded.nats 1
abbrev G2 := Graded.nats 2

abbrev Dir := ℕ ⊕ ℕ
abbrev Triple (α : Type) := α × α × α

def first : Dir → ℕ
  | .inl a => a
  | .inr _ => 0

def second : Dir → ℕ
  | .inl _ => 0
  | .inr b => b+1

def size (d : Dir) : ℕ := first d + second d

def reversed : Dir → Bool
  | .inl _ => false
  | .inr _ => true

def balancePair : (ℕ × ℕ) ≃ (ℕ × Dir) where
  toFun p := if p.2 ≤ p.1 then (p.2, .inl (p.1-p.2)) else (p.1, .inr (p.2-p.1-1))
  invFun p := (p.1+first p.2,p.1+second p.2)
  left_inv := by
    rintro ⟨a,b⟩
    by_cases h : b ≤ a
    · simp only [ite_eq_left h, first, second]
      congr 1
      omega
    · simp only [ite_eq_right h, first, second]
      congr 1
      omega
  right_inv := by
    rintro ⟨m,a | b⟩
    · have h : m ≤ m+a := by omega
      change (if m ≤ m+a then (m, Sum.inl (m+a-m)) else (m+a, Sum.inr (m-(m+a)-1))) = _
      rw [ite_eq_left h, Nat.add_sub_cancel_left]
    · have h : ¬m+(b+1) ≤ m := by omega
      change (if m+(b+1) ≤ m then (m+(b+1), Sum.inl (m-(m+(b+1))))
        else (m, Sum.inr (m+(b+1)-m-1))) = _
      rw [ite_eq_right h, Nat.add_sub_cancel_left, Nat.add_sub_cancel]

private def largestDegree (a b c d e f : ℕ) : ℕ :=
  max (max (a+c+e) (a+d+f)) (max (b+c+f) (b+d+e))

private def residualDegree (u : Triple Dir) : ℕ :=
  largestDegree (first u.1) (second u.1) (first u.2.1) (second u.2.1)
    (first u.2.2) (second u.2.2)

private def oddReversal (u : Triple Dir) : Bool :=
  (reversed u.1 ^^ reversed u.2.1) ^^ reversed u.2.2

private def triangle (u : Triple Dir) : Prop :=
  oddReversal u = true ∧ size u.1 ≠ 0 ∧ size u.2.1 ≠ 0 ∧ size u.2.2 ≠ 0

private def min3 (a b c : ℕ) : ℕ := min a (min b c)

private theorem largestDegree_translate (m₀ m₁ m₂ a b c d e f : ℕ) :
    largestDegree (m₀+a) (m₀+b) (m₁+c) (m₁+d) (m₂+e) (m₂+f) =
      m₀+m₁+m₂+largestDegree a b c d e f := by
  unfold largestDegree
  omega

private theorem residualDegree_formula (u : Triple Dir) :
    residualDegree u = size u.1 + size u.2.1 + size u.2.2 -
      (if oddReversal u then min3 (size u.1) (size u.2.1) (size u.2.2) else 0) := by
  rcases u with ⟨a|a,b|b,c|c⟩ <;>
    simp [residualDegree, largestDegree, min3, oddReversal, reversed, first, second, size] <;> omega

private theorem residualDegree_bound (u : Triple Dir) :
    size u.1 ≤ residualDegree u ∧ size u.2.1 ≤ residualDegree u ∧
      size u.2.2 ≤ residualDegree u := by
  rw [residualDegree_formula]
  split
  · unfold min3; omega
  · omega

private theorem residualDegree_other (u : Triple Dir) (h : ¬triangle u) :
    residualDegree u = size u.1 + size u.2.1 + size u.2.2 := by
  rw [residualDegree_formula]
  split
  · rename_i hp
    unfold triangle at h
    simp only [hp, true_and] at h
    unfold min3
    omega
  · omega

private def residualWeight : Graded where
  Space := Triple Dir
  weight := residualDegree
  finite_fiber n := by
    let code (d : Dir) (h : size d ≤ n) : Fin (n+1) ⊕ Fin (n+1) :=
      match d with
      | .inl a => .inl ⟨a, by simp [size, first, second] at h; omega⟩
      | .inr b => .inr ⟨b, by simp [size, first, second] at h; omega⟩
    have inject {a b : Dir} (ha : size a ≤ n) (hb : size b ≤ n)
        (h : code a ha = code b hb) : a=b := by
      cases a <;> cases b <;> simp [code, Fin.mk.injEq] at h ⊢
      all_goals exact h
    refine Finite.of_injective (β := Triple (Fin (n+1) ⊕ Fin (n+1))) (fun u => ?_) ?_
    · have h := residualDegree_bound u.val
      exact (code u.val.1 (by omega), code u.val.2.1 (by omega), code u.val.2.2 (by omega))
    · intro u v h
      exact Subtype.ext (Prod.ext (inject _ _ (congrArg Prod.fst h))
        (Prod.ext (inject _ _ (congrArg (fun r => r.2.1) h)) (inject _ _ (congrArg (fun r => r.2.2) h))))

private abbrev dirSize : Graded := G1.sum (G1.shift 1)
private abbrev tripleNat : Graded := G1.prod (G1.prod G1)
private abbrev sumSize : Graded := dirSize.prod (dirSize.prod dirSize)

private lemma size_eq_weight (d : Dir) : dirSize.weight d = size d := by
  cases d <;> simp [size, first, second, Graded.shift, Nat.add_comm]

private abbrev data0 : Graded := tripleNat.prod (residualWeight.prod G1)

private lemma rows0 (n : ℕ) (v : Fin 10 → ℕ) :
    pattern0.rows n v ↔
      v 0+(v 1+v 2+v 3)=n ∧
      v 4+(v 1+v 6+v 5)=n ∧
      v 7+(v 8+v 2+v 5)=n ∧
      v 9+(v 8+v 6+v 3)=n := by
  rw [four_rows]
  simp only [Fin.sum_univ_four]
  change (v 0+v 1+v 2+v 3=n ∧ v 1+v 4+v 5+v 6=n ∧
    v 2+v 5+v 7+v 8=n ∧ v 3+v 6+v 8+v 9=n) ↔ _
  omega

private abbrev Edges := Triple (ℕ × ℕ)

private def edgeDegree (u : Edges) : ℕ :=
  largestDegree u.1.1 u.1.2 u.2.1.1 u.2.1.2 u.2.2.1 u.2.2.2

private def balanceEdges : Edges ≃ Triple ℕ × Triple Dir where
  toFun u := let a := balancePair u.1
             let b := balancePair u.2.1
             let c := balancePair u.2.2
             ((a.1,b.1,c.1),(a.2,b.2,c.2))
  invFun u := (balancePair.symm (u.1.1,u.2.1),
    balancePair.symm (u.1.2.1,u.2.2.1),
    balancePair.symm (u.1.2.2,u.2.2.2))
  left_inv := by intro u; simp
  right_inv := by intro u; simp

private lemma balanceEdges_degree (m : Triple ℕ) (r : Triple Dir) :
    edgeDegree (balanceEdges.symm (m,r)) = m.1+m.2.1+m.2.2+residualDegree r := by
  exact largestDegree_translate _ _ _ _ _ _ _ _ _

private abbrev params0 (n : ℕ) := {v : Fin 10 → ℕ //
  v 0+(v 1+v 2+v 3)=n ∧ v 4+(v 1+v 6+v 5)=n ∧
  v 7+(v 8+v 2+v 5)=n ∧ v 9+(v 8+v 6+v 3)=n}

private def paramsToEdges (n : ℕ) : params0 n ≃ {u : Edges // edgeDegree u ≤ n} where
  toFun v := ⟨((v.val 1,v.val 8),(v.val 2,v.val 6),(v.val 3,v.val 5)), by
    have ⟨h0,h1,h2,h3⟩ := v.property
    change largestDegree (v.val 1) (v.val 8) (v.val 2) (v.val 6) (v.val 3) (v.val 5) ≤ n
    simp only [largestDegree, max_le_iff]
    omega⟩
  invFun u :=
    let a := u.val.1.1
    let b := u.val.1.2
    let c := u.val.2.1.1
    let d := u.val.2.1.2
    let e := u.val.2.2.1
    let f := u.val.2.2.2
    ⟨![n-(a+c+e),a,c,e,n-(a+d+f),f,d,n-(b+c+f),b,n-(b+d+e)], by
      have h : largestDegree a b c d e f ≤ n := u.property
      simp only [largestDegree, max_le_iff] at h
      change n-(a+c+e)+(a+c+e)=n ∧ n-(a+d+f)+(a+d+f)=n ∧
        n-(b+c+f)+(b+c+f)=n ∧ n-(b+d+e)+(b+d+e)=n
      omega⟩
  left_inv := by
    intro v
    have ⟨h0,h1,h2,h3⟩ := v.property
    apply Subtype.ext
    funext i
    fin_cases i
    · change n-(v.val 1+v.val 2+v.val 3)=v.val 0; omega
    · rfl
    · rfl
    · rfl
    · change n-(v.val 1+v.val 6+v.val 5)=v.val 4; omega
    · rfl
    · rfl
    · change n-(v.val 8+v.val 2+v.val 5)=v.val 7; omega
    · rfl
    · change n-(v.val 8+v.val 6+v.val 3)=v.val 9; omega
  right_inv := by intro u; rfl

private def edgesToFiber (n : ℕ) : {u : Edges // edgeDegree u ≤ n} ≃ data0.Fiber n := by
  let e : {u : Edges // edgeDegree u ≤ n} ≃
      {u : Triple ℕ × Triple Dir // u.1.1+u.1.2.1+u.1.2.2+residualDegree u.2 ≤ n} :=
    (balanceEdges.symm.subtypeEquiv (fun u => by rw [balanceEdges_degree])).symm
  refine e.trans ?_
  exact {
    toFun := fun ⟨⟨m,r⟩,h⟩ => ⟨(m,r,n-(m.1+m.2.1+m.2.2+residualDegree r)), by
      change 1*m.1+(1*m.2.1+1*m.2.2)+(residualDegree r+1*(n-(m.1+m.2.1+m.2.2+residualDegree r)))=n
      change m.1+m.2.1+m.2.2+residualDegree r ≤ n at h
      omega⟩
    invFun := fun ⟨⟨m,r,t⟩,h⟩ => ⟨(m,r), by
      change Triple ℕ at m
      change ℕ at t
      change 1*m.1+(1*m.2.1+1*m.2.2)+(residualDegree r+1*t)=n at h
      change m.1+m.2.1+m.2.2+residualDegree r ≤ n
      omega⟩
    left_inv := by rintro ⟨⟨m,r⟩,h⟩; rfl
    right_inv := by
      rintro ⟨⟨m,r,t⟩,h⟩
      change Triple ℕ at m
      change ℕ at t
      change 1*m.1+(1*m.2.1+1*m.2.2)+(residualDegree r+1*t)=n at h
      apply Subtype.ext
      exact Prod.ext rfl (Prod.ext rfl (by
        change n-(m.1+m.2.1+m.2.2+residualDegree r)=t
        omega)) }

private def fibers0 (n : ℕ) : TwistMat rep0 n ≃ data0.Fiber n :=
  (pattern0.equiv n).trans <| (Equiv.subtypeEquivRight (rows0 n)).trans <|
    (paramsToEdges n).trans (edgesToFiber n)

def positiveDir (b : Bool) (a : ℕ) : Dir :=
  if b then .inr a else .inl (a+1)

@[simp] lemma positiveDir_size (b : Bool) (a : ℕ) : size (positiveDir b a) = a+1 := by
  cases b <;> simp [positiveDir, first, second, size]

@[simp] private lemma positiveDir_reversed (b : Bool) (a : ℕ) : reversed (positiveDir b a) = b := by
  cases b <;> simp [positiveDir, reversed]

lemma positiveDir_rebuild (d : Dir) (h : size d ≠ 0) :
    positiveDir (reversed d) (size d-1) = d := by
  cases d with
  | inl a =>
    simp [positiveDir, first, second, size, reversed] at h ⊢
    omega
  | inr a => simp [positiveDir, first, second, size, reversed]

private def tripDirections (b : Bool × Bool) (a : Triple ℕ) : Triple Dir :=
  (positiveDir b.1 a.1, positiveDir b.2 a.2.1, positiveDir (!(b.1 ^^ b.2)) a.2.2)

private def triangleEquiv : {r : Triple Dir // triangle r} ≃ (Bool × Bool) × Triple ℕ where
  toFun r := ((reversed r.val.1, reversed r.val.2.1),
    (size r.val.1-1, size r.val.2.1-1, size r.val.2.2-1))
  invFun p := ⟨tripDirections p.1 p.2, by
    rcases p with ⟨⟨a,b⟩,u⟩
    cases a <;> cases b <;>
      simp [triangle, oddReversal, tripDirections]⟩
  left_inv := by
    rintro ⟨⟨u,v,w⟩,⟨h,hu,hv,hw⟩⟩
    have parity : ∀ a b c : Bool, ((a ^^ b) ^^ c) = true → Bool.not (a ^^ b) = c := by
      decide
    have hlast := parity (reversed u) (reversed v) (reversed w) h
    apply Subtype.ext
    change (positiveDir (reversed u) (size u-1), positiveDir (reversed v) (size v-1),
      positiveDir (!(reversed u ^^ reversed v)) (size w-1)) = (u,v,w)
    rw [hlast, positiveDir_rebuild u hu, positiveDir_rebuild v hv, positiveDir_rebuild w hw]
  right_inv := by
    rintro ⟨⟨a,b⟩,u⟩
    change ((reversed (positiveDir a u.1), reversed (positiveDir b u.2.1)),
      (size (positiveDir a u.1)-1, size (positiveDir b u.2.1)-1,
        size (positiveDir (!(a ^^ b)) u.2.2)-1)) = ((a,b), u)
    simp

private abbrev minZero (s : Triple ℕ) : Prop := min3 s.1 s.2.1 s.2.2 = 0

private def unshiftMin : Triple ℕ ≃ ℕ × {s : Triple ℕ // minZero s} where
  toFun u :=
    let t := min3 u.1 u.2.1 u.2.2
    (t,⟨(u.1-t,u.2.1-t,u.2.2-t), by
      dsimp [minZero,t]
      unfold min3
      omega⟩)
  invFun v := (v.1+v.2.val.1,v.1+v.2.val.2.1,v.1+v.2.val.2.2)
  left_inv := by
    rintro ⟨a,b,c⟩
    dsimp
    unfold min3
    simp only [Prod.mk.injEq]; omega
  right_inv := by
    rintro ⟨t, ⟨⟨a,b,c⟩,h⟩⟩
    have he : min3 (t+a) (t+b) (t+c) = t := by
      change min3 a b c = 0 at h
      unfold min3 at *
      omega
    apply Prod.ext
    · exact he
    · apply Subtype.ext
      change (t+a-min3 (t+a) (t+b) (t+c),t+b-min3 (t+a) (t+b) (t+c),
        t+c-min3 (t+a) (t+b) (t+c)) = (a,b,c)
      rw [he]
      simp only [Prod.mk.injEq]; omega

private def allPositiveEquiv : {s : Triple ℕ // ¬minZero s} ≃ Triple ℕ where
  toFun s := (s.val.1-1,s.val.2.1-1,s.val.2.2-1)
  invFun s := ⟨(s.1+1,s.2.1+1,s.2.2+1), by
    change min3 (s.1+1) (s.2.1+1) (s.2.2+1) ≠ 0
    unfold min3
    omega⟩
  left_inv := by
    rintro ⟨⟨a,b,c⟩,h⟩
    change min3 a b c ≠ 0 at h
    unfold min3 at h
    apply Subtype.ext
    change (a-1+1,b-1+1,c-1+1) = (a,b,c)
    simp only [Prod.mk.injEq]; omega
  right_inv := by
    rintro ⟨a,b,c⟩
    change (a+1-1,b+1-1,c+1-1) = _
    simp

private theorem zeroMin_series :
    (tripleNat.filter minZero).series = (1-x^3)*geom 1^3 := by
  have hp : (tripleNat.filter (fun s => ¬minZero s)).series = (tripleNat.shift 3).series := by
    apply Graded.series_congr allPositiveEquiv
    rintro ⟨⟨a,b,c⟩,h⟩
    change ℕ at a b c
    change min3 a b c ≠ 0 at h
    unfold min3 at h
    change 3+(1*(a-1)+(1*(b-1)+1*(c-1))) = 1*a+(1*b+1*c)
    omega
  have h := Graded.series_partition tripleNat minZero
  rw [hp] at h
  simp only [Graded.series_prod, Graded.series_nats, Graded.series_shift] at h
  linear_combination -h

private abbrev directionChoices := Graded.finite (Bool × Bool)
private abbrev triangleSumModel := directionChoices.prod (tripleNat.shift 3)
private abbrev triangleMaxModel := directionChoices.prod ((G2.prod (tripleNat.filter minZero)).shift 2)

private lemma four_directions : Nat.card (Bool × Bool) = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_prod]
  decide

private theorem triangleSum_series :
    (sumSize.filter triangle).series = 4*(x*geom 1)^3 := by
  rw [Graded.series_congr (B := triangleSumModel) triangleEquiv]
  · simp only [triangleSumModel, directionChoices, tripleNat, Graded.series_prod, Graded.series_shift,
      Graded.series_nats, Graded.series_finite, four_directions]
    ring
  · rintro ⟨⟨a,b,c⟩,⟨_,ha,hb,hc⟩⟩
    change 0+(3+(1*(size a-1)+(1*(size b-1)+1*(size c-1)))) =
      dirSize.weight a+(dirSize.weight b+dirSize.weight c)
    rw [size_eq_weight a, size_eq_weight b, size_eq_weight c]
    change size a ≠ 0 at ha
    change size b ≠ 0 at hb
    change size c ≠ 0 at hc
    omega

private theorem triangleMax_series :
    (residualWeight.filter triangle).series = 4*(x^2*geom 2*(1-x^3)*geom 1^3) := by
  let e := triangleEquiv.trans (Equiv.prodCongr (Equiv.refl (Bool × Bool)) unshiftMin)
  rw [Graded.series_congr (B := triangleMaxModel) e]
  · simp only [triangleMaxModel, directionChoices, Graded.series_prod, Graded.series_shift,
      Graded.series_nats, Graded.series_finite, four_directions, zeroMin_series]
    ring
  · rintro ⟨⟨a,b,c⟩,⟨hp,ha,hb,hc⟩⟩
    let t := min3 (size a-1) (size b-1) (size c-1)
    change 0+(2+(2*t+(1*(size a-1-t)+(1*(size b-1-t)+1*(size c-1-t))))) =
      residualDegree (a,b,c)
    rw [residualDegree_formula]
    change oddReversal (a,b,c) = true at hp
    simp only [hp, ite_true]
    dsimp [t,min3]
    change size a ≠ 0 at ha
    change size b ≠ 0 at hb
    change size c ≠ 0 at hc
    omega

private theorem residual_series : residualWeight.series =
    ((1+x)*geom 1)^3 + 4*(x^2*geom 2*(1-x^3)*geom 1^3-(x*geom 1)^3) := by
  have hsize : dirSize.series = (1+x)*geom 1 := by simp; ring
  have hsame : (residualWeight.filter (fun s => ¬triangle s)).series =
      (sumSize.filter (fun s => ¬triangle s)).series := by
    apply Graded.series_congr (A := residualWeight.filter (fun s => ¬triangle s))
      (B := sumSize.filter (fun s => ¬triangle s)) (Equiv.refl {u : Triple Dir // ¬triangle u})
    rintro ⟨⟨a,b,c⟩,h⟩
    change dirSize.weight a+(dirSize.weight b+dirSize.weight c) = residualDegree (a,b,c)
    rw [size_eq_weight a, size_eq_weight b, size_eq_weight c, residualDegree_other _ h]
    exact (Nat.add_assoc _ _ _).symm
  have hd := Graded.series_partition residualWeight triangle
  have hs := Graded.series_partition sumSize triangle
  rw [triangleMax_series, hsame] at hd
  rw [triangleSum_series] at hs
  change (dirSize.prod (dirSize.prod dirSize)).series = _ at hs
  simp only [Graded.series_prod, hsize] at hs
  linear_combination hd-hs

theorem twist0_series : twistSeries rep0 =
    geom 1^4 * (((1+x)*geom 1)^3 +
      4*(x^2*geom 2*(1-x^3)*geom 1^3-(x*geom 1)^3)) := by
  rw [twist_series_from_fibers rep0 data0 fibers0]
  simp only [data0, tripleNat, Graded.series_prod, Graded.series_nats, residual_series]
  ring

end A333886
