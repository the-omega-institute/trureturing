/- GID: D5/S3/Quantum/Analysis/RefinedBMVDimThreeSize
   generality: G
   mirror-B: none(waiver:finite-gate-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneity and coefficient size bounds for packed refined BMV certificates. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThreeInteger

/-! # Bounds on the ordered integer certificate -/

namespace RefinedBMV.DimThree.Certificate

def Term.degree (m : Term) : Nat :=
  m.exponents.1 + m.exponents.2.1 + m.exponents.2.2

def coefficientNorm (l : List Term) : Nat :=
  (l.map fun m => m.coefficient.natAbs).sum

private def Controlled (l : List Term) (d M : Nat) : Prop :=
  (∀ m ∈ l, m.degree = d) ∧ coefficientNorm l ≤ M

private theorem empty_controlled (d M : Nat) : Controlled [] d M := by
  simp [Controlled, coefficientNorm]

private theorem mono {l : List Term} {d M N : Nat} (h : Controlled l d M) (hMN : M ≤ N) :
    Controlled l d N := ⟨h.1, Nat.le_trans h.2 hMN⟩

private theorem coefficientNorm_cons (x : Term) (xs : List Term) :
    coefficientNorm (x :: xs) = x.coefficient.natAbs + coefficientNorm xs := rfl

private theorem controlled_cons {x : Term} {xs : List Term} {d M : Nat}
    (hx : x.degree = d) (hxs : Controlled xs d M) :
    Controlled (x :: xs) d (x.coefficient.natAbs + M) := by
  refine ⟨?_, Nat.add_le_add_left hxs.2 _⟩
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hx
  · exact hxs.1 _ hm

private theorem merge_controlled (xs ys : List Term) (d : Nat)
    (hx : ∀ m ∈ xs, m.degree = d) (hy : ∀ m ∈ ys, m.degree = d) :
    Controlled (mergeTerms xs ys) d (coefficientNorm xs + coefficientNorm ys) := by
  induction xs generalizing ys with
  | nil => simpa [mergeTerms, Controlled, coefficientNorm] using hy
  | cons x xs ih =>
    have hxd := hx x (by simp)
    have hx' (m : Term) (hm : m ∈ xs) := hx m (by simp [hm])
    change Controlled (mergeInsert x xs (mergeTerms xs) ys) d _
    induction ys with
    | nil => simpa [mergeInsert, Controlled, coefficientNorm] using hx
    | cons y ys jh =>
      have hyd := hy y (by simp)
      have hy' (m : Term) (hm : m ∈ ys) := hy m (by simp [hm])
      rw [mergeInsert]
      split
      · have h := controlled_cons (x := ⟨x.exponents, x.coefficient + y.coefficient⟩)
            hxd (ih ys hx' hy')
        apply mono h
        change (x.coefficient + y.coefficient).natAbs + (coefficientNorm xs + coefficientNorm ys) ≤
          (x.coefficient.natAbs + coefficientNorm xs) + (y.coefficient.natAbs + coefficientNorm ys)
        have habs := Int.natAbs_add_le x.coefficient y.coefficient
        omega
      · split
        · have h := controlled_cons hxd (ih (y :: ys) hx' hy)
          apply mono h
          change x.coefficient.natAbs + (coefficientNorm xs + coefficientNorm (y :: ys)) ≤
            (x.coefficient.natAbs + coefficientNorm xs) + coefficientNorm (y :: ys)
          omega
        · have h := controlled_cons hyd (jh hy')
          apply mono h
          rw [coefficientNorm_cons (xs := ys)]
          omega

private theorem merge_bound {xs ys : List Term} {d M N : Nat}
    (hx : Controlled xs d M) (hy : Controlled ys d N) :
    Controlled (mergeTerms xs ys) d (M + N) :=
  mono (merge_controlled xs ys d hx.1 hy.1) (Nat.add_le_add hx.2 hy.2)

private theorem neg_bound (xs : List Term) (d : Nat)
    (hx : ∀ m ∈ xs, m.degree = d) :
    Controlled (xs.map Term.neg) d (coefficientNorm xs) := by
  induction xs with
  | nil => exact empty_controlled _ _
  | cons x xs ih =>
    have hxd := hx x (by simp)
    have h := controlled_cons (x := x.neg) hxd (ih (fun m hm => hx m (by simp [hm])))
    simpa [Term.neg, coefficientNorm_cons] using h

private theorem mulTerms_bound (x : Term) (ys : List Term) (d e : Nat)
    (hx : x.degree = d) (hy : ∀ m ∈ ys, m.degree = e) :
    Controlled (ys.map (Term.mul x)) (d + e) (x.coefficient.natAbs * coefficientNorm ys) := by
  induction ys with
  | nil =>
    change Controlled [] _ _
    exact empty_controlled _ _
  | cons y ys ih =>
    have hyd := hy y (by simp)
    have hprod : (x.mul y).degree = d + e := by
      simp only [Term.degree, Term.mul] at hx hyd ⊢
      omega
    have h := controlled_cons hprod (ih (fun m hm => hy m (by simp [hm])))
    simpa [Term.mul, coefficientNorm_cons, Nat.mul_add, Int.natAbs_mul] using h

private def productBudget (ps : List (List Term)) : Nat :=
  (ps.map coefficientNorm).sum

private theorem mergePairs_control (ps : List (List Term)) (d : Nat)
    (h : ∀ p ∈ ps, ∀ m ∈ p, m.degree = d) :
    (∀ p ∈ mergePairs ps, ∀ m ∈ p, m.degree = d) ∧
      productBudget (mergePairs ps) ≤ productBudget ps := by
  match ps with
  | [] => simp [mergePairs, productBudget]
  | [p] => exact ⟨h, Nat.le_refl _⟩
  | p :: q :: ps =>
    have hp : ∀ m ∈ p, m.degree = d := h p (by simp)
    have hq : ∀ m ∈ q, m.degree = d := h q (by simp)
    have hr : ∀ k ∈ ps, ∀ m ∈ k, m.degree = d := fun k hk => h k (by simp [hk])
    have hmerge := merge_controlled p q d hp hq
    have hi := mergePairs_control ps d hr
    constructor
    · intro k hk
      change k ∈ mergeTerms p q :: mergePairs ps at hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hmerge.1
      · exact hi.1 k hk
    · have := hmerge.2
      have := hi.2
      simp only [mergePairs, productBudget, List.map_cons, List.sum_cons] at *
      omega
termination_by structural ps

private theorem mergeProducts_control (k : Nat) (ps : List (List Term)) (d : Nat)
    (h : ∀ p ∈ ps, ∀ m ∈ p, m.degree = d) :
    Controlled (mergeProducts k ps) d (productBudget ps) := by
  induction k generalizing ps with
  | zero =>
    induction ps with
    | nil => exact empty_controlled _ _
    | cons p ps ih =>
      have hp : Controlled p d (coefficientNorm p) := ⟨h p (by simp), Nat.le_refl _⟩
      have hr : ∀ q ∈ ps, ∀ m ∈ q, m.degree = d := fun q hq => h q (by simp [hq])
      exact merge_bound hp (ih hr)
  | succ k ih =>
    rcases ps with _ | ⟨p, _ | ⟨q, ps⟩⟩
    · exact empty_controlled _ _
    · refine ⟨h p (by simp), ?_⟩
      change coefficientNorm p ≤ _
      simp [productBudget]
    · have hh := mergePairs_control (p :: q :: ps) d h
      exact mono (ih _ hh.1) hh.2

private theorem mul_bound {a b : Sparse} {d e M N : Nat}
    (ha : Controlled a.terms d M) (hb : Controlled b.terms e N) :
    Controlled (a * b).terms (d + e) (M * N) := by
  let ps := a.terms.map fun x => b.terms.map (Term.mul x)
  have hps : ∀ p ∈ ps, ∀ m ∈ p, m.degree = d + e := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact (mulTerms_bound x b.terms d e (ha.1 x hx) hb.1).1
  refine mono (mergeProducts_control 10 ps (d + e) hps) ?_
  apply Nat.le_trans _ (Nat.mul_le_mul ha.2 hb.2)
  have hsum (xs : List Term) (hx : ∀ x ∈ xs, x.degree = d) :
      productBudget (xs.map fun x => b.terms.map (Term.mul x)) ≤
        coefficientNorm xs * coefficientNorm b.terms := by
    induction xs with
    | nil => simp [productBudget, coefficientNorm]
    | cons x xs ih =>
      have hx' (y : Term) (hy : y ∈ xs) := hx y (by simp [hy])
      have h := Nat.add_le_add (mulTerms_bound x b.terms d e (hx x (by simp)) hb.1).2 (ih hx')
      simpa only [productBudget, List.map_cons, List.sum_cons, coefficientNorm_cons, Nat.add_mul]
        using h
  exact hsum a.terms ha.1

private theorem constant_bound (n : Nat) :
    Controlled (Sparse.constant n).terms 0 n := by
  simp [Controlled, Sparse.constant, Term.degree, coefficientNorm]

private theorem add_bound {a b : Sparse} {d M N : Nat}
    (ha : Controlled a.terms d M) (hb : Controlled b.terms d N) :
    Controlled (a + b).terms d (M + N) := merge_bound ha hb

private theorem sub_bound {a b : Sparse} {d M N : Nat}
    (ha : Controlled a.terms d M) (hb : Controlled b.terms d N) :
    Controlled (a - b).terms d (M + N) :=
  merge_bound ha (mono (neg_bound b.terms d hb.1) hb.2)

private theorem pow_bound {a : Sparse} {d M : Nat} (ha : Controlled a.terms d M) (k : Nat) :
    Controlled (a ^ k).terms (d * k) (M ^ k) := by
  induction k with
  | zero => exact constant_bound 1
  | succ k ih =>
    change Controlled (a ^ k * a).terms (d * (k + 1)) (M ^ (k + 1))
    simpa only [Nat.mul_succ, Nat.pow_succ] using mul_bound ih ha

private theorem sum_bound (l : List Sparse) (d M : Nat)
    (h : ∀ a ∈ l, Controlled a.terms d M) :
    Controlled l.sum.terms d (l.length * M) := by
  induction l with
  | nil => exact empty_controlled _ _
  | cons a l ih =>
    have h' (b : Sparse) (hb : b ∈ l) := h b (by simp [hb])
    have hh := add_bound (h a (by simp)) (ih h')
    simpa [Nat.add_mul, Nat.add_comm] using hh

private theorem gap_degree (p : Nat) (g : Nat × Nat × Nat) (hg : g ∈ gaps p) :
    g.1 + g.2.1 + g.2.2 = p := by
  unfold gaps at hg
  rcases List.mem_flatMap.mp hg with ⟨i, hi, hg⟩
  rcases List.mem_map.mp hg with ⟨j, hj, rfl⟩
  have hi' := List.mem_range.mp hi
  have hj' := List.mem_range.mp hj
  change i + j + (p - i - j) = p
  omega

private theorem defect_bound (p : Nat) {a b c : Sparse}
    (ha : Controlled a.terms 1 3) (hb : Controlled b.terms 1 3)
    (hc : Controlled c.terms 1 3) :
    Controlled (defect p a b c).terms (3 * p) (2 * (gaps p).length * 3 ^ (3 * p)) := by
  have hmonomial (g : Nat × Nat × Nat) (hg : g ∈ gaps p) :
      Controlled (((a ^ 3) ^ g.1) * ((b ^ 3) ^ g.2.1) * ((c ^ 3) ^ g.2.2)).terms
        (3 * p) (3 ^ (3 * p)) := by
    have hh := mul_bound
      (mul_bound (pow_bound (pow_bound ha 3) g.1) (pow_bound (pow_bound hb 3) g.2.1))
      (pow_bound (pow_bound hc 3) g.2.2)
    simpa only [Nat.one_mul, ← Nat.pow_mul, ← Nat.mul_add, ← Nat.pow_add, gap_degree p g hg] using hh
  have hsum : Controlled (((gaps p).map fun g =>
      (a ^ 3) ^ g.1 * (b ^ 3) ^ g.2.1 * (c ^ 3) ^ g.2.2).sum).terms
      (3 * p) ((gaps p).length * 3 ^ (3 * p)) := by
    have hh := sum_bound ((gaps p).map fun g =>
        (a ^ 3) ^ g.1 * (b ^ 3) ^ g.2.1 * (c ^ 3) ^ g.2.2) (3 * p) (3 ^ (3 * p)) (by
      intro a ha
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
      exact hmonomial g hg)
    simpa only [List.length_map] using hh
  have hbase : Controlled (a * b * c).terms 3 (3 ^ 3) := mul_bound (mul_bound ha hb) hc
  have hgeom := mul_bound (constant_bound (gaps p).length) (pow_bound hbase p)
  have hgeom' : Controlled (((↑(gaps p).length : Sparse) * (a * b * c) ^ p)).terms
      (3 * p) ((gaps p).length * 3 ^ (3 * p)) := by
    change Controlled (Sparse.constant (gaps p).length * (a * b * c) ^ p).terms _ _
    simpa only [Nat.zero_add, ← Nat.pow_mul] using hgeom
  have hh := sub_bound hsum hgeom'
  have he : (gaps p).length * 3 ^ (3 * p) + (gaps p).length * 3 ^ (3 * p) =
      2 * (gaps p).length * 3 ^ (3 * p) := by
    rw [show (2 : Nat) * (gaps p).length = (gaps p).length + (gaps p).length by omega, Nat.add_mul]
  exact he ▸ hh

private def defectSize (p : Nat) : Nat := 2 * (gaps p).length * 3 ^ (3 * p)

private theorem criterion_bound (p : Nat) {a b c : Sparse}
    (ha : Controlled a.terms 1 3) (hb : Controlled b.terms 1 3)
    (hc : Controlled c.terms 1 3) :
    Controlled (criterion p a b c).terms (12 * p) (24 * defectSize p ^ 4) := by
  let d := 3 * p
  let M := defectSize p
  let z := defect p a b c
  let Q := defect p b b a * defect p c c a + defect p a a b * defect p c c b
  let W := defect p a a c * defect p b b c
  have hz : Controlled z.terms d M := defect_bound p ha hb hc
  have hQ : Controlled Q.terms (d + d) (M * M + M * M) :=
    add_bound
      (mul_bound (defect_bound p hb hb ha) (defect_bound p hc hc ha))
      (mul_bound (defect_bound p ha ha hb) (defect_bound p hc hc hb))
  have hW : Controlled W.terms (d + d) (M * M) :=
    mul_bound (defect_bound p ha ha hc) (defect_bound p hb hb hc)
  have hz2 : Controlled (z ^ 2).terms (d + d) (M * M) := by
    simpa only [Nat.mul_succ, Nat.mul_zero, Nat.zero_add, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      using pow_bound hz 2
  have hdiff := sub_bound (sub_bound hz2 hQ) hW
  have hleft := mul_bound (mul_bound (constant_bound 4) hQ) hW
  have hd : 0 + (d + d) + (d + d) = (d + d) + (d + d) := by omega
  rw [hd] at hleft
  have hright := pow_bound hdiff 2
  simp only [Nat.mul_succ, Nat.mul_zero, Nat.zero_add, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    at hright
  have hh := sub_bound hleft hright
  change Controlled ((Sparse.constant 4 * Q * W - (z ^ 2 - Q - W) ^ 2).terms)
    (12 * p) (24 * M ^ 4)
  have he : d + d + (d + d) = 12 * p := by dsimp [d]; omega
  rw [he] at hh
  have hnorm : 4 * (M * M + M * M) * (M * M) +
      (M * M + (M * M + M * M) + M * M) * (M * M + (M * M + M * M) + M * M) =
      24 * M ^ 4 := by
    let u := M * M
    change 4 * (u + u) * u + (u + (u + u) + u) * (u + (u + u) + u) = 24 * M ^ 4
    have ht : u + u = 2 * u := by omega
    have hf : u + (u + u) + u = 4 * u := by omega
    have hp : M ^ 4 = u * u := by
      dsimp [u]
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    rw [hf, ht, hp]
    calc
      _ = (4 * 2) * (u * u) + (4 * 4) * (u * u) := by ac_rfl
      _ = _ := by rw [← Nat.add_mul]
  simpa only [hnorm] using hh

private theorem ordered_control (p : Nat) :
    Controlled (orderedPolynomial p).terms (12 * p) (24 * defectSize p ^ 4) := by
  let s : Sparse := ⟨[⟨(1, 0, 0), 1⟩]⟩
  let t : Sparse := ⟨[⟨(0, 1, 0), 1⟩]⟩
  let u : Sparse := ⟨[⟨(0, 0, 1), 1⟩]⟩
  have hs : Controlled s.terms 1 1 := by simp [Controlled, coefficientNorm, s, Term.degree]
  have ht : Controlled t.terms 1 1 := by simp [Controlled, coefficientNorm, t, Term.degree]
  have hu : Controlled u.terms 1 1 := by simp [Controlled, coefficientNorm, u, Term.degree]
  have hst := add_bound hs ht
  have hstu := add_bound hst hu
  exact criterion_bound p (mono hs (by decide)) (mono hst (by decide)) hstu

theorem ordered_degree (p : Nat) (m : Term) (hm : m ∈ (orderedPolynomial p).terms) :
    m.degree = 12 * p :=
  (ordered_control p).1 m hm

def digitBits (p : Nat) : Nat :=
  if p = 5 then 128 else if p = 6 then 160 else 168

theorem ordered_norm_lt (p : Nat) (hp : p = 5 ∨ p = 6 ∨ p = 7) :
    coefficientNorm (orderedPolynomial p).terms < 2 ^ digitBits p := by
  apply Nat.lt_of_le_of_lt (ordered_control p).2
  rcases hp with rfl | rfl | rfl <;> decide +kernel

end RefinedBMV.DimThree.Certificate
