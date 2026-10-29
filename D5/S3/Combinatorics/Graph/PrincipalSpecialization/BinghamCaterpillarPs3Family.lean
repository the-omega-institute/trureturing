/- GID: D5/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrincipalSpecialization/BinghamCaterpillarPs3Family
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every positive j gives unequal second and equal third ordinary caterpillar specializations. -/

/-
proof_shape: Parts: bind-only; source representation; consumers: Vertex, alpha, beta.
proof_shape: Vertex: bind-only; source carrier; consumers: edgeRel, caterpillar.
proof_shape: edgeRel: bind-only; source edge list; consumers: caterpillar.
proof_shape: caterpillar: bind-only; source graph; consumers: claim, coloringEquiv.
proof_shape: ps: bind-only; source equation (2.1); consumers: claim, coloring_factorization.
proof_shape: alpha: bind-only; source family; consumers: claim, ps3_equal, ps2_alpha.
proof_shape: beta: bind-only; source family; consumers: claim, ps3_equal, ps2_beta.
proof_shape: claim: bind-only; source proposition; consumer: result.
proof_shape: root: bind-only; consumers: Leaf, assemble, restrictSpine, restrictLeaves.
proof_shape: Leaf: bind-only; consumers: Leaves, assemble_weight, coloring_factorization.
proof_shape: SpineGood: bind-only; consumers: Spine, ps_spine_sum, five_spine_good.
proof_shape: Spine: bind-only; consumers: assemble, restrictSpine, coloringEquiv.
proof_shape: Leaves: bind-only; consumers: assemble, restrictLeaves, coloringEquiv.
proof_shape: assemble: bind-only; consumers: coloringEquiv, assemble_weight.
proof_shape: restrictSpine: bind-only; consumers: restrictLeaves, coloringEquiv.
proof_shape: restrictLeaves: bind-only; consumer: coloringEquiv.
proof_shape: coloringEquiv: bind-only; consumer: coloring_factorization.
proof_shape: leafSum: bind-only; consumers: blockWeight, leafSum_eq.
proof_shape: blockWeight: bind-only; consumers: coloring_factorization, diagonal_identity, ps2_alpha, ps2_beta.
proof_shape: assemble_weight: bind-only; consumer: coloring_factorization.
proof_shape: coloring_factorization: bind-only; consumer: ps_spine_sum.
proof_shape: subtype_sum: bind-only; consumers: ps_spine_sum, leafSum_eq.
proof_shape: ps_spine_sum: bind-only; consumer: ps_five.
proof_shape: sum_finfun_succ: bind-only; consumer: ps_five.
proof_shape: fiveSum: bind-only; consumers: ps_five, diagonal_identity, ps2_alpha, ps2_beta.
proof_shape: five_spine_good: bind-only; consumer: ps_five.
proof_shape: ps_five: bind-only; consumers: ps3_equal, ps2_alpha, ps2_beta.
proof_shape: leafSum_eq: bind-only; consumers: diagonal_identity, ps2_alpha, ps2_beta.
proof_shape: diagonal_identity: bind-only; consumer: ps3_equal.
proof_shape: ps3_equal: bind-only; consumer: result.
proof_shape: ps2_alpha: bind-only; consumer: ps2_ne.
proof_shape: ps2_beta: bind-only; consumer: ps2_ne.
proof_shape: ps2_ne: bind-only; consumer: result.
proof_shape: result: bind-only; settles the first question in Remark 3.11.
escape_witness: none (bind-only).
admission_basis: open-problem-resolution (#23727, Tier 1).
Direct frozen D5 dependencies: none; all imports are pinned Mathlib.
The proof constructs an explicit coloring equivalence and normalizes its finite
weighted sums using upstream finite-product and finite-sum identities. No new
escape content is claimed for reindexing, distribution, or polynomial normalization.
Utility is none: the statement is an unbounded positive-parameter family; its
finite spine expansions are consumed algebraic identities, with arbitrary middle
weights in the three-color identity. There is no bounded j enumeration, checker,
numerical threshold, or separately delivered certified instance.
The fixed end blocks are 5,4,3. No classification of all such pairs is asserted.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.PNat.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Trureturing.OpenProblems.BinghamCaterpillarPs3Family

open scoped BigOperators

/-- A source composition of length l, with its positive parts explicitly indexed. -/
abbrev Parts (l : ℕ) := Fin l → ℕ+

/-- (i,0) is v_(i+1); (i,r), 1 ≤ r < a_i, is w_(i+1,r). -/
abbrev Vertex {l : ℕ} (a : Parts l) := (i : Fin l) × Fin (a i).val

/-- Source edge list, before Mathlib's symmetric, loopless closure. -/
def edgeRel {l : ℕ} (a : Parts l) (u v : Vertex a) : Prop :=
  (u.1 = v.1 ∧ u.2.val = 0 ∧ v.2.val ≠ 0) ∨
  (u.2.val = 0 ∧ v.2.val = 0 ∧ u.1.val + 1 = v.1.val)

/-- C_a: a spine path with a_i-1 pendant leaves at its ith vertex. -/
def caterpillar {l : ℕ} (a : Parts l) : SimpleGraph (Vertex a) :=
  SimpleGraph.fromRel (edgeRel a)

/-- Equation (2.1): finite principal specialization of the ordinary CSF.
The source explicitly changes to colors 0,...,k-1 in this equation. -/
noncomputable def ps {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Polynomial ℤ :=
  ∑ c : G.Coloring (Fin k), Polynomial.X ^ (∑ v : V, (c v).val)

/-- alpha_j, with j represented by a positive natural. -/
def alpha (j : ℕ+) : Parts 5 :=
  fun i => if i.val = 0 then 5 else if i.val = 1 then j else
    if i.val = 2 then j else if i.val = 3 then 4 else 3

/-- beta_j, with j represented by a positive natural. -/
def beta (j : ℕ+) : Parts 5 :=
  fun i => if i.val = 0 then 4 else if i.val = 1 then j else
    if i.val = 2 then j else if i.val = 3 then 5 else 3

/-- Remark 3.11, first question only; every positive integer j is quantified. -/
def claim : Prop :=
  ∀ j : ℕ+,
    ps (caterpillar (alpha j)) 2 ≠ ps (caterpillar (beta j)) 2 ∧
    ps (caterpillar (alpha j)) 3 = ps (caterpillar (beta j)) 3


private def root {l : ℕ} (a : Parts l) (i : Fin l) : Fin (a i).val :=
  ⟨0, (a i).pos⟩

private abbrev Leaf {l : ℕ} (a : Parts l) (i : Fin l) :=
  {r : Fin (a i).val // r ≠ root a i}

private def SpineGood {l k : ℕ} (c : Fin l → Fin k) : Prop :=
  ∀ i j, i.val + 1 = j.val → c i ≠ c j

private abbrev Spine (l k : ℕ) := {c : Fin l → Fin k // SpineGood c}

private abbrev Leaves {l k : ℕ} (a : Parts l) (c : Fin l → Fin k) :=
  ∀ i, Leaf a i → {d : Fin k // d ≠ c i}

private def assemble {l k : ℕ} (a : Parts l) (c : Spine l k) (f : Leaves a c.val) :
    (caterpillar a).Coloring (Fin k) :=
  SimpleGraph.Coloring.mk (fun v => if h : v.2 = root a v.1 then c.val v.1
    else (f v.1 ⟨v.2, h⟩).val) (by
    intro u v h
    rcases h with ⟨huv, h | h⟩
    · rcases h with ⟨hi, hu, hv⟩ | ⟨hu, hv, hij⟩
      · have hu' : u.2 = root a u.1 := Fin.ext hu
        have hv' : v.2 ≠ root a v.1 := fun e => hv (congrArg Fin.val e)
        simp only [dite_eq_left hu', dite_eq_right hv']
        simpa only [hi] using (f v.1 ⟨v.2, hv'⟩).property.symm
      · have hu' : u.2 = root a u.1 := Fin.ext hu
        have hv' : v.2 = root a v.1 := Fin.ext hv
        simp only [dite_eq_left hu', dite_eq_left hv']
        exact c.property _ _ hij
    · rcases h with ⟨hi, hv, hu⟩ | ⟨hv, hu, hji⟩
      · have hu' : u.2 ≠ root a u.1 := fun e => hu (congrArg Fin.val e)
        have hv' : v.2 = root a v.1 := Fin.ext hv
        simp only [dite_eq_right hu', dite_eq_left hv']
        simpa only [hi] using (f u.1 ⟨u.2, hu'⟩).property
      · have hu' : u.2 = root a u.1 := Fin.ext hu
        have hv' : v.2 = root a v.1 := Fin.ext hv
        simp only [dite_eq_left hu', dite_eq_left hv']
        exact (c.property _ _ hji).symm)

private def restrictSpine {l k : ℕ} {a : Parts l}
    (c : (caterpillar a).Coloring (Fin k)) : Spine l k :=
  ⟨fun i => c ⟨i, root a i⟩, by
    intro i j hij
    apply c.valid
    constructor
    · intro h
      have he : i.val = j.val := congrArg Fin.val (congrArg Sigma.fst h)
      omega
    · exact Or.inl (Or.inr ⟨rfl, rfl, hij⟩)⟩

private def restrictLeaves {l k : ℕ} {a : Parts l}
    (c : (caterpillar a).Coloring (Fin k)) : Leaves a (restrictSpine c).val :=
  fun i r => ⟨c ⟨i, r.val⟩, by
    apply c.valid
    constructor
    · intro h
      apply r.property
      exact eq_of_heq (Sigma.mk.inj h).2
    · apply Or.inr
      apply Or.inl
      refine ⟨rfl, rfl, ?_⟩
      intro h
      exact r.property (Fin.ext h)⟩

private def coloringEquiv {l k : ℕ} (a : Parts l) :
    (caterpillar a).Coloring (Fin k) ≃ (c : Spine l k) × Leaves a c.val where
  toFun c := ⟨restrictSpine c, restrictLeaves c⟩
  invFun c := assemble a c.1 c.2
  left_inv c := by
    apply RelHom.ext
    intro v
    rcases v with ⟨i,r⟩
    change (if h : r = root a i then c ⟨i, root a i⟩ else c ⟨i,r⟩) = _
    by_cases h : r = root a i
    · subst r; simp
    · simp [h]
  right_inv cf := by
    rcases cf with ⟨c,f⟩
    have h : restrictSpine (assemble a c f) = c := by
      apply Subtype.ext
      funext i
      change (if h : root a i = root a i then c.val i else (f i ⟨root a i,h⟩).val) = c.val i
      simp
    apply Sigma.ext h
    apply heq_of_eq
    funext i r
    apply Subtype.ext
    change (if h : r.val = root a i then c.val i else (f i ⟨r.val,h⟩).val) = (f i r).val
    simp [r.property]


attribute [local instance] Classical.propDecidable

private noncomputable def leafSum {k : ℕ} (c : Fin k) : Polynomial ℤ :=
  ∑ d : {d : Fin k // d ≠ c}, Polynomial.X ^ d.val.val

private noncomputable def blockWeight {k : ℕ} (m : ℕ+) (c : Fin k) : Polynomial ℤ :=
  Polynomial.X ^ c.val * leafSum c ^ (m.val - 1)

private lemma assemble_weight {l k : ℕ} (a : Parts l) (c : Spine l k)
    (f : Leaves a c.val) :
    (Polynomial.X : Polynomial ℤ) ^ (∑ v : Vertex a, (assemble a c f v).val) =
      ∏ i, (Polynomial.X ^ (c.val i).val *
        ∏ r : Leaf a i, Polynomial.X ^ (f i r).val.val) := by
  classical
  rw [← Finset.prod_pow_eq_pow_sum, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ (root a i)]
  apply congrArg₂ (· * ·)
  · change Polynomial.X ^ (if h : root a i = root a i then c.val i
      else (f i ⟨root a i,h⟩).val).val = _
    simp
  · apply Finset.prod_congr rfl
    intro r _
    change Polynomial.X ^ (if h : r.val = root a i then c.val i
      else (f i ⟨r.val,h⟩).val).val = _
    simp [r.property]

private lemma coloring_factorization {l k : ℕ} (a : Parts l) :
    ps (caterpillar a) k = ∑ c : Spine l k, ∏ i, blockWeight (a i) (c.val i) := by
  classical
  calc
    ps (caterpillar a) k =
        ∑ cf : (c : Spine l k) × Leaves a c.val,
          ∏ i, (Polynomial.X ^ (cf.1.val i).val *
            ∏ r : Leaf a i, Polynomial.X ^ (cf.2 i r).val.val) := by
      symm
      apply Fintype.sum_equiv (coloringEquiv a).symm
      intro cf
      exact (assemble_weight a cf.1 cf.2).symm
    _ = ∑ c : Spine l k, ∑ f : Leaves a c.val,
          ∏ i, (Polynomial.X ^ (c.val i).val *
            ∏ r : Leaf a i, Polynomial.X ^ (f i r).val.val) := by
      rw [Fintype.sum_sigma]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Fintype.prod_sum (fun i (f : Leaf a i → {d : Fin k // d ≠ c.val i}) =>
        Polynomial.X ^ (c.val i).val * ∏ r, Polynomial.X ^ (f r).val.val)]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.mul_sum]
      rw [← Fintype.prod_sum (fun (_ : Leaf a i) (d : {d : Fin k // d ≠ c.val i}) =>
        (Polynomial.X : Polynomial ℤ) ^ d.val.val)]
      simp [blockWeight, leafSum]


private lemma subtype_sum {A : Type*} [Fintype A] (p : A → Prop)
    (f : A → Polynomial ℤ) :
    (∑ x : {x // p x}, f x.val) = ∑ x : A, if p x then f x else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp), Finset.sum_filter]

private lemma ps_spine_sum {l k : ℕ} (a : Parts l) :
    ps (caterpillar a) k =
      ∑ c : Fin l → Fin k, if SpineGood c then ∏ i, blockWeight (a i) (c i) else 0 := by
  rw [coloring_factorization]
  exact subtype_sum (SpineGood (l:=l) (k:=k)) (fun c => ∏ i, blockWeight (a i) (c i))

private lemma sum_finfun_succ {A : Type*} [Fintype A] {n : ℕ}
    (f : (Fin (n+1) → A) → Polynomial ℤ) :
    ∑ c, f c = ∑ x, ∑ c : Fin n → A, f (Fin.cons x c) := by
  calc
    _ = ∑ p : A × (Fin n → A), f (Fin.cons p.1 p.2) :=
      (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => A)) f).symm
    _ = _ := Fintype.sum_prod_type _

private noncomputable def fiveSum {k : ℕ} (w : Fin 5 → Fin k → Polynomial ℤ) :=
  ∑ c₀ : Fin k, ∑ c₁ : Fin k, ∑ c₂ : Fin k, ∑ c₃ : Fin k, ∑ c₄ : Fin k,
    if c₀ ≠ c₁ ∧ c₁ ≠ c₂ ∧ c₂ ≠ c₃ ∧ c₃ ≠ c₄ then
      w 0 c₀ * w 1 c₁ * w 2 c₂ * w 3 c₃ * w 4 c₄ else 0

private lemma five_spine_good {k : ℕ} (c : Fin 5 → Fin k) :
    SpineGood c ↔ c 0 ≠ c 1 ∧ c 1 ≠ c 2 ∧ c 2 ≠ c 3 ∧ c 3 ≠ c 4 := by
  constructor
  · intro h
    exact ⟨h 0 1 rfl,h 1 2 rfl,h 2 3 rfl,h 3 4 rfl⟩
  · rintro ⟨h₀,h₁,h₂,h₃⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

set_option maxHeartbeats 800000 in
private lemma ps_five {k : ℕ} (a : Parts 5) :
    ps (caterpillar a) k = fiveSum (k:=k) (fun i c => blockWeight (a i) c) := by
  rw [ps_spine_sum]
  simp_rw [five_spine_good]
  unfold fiveSum
  rw [sum_finfun_succ]
  apply Finset.sum_congr rfl
  intro c0 _
  rw [sum_finfun_succ]
  apply Finset.sum_congr rfl
  intro c1 _
  rw [sum_finfun_succ]
  apply Finset.sum_congr rfl
  intro c2 _
  rw [sum_finfun_succ]
  apply Finset.sum_congr rfl
  intro c3 _
  rw [sum_finfun_succ]
  apply Finset.sum_congr rfl
  intro c4 _
  simp [Fin.prod_univ_succ, mul_assoc]
  rfl


private lemma leafSum_eq {k : ℕ} (c : Fin k) :
    leafSum c = ∑ d : Fin k, if d ≠ c then Polynomial.X ^ d.val else 0 := by
  unfold leafSum
  convert subtype_sum (fun d : Fin k => d ≠ c) (fun d => Polynomial.X ^ d.val) using 1
  all_goals
    apply Finset.sum_congr
    · ext x; simp
    · intro x _
      first | rfl | (split_ifs <;> rfl)

set_option maxHeartbeats 1000000 in
private lemma diagonal_identity (w : Fin 3 → Polynomial ℤ) :
    fiveSum ![blockWeight 5, w, w, blockWeight 4, blockWeight 3] =
      fiveSum ![blockWeight 4, w, w, blockWeight 5, blockWeight 3] := by
  norm_num [fiveSum, Fin.sum_univ_succ, blockWeight, leafSum_eq, Fin.cons]
  ring

private lemma ps3_equal (j : ℕ+) :
    ps (caterpillar (alpha j)) 3 = ps (caterpillar (beta j)) 3 := by
  rw [ps_five, ps_five]
  have ha : (fun i (c : Fin 3) => blockWeight (alpha j i) c) =
      ![blockWeight 5, blockWeight j, blockWeight j, blockWeight 4, blockWeight 3] := by
    funext i c
    fin_cases i <;> rfl
  have hb : (fun i (c : Fin 3) => blockWeight (beta j i) c) =
      ![blockWeight 4, blockWeight j, blockWeight j, blockWeight 5, blockWeight 3] := by
    funext i c
    fin_cases i <;> rfl
  rw [ha,hb]
  exact diagonal_identity _

private lemma ps2_alpha (j : ℕ+) :
    ps (caterpillar (alpha j)) 2 =
      Polynomial.X ^ (j.val+5) + Polynomial.X ^ (j.val+7) := by
  rw [ps_five]
  norm_num [fiveSum, Fin.sum_univ_succ, alpha, blockWeight, leafSum_eq, Fin.cons]
  have h5 : j.val + 5 = (j.val - 1) + 6 := by have := j.pos; omega
  have h7 : j.val + 7 = (j.val - 1) + 8 := by have := j.pos; omega
  rw [h5,h7, pow_add, pow_add]
  ring

private lemma ps2_beta (j : ℕ+) :
    ps (caterpillar (beta j)) 2 =
      Polynomial.X ^ (j.val+6) + Polynomial.X ^ (j.val+6) := by
  rw [ps_five]
  norm_num [fiveSum, Fin.sum_univ_succ, beta, blockWeight, leafSum_eq, Fin.cons]
  have h6 : j.val + 6 = (j.val - 1) + 7 := by have := j.pos; omega
  rw [h6, pow_add]
  ring

private lemma ps2_ne (j : ℕ+) :
    ps (caterpillar (alpha j)) 2 ≠ ps (caterpillar (beta j)) 2 := by
  rw [ps2_alpha,ps2_beta]
  intro heq
  have hc := congrArg (fun p : Polynomial ℤ => p.coeff (j.val+5)) heq
  simp [Polynomial.coeff_X_pow] at hc

theorem result : claim := by
  intro j
  exact ⟨ps2_ne j, ps3_equal j⟩

end Trureturing.OpenProblems.BinghamCaterpillarPs3Family
