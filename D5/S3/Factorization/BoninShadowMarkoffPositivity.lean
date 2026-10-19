/- GID: D5/S3/Factorization/BoninShadowMarkoffPositivity
   generality: G
   mirror-B: D5/B/S3/Factorization/BoninShadowMarkoffPositivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The rooted shadow Markoff tree has the conjectured quadrilateral positivity region. -/

/-
admission_basis: open-problem-resolution (#17060; Proved)
escape_witness: no_nonnegative_drift (via resonant_negative, necessary, result)
Direct frozen dependency F:
  D5/S3/Factorization/MarkovEquationMutation.markov_equation_mutation
  declaration statement_id:
  sha256:186570f9f6350dad09e43b147057586bf5e0ea26cd4536265608a0e0c4cbabec
Each dependency below follows through the other declarations of this module.
The settling theorem result consumes the negative-drift content path.
The shifted-cone and spine-recurrence helpers are consumed bind-only declarations.

step_poly
  proof_shape: bind-only
  consumers: cone_scan, path_valid, spine_next
  Direct frozen dependencies: none
eqn_poly
  proof_shape: bind-only
  consumers: cone_scan, path_valid
  Direct frozen dependencies: F
ordered_poly
  proof_shape: bind-only
  consumers: cone_scan, path_valid
  Direct frozen dependencies: none
integral_poly
  proof_shape: bind-only
  consumers: path_valid
  Direct frozen dependencies: none
cone_poly
  proof_shape: bind-only
  consumers: cone_scan
  Direct frozen dependencies: none
cone_nonneg
  proof_shape: bind-only
  consumers: sufficient
  Direct frozen dependencies: none
integral_nonneg_nat
  proof_shape: bind-only
  consumers: sufficient
  Direct frozen dependencies: none
scan_invariant
  proof_shape: bind-only
  consumers: cone_scan, path_valid
  Direct frozen dependencies: none
cone_scan
  proof_shape: bind-only
  consumers: sufficient
  Direct frozen dependencies: F
root_valid
  proof_shape: bind-only
  consumers: path_valid
  Direct frozen dependencies: none
path_valid
  proof_shape: bind-only
  consumers: sufficient, spine_next
  Direct frozen dependencies: F
first_steps
  proof_shape: bind-only
  consumers: sufficient, spine_mem
  Direct frozen dependencies: none
base_cone
  proof_shape: bind-only
  consumers: sufficient
  Direct frozen dependencies: none
sufficient
  proof_shape: bind-only
  consumers: result
  Direct frozen dependencies: F
spine_mem
  proof_shape: bind-only
  consumers: spine_next, necessary
  Direct frozen dependencies: none
spine_next
  proof_shape: bind-only
  consumers: spine_recurrence_l, spine_recurrence_r
  Direct frozen dependencies: F
spine_fixed_l
  proof_shape: bind-only
  consumers: spine_recurrence_l
  Direct frozen dependencies: none
spine_fixed_r
  proof_shape: bind-only
  consumers: spine_recurrence_r
  Direct frozen dependencies: none
spine_recurrence_l
  proof_shape: bind-only
  consumers: necessary
  Direct frozen dependencies: F
spine_recurrence_r
  proof_shape: bind-only
  consumers: necessary
  Direct frozen dependencies: F
no_nonnegative_drift
  proof_shape: content
  consumers: resonant_negative
  Direct frozen dependencies: none
real_recurrence_growth
  proof_shape: content
  consumers: resonant_negative
  Direct frozen dependencies: none
wronskian_step
  proof_shape: bind-only
  consumers: resonant_negative
  Direct frozen dependencies: none
resonant_negative
  proof_shape: content
  consumers: necessary
  Direct frozen dependencies: none
region_convex
  proof_shape: bind-only
  consumers: quadrilateral_region
  Direct frozen dependencies: none
quadrilateral_region
  proof_shape: bind-only
  consumers: region_chart
  Direct frozen dependencies: none
nat_node_nonneg
  proof_shape: bind-only
  consumers: necessary
  Direct frozen dependencies: none
necessary
  proof_shape: content
  consumers: result
  Direct frozen dependencies: F
region_chart
  proof_shape: bind-only
  consumers: result
  Direct frozen dependencies: none
result
  proof_shape: content
  consumers: settling result
  Direct frozen dependencies: F

The tree and rational chart follow Conjecture 1 and Section 5 of Bonin, arXiv:2403.07668v2.
The product type of Node and the coordinate projections are written directly, without aliases.
The public definitions and claim have the bodies of issue #17060, with Node expanded.
Only the rooted tree after the mandatory right and left moves is asserted.
The nonnegative-integer reading includes the boundary vertices; arbitrary root permutations
are outside this statement.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17538
-/

import D5.S3.Factorization.MarkovEquationMutation

noncomputable section

namespace D5.S3.Factorization.BoninShadowMarkoffPositivity

/-- The two moves of the source's `path`: `l` mutates the second pair, `r` the first. -/
inductive Move
  | l
  | r

/-- One mutation step, exactly as in the source's Section 5 code. -/
def step : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) → Move → (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)
  | (a, al, b, be, c, ga), .l =>
      (a, al, c, ga, (a ^ 2 + c ^ 2) / b, (-((a ^ 2 + c ^ 2) / b) * be + 2 * a * al + 2 * c * ga) /
          b)
  | (a, al, b, be, c, ga), .r =>
      (c, ga, b, be, (b ^ 2 + c ^ 2) / a, (-((b ^ 2 + c ^ 2) / a) * al + 2 * b * be + 2 * c * ga) /
          a)

/-- The source's `path(alpha, beta, gamma, C)`: the nodes along `'r' + 'l' + C`,
starting with the root `(1, 1, 1)`. -/
def path (al be ga : ℚ) (C : List Move) : List (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) :=
  (Move.r :: Move.l :: C).scanl step (1, al, 1, be, 1, ga)

/-- A node with `a, b, c, alpha, beta, gamma ∈ ℕ`, Eq. (8). -/
def IsNatNode (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) : Prop :=
  ∃ a al b be c ga : ℕ, t = ((a : ℚ), (al : ℚ), (b : ℚ), (be : ℚ), (c : ℚ), (ga : ℚ))

/-- The quadrilateral of Conjecture 1 in the chart `γ = 1`: vertices `(0:0:1)`,
`(1:0:2)`, `(1:1:1)`, `(0:2:1)`. -/
def quadrilateral : Set (ℚ × ℚ) :=
  convexHull ℚ {(0, 0), (1 / 2, 0), (1, 1), (0, 2)}

/-- Conjecture 1: a nonzero initial triple gives a nonnegative integer tree
exactly when its projective point lies in the quadrilateral. -/
def claim : Prop :=
  ∀ al be ga : ℕ, (al, be, ga) ≠ (0, 0, 0) →
    ((∀ C : List Move, ∀ t ∈ path al be ga C, IsNatNode t) ↔
      (0 < ga ∧ ((al : ℚ) / ga, (be : ℚ) / ga) ∈ quadrilateral))


private def Eqn (σ : ℚ) : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) → Prop
  | (a, x, b, y, c, z) => a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c ∧
      2 * a * x + 2 * b * y + 2 * c * z = 3 * (b * c * x + a * c * y + a * b * z) - σ * a * b * c

private def Ordered : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) → Prop
  | (a, _, b, _, c, _) => 1 ≤ a ∧ 1 ≤ b ∧ a ≤ c ∧ b ≤ c

private def Integral : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) → Prop
  | (a, x, b, y, c, z) => ∃ ai xi bi yi ci zi : ℤ,
      a = ai ∧ x = xi ∧ b = bi ∧ y = yi ∧ c = ci ∧ z = zi

private def poly (σ : ℚ) : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) → Move → (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)
  | (a, x, b, y, c, z), .l => (a, x, c, z, 3 * a * c - b, 3 * a * z + 3 * c * x - σ * a * c - y)
  | (a, x, b, y, c, z), .r => (c, z, b, y, 3 * b * c - a, 3 * b * z + 3 * c * y - σ * b * c - x)

private theorem step_poly (σ : ℚ) (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (m : Move) (h : Eqn σ t)
    (ho : Ordered t) : step t m = poly σ t m := by
  rcases t with ⟨a, x, b, y, c, z⟩
  rcases h with ⟨he, hd⟩
  rcases ho with ⟨ha, hb, hac, hbc⟩
  have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ha)
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hb)
  cases m
  · have hr : (a ^ 2 + c ^ 2) / b = 3 * a * c - b := by
      apply (div_eq_iff hb0).2
      nlinarith [he]
    simp only [step, poly, hr, Prod.mk.injEq, true_and]
    apply (div_eq_iff hb0).2
    linear_combination hd
  · have hr : (b ^ 2 + c ^ 2) / a = 3 * b * c - a := by
      apply (div_eq_iff ha0).2
      nlinarith [he]
    simp only [step, poly, hr, Prod.mk.injEq, true_and]
    apply (div_eq_iff ha0).2
    linear_combination hd

private theorem eqn_poly (σ : ℚ) (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (m : Move) (h : Eqn σ t) :
    Eqn σ (poly σ t m) := by
  rcases t with ⟨a, x, b, y, c, z⟩
  rcases h with ⟨he, hd⟩
  cases m <;> simp only [poly, Eqn] <;> constructor
  · exact D5.S3.Factorization.MarkovEquationMutation.markov_equation_mutation a c b (by nlinarith
      [he])
  · linear_combination hd
  · have h' := D5.S3.Factorization.MarkovEquationMutation.markov_equation_mutation c b a
      (by nlinarith [he])
    convert h' using 1 <;> ring
  · linear_combination hd

private theorem ordered_poly (σ : ℚ) (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (m : Move) (ho : Ordered t) :
    Ordered (poly σ t m) := by
  rcases t with ⟨a, x, b, y, c, z⟩
  rcases ho with ⟨ha, hb, hac, hbc⟩
  have hc : 1 ≤ c := le_trans ha hac
  have hl : c ≤ 3 * a * c - b := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc)]
  have hr : c ≤ 3 * b * c - a := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
  cases m
  · exact ⟨ha, hc, le_trans hac hl, hl⟩
  · exact ⟨hc, hb, hr, le_trans hbc hr⟩

private theorem integral_poly (σ : ℚ) (hσ : ∃ s : ℤ, σ = s) (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (m :
    Move)
    (h : Integral t) : Integral (poly σ t m) := by
  rcases t with ⟨a, x, b, y, c, z⟩
  rcases h with ⟨ai, xi, bi, yi, ci, zi, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases hσ with ⟨s, rfl⟩
  cases m
  · refine ⟨ai, xi, ci, zi, 3 * ai * ci - bi, 3 * ai * zi + 3 * ci * xi - s * ai * ci - yi, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;> push_cast <;> rfl
  · refine ⟨ci, zi, bi, yi, 3 * bi * ci - ai, 3 * bi * zi + 3 * ci * yi - s * bi * ci - xi, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;> push_cast <;> rfl


private def Cone (σ : ℚ) : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) → Prop
  | (a, x, b, y, c, z) => 0 ≤ 3 * x - σ * a ∧ 0 ≤ 3 * y - σ * b ∧
      3 * x - σ * a ≤ 3 * z - σ * c ∧ 3 * y - σ * b ≤ 3 * z - σ * c

private theorem cone_poly (σ : ℚ) (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (m : Move) (ho : Ordered t) (h :
    Cone σ t) :
    Cone σ (poly σ t m) := by
  rcases t with ⟨a, x, b, y, c, z⟩
  rcases ho with ⟨ha, hb, hac, hbc⟩
  rcases h with ⟨hx, hy, hxz, hyz⟩
  have hz : 0 ≤ 3 * z - σ * c := le_trans hx hxz
  have hc : 1 ≤ c := le_trans ha hac
  have hl : 3 * z - σ * c ≤ 3 * (3 * a * z + 3 * c * x - σ * a * c - y) - σ * (3 * a * c - b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hz, mul_nonneg (by linarith : 0 ≤ c) hx]
  have hr : 3 * z - σ * c ≤ 3 * (3 * b * z + 3 * c * y - σ * b * c - x) - σ * (3 * b * c - a) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) hz, mul_nonneg (by linarith : 0 ≤ c) hy]
  cases m
  · exact ⟨hx, hz, le_trans hxz hl, hl⟩
  · exact ⟨hz, hy, hr, le_trans hyz hr⟩

private theorem cone_nonneg (σ : ℚ) (hs : 0 ≤ σ) (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (ho : Ordered t) (h
    : Cone σ t) :
    (0 ≤ t.2.1 ∧ 0 ≤ t.2.2.2.1 ∧ 0 ≤ t.2.2.2.2.2) := by
  rcases t with ⟨a, x, b, y, c, z⟩
  rcases ho with ⟨ha, hb, hac, hbc⟩
  rcases h with ⟨hx, hy, hxz, hyz⟩
  have hc : 0 ≤ c := (zero_le_one.trans ha).trans hac
  have hsa := mul_nonneg hs (zero_le_one.trans ha)
  have hsb := mul_nonneg hs (zero_le_one.trans hb)
  have hsc := mul_nonneg hs hc
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem integral_nonneg_nat (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (hi : Integral t) (ho : Ordered
    t)
    (hn : (0 ≤ t.2.1 ∧ 0 ≤ t.2.2.2.1 ∧ 0 ≤ t.2.2.2.2.2)) : IsNatNode t := by
  rcases t with ⟨a, x, b, y, c, z⟩
  rcases hi with ⟨ai, xi, bi, yi, ci, zi, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases ho with ⟨ha, hb, hac, hbc⟩
  rcases hn with ⟨hx, hy, hz⟩
  have ha0 : 0 ≤ ai := Rat.intCast_nonneg.mp (zero_le_one.trans ha)
  have hb0 : 0 ≤ bi := Rat.intCast_nonneg.mp (zero_le_one.trans hb)
  have hc0 : 0 ≤ ci := Rat.intCast_nonneg.mp ((zero_le_one.trans ha).trans hac)
  dsimp only at hx hy hz
  have hx0 : 0 ≤ xi := Rat.intCast_nonneg.mp hx
  have hy0 : 0 ≤ yi := Rat.intCast_nonneg.mp hy
  have hz0 : 0 ≤ zi := Rat.intCast_nonneg.mp hz
  refine ⟨ai.toNat, xi.toNat, bi.toNat, yi.toNat, ci.toNat, zi.toNat, ?_⟩
  simp only [Prod.mk.injEq]
  norm_cast
  simp [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0, Int.toNat_of_nonneg hc0,
    Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0, Int.toNat_of_nonneg hz0]

private theorem scan_invariant (P : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) → Prop) (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ))
    (ht : P t)
    (hm : ∀ t m, P t → P (step t m)) (C : List Move) :
    ∀ s ∈ C.scanl step t, P s := by
  intro s hs
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
  rw [List.getElem_scanl]
  exact List.foldlRecOn _ _ ht (fun t ht m _ => hm t m ht)

private theorem cone_scan (σ : ℚ) (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (he : Eqn σ t) (ho : Ordered t) (hc
    : Cone σ t)
    (C : List Move) : ∀ s ∈ C.scanl step t, Cone σ s := by
  have hi : ∀ s ∈ C.scanl step t, Eqn σ s ∧ Ordered s ∧ Cone σ s := by
    refine scan_invariant _ _ ⟨he, ho, hc⟩ ?_ C
    intro s m h
    rw [step_poly _ _ _ h.1 h.2.1]
    exact ⟨eqn_poly _ _ _ h.1, ordered_poly _ _ _ h.2.1, cone_poly _ _ _ h.2.1 h.2.2⟩
  intro s hs
  exact (hi s hs).2.2

private theorem root_valid (al be ga : ℤ) :
    Eqn (al + be + ga) (1, al, 1, be, 1, ga) ∧ Ordered (1, al, 1, be, 1, ga) ∧
      Integral (1, al, 1, be, 1, ga) := by
  refine ⟨?_, by norm_num [Ordered], ?_⟩
  · constructor
    · norm_num
    · ring
  · exact ⟨1, al, 1, be, 1, ga, by norm_num, by simp, by norm_num, by simp, by norm_num, by simp⟩

private theorem path_valid (al be ga : ℤ) (C : List Move) :
    ∀ t ∈ path al be ga C, Eqn (al + be + ga) t ∧ Ordered t ∧ Integral t := by
  unfold path
  refine scan_invariant (fun t => Eqn (al + be + ga) t ∧ Ordered t ∧ Integral t)
    (1, al, 1, be, 1, ga) (root_valid al be ga) ?_ (Move.r::Move.l::C)
  intro t m h
  rw [step_poly _ _ _ h.1 h.2.1]
  exact ⟨eqn_poly _ _ _ h.1, ordered_poly _ _ _ h.2.1,
    integral_poly _ ⟨(al:ℤ) + be + ga, by push_cast; rfl⟩ _ _ h.2.2⟩

private def base (al be ga : ℚ) : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) := (1, ga, 2, 2 * (be + ga - al), 5, -8 *
    al + 3 * be + 10 * ga)

private theorem first_steps (al be ga : ℚ) :
    step (step (1, al, 1, be, 1, ga) .r) .l = base al be ga := by
  simp only [step, base]
  norm_num
  constructor <;> ring

private theorem base_cone (al be ga : ℚ) (hu : al + be ≤ 2 * ga) (hv : 2 * al ≤ be + ga) :
    Cone (al + be + ga) (base al be ga) := by
  dsimp [Cone, base]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith


private theorem sufficient (al be ga : ℕ) (hu : al + be ≤ 2 * ga) (hv : 2 * al ≤ be + ga) :
    ∀ C : List Move, ∀ t ∈ path al be ga C, IsNatNode t := by
  have huq : (al:ℚ) + be ≤ 2 * ga := by exact_mod_cast hu
  have hvq : 2 * (al:ℚ) ≤ be + ga := by exact_mod_cast hv
  have hs : (0:ℚ) ≤ al + be + ga := by positivity
  have hbase := path_valid al be ga [] (base al be ga) (by simp [path, List.scanl_cons,
      first_steps])
  have hsc (C : List Move) : ∀ t ∈ C.scanl step (base al be ga), IsNatNode t := by
    have hco := cone_scan (al + be + ga) (base al be ga) hbase.1 hbase.2.1
      (base_cone _ _ _ huq hvq) C
    intro t ht
    have hm : t ∈ path al be ga C := by
      simp only [path, List.scanl_cons, first_steps]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ht)
    have h := path_valid al be ga C t hm
    exact integral_nonneg_nat _ h.2.2 h.2.1 (cone_nonneg _ hs _ h.2.1 (hco t ht))
  intro C t ht
  simp only [path, List.scanl_cons] at ht
  rw [first_steps] at ht
  rcases List.mem_cons.mp ht with rfl|ht
  · exact ⟨1, al, 1, be, 1, ga, rfl⟩
  rcases List.mem_cons.mp ht with rfl|ht
  · have h := path_valid al be ga [] (step (1, al, 1, be, 1, ga) .r) (by simp [path,
      List.scanl_cons])
    apply integral_nonneg_nat _ h.2.2 h.2.1
    norm_num [step]
    linarith
  · exact hsc C t ht


private def spine (al be ga : ℚ) (m : Move) (n : ℕ) : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) :=
  (List.replicate n m).foldl step (base al be ga)

private theorem spine_mem (al be ga : ℚ) (m : Move) (n : ℕ) :
    spine al be ga m n ∈ path al be ga (List.replicate n m) := by
  simp only [path, List.scanl_cons, first_steps]
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  have hn : (List.replicate n m).scanl step (base al be ga) ≠ [] := List.scanl_ne_nil
  have h := List.getLast_mem hn
  rw [List.getLast_scanl] at h
  exact h

private theorem spine_next (al be ga : ℕ) (m : Move) (n : ℕ) :
    spine al be ga m (n + 1) = poly (al + be + ga) (spine al be ga m n) m := by
  have h := path_valid al be ga _ _ (spine_mem al be ga m n)
  simpa [spine, List.replicate_succ', List.foldl_append] using
    (step_poly (al + be + ga) (spine al be ga m n) m h.1 h.2.1)


private theorem spine_fixed_l (al be ga : ℕ) (n : ℕ) :
    (spine al be ga .l n).1 = 1 ∧ (spine al be ga .l n).2.1 = ga := by
  unfold spine
  apply List.foldlRecOn (motive := fun t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) =>
    t.1 = 1 ∧ t.2.1 = (ga : ℚ))
  · simp [base]
  · intro t ht m hm
    have hm := List.eq_of_mem_replicate hm
    subst m
    simpa only [step] using ht

private theorem spine_fixed_r (al be ga : ℕ) (n : ℕ) :
    (spine al be ga .r n).2.2.1 = 2 ∧ (spine al be ga .r n).2.2.2.1 = 2 * (be + ga - al) := by
  unfold spine
  apply List.foldlRecOn (motive := fun t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ) =>
    t.2.2.1 = 2 ∧ t.2.2.2.1 = 2 * ((be : ℚ) + ga - al))
  · simp [base]
  · intro t ht m hm
    have hm := List.eq_of_mem_replicate hm
    subst m
    simpa only [step] using ht

private theorem spine_recurrence_l (al be ga : ℕ) (n : ℕ) :
    (spine al be ga .l (n + 2)).2.2.1 = 3 * (spine al be ga .l (n + 1)).2.2.1 - (spine al be ga .l
        n).2.2.1 ∧
    (spine al be ga .l (n + 2)).2.2.2.1 = 3 * (spine al be ga .l (n + 1)).2.2.2.1 - (spine al be ga
        .l n).2.2.2.1 + (2 * ga - al - be) * (spine al be ga .l (n + 1)).2.2.1 := by
  have hf := spine_fixed_l al be ga n
  rw [show n + 2 = (n + 1) + 1 by omega, spine_next, spine_next]
  rcases he : spine (al:ℚ) be ga .l n with ⟨a, x, b, y, c, z⟩
  simp only [he] at hf
  rcases hf with ⟨rfl, rfl⟩
  constructor <;> dsimp [poly] <;> ring

private theorem spine_recurrence_r (al be ga : ℕ) (n : ℕ) :
    (spine al be ga .r (n + 2)).1 = 6 * (spine al be ga .r (n + 1)).1 - (spine al be ga .r n).1 ∧
    (spine al be ga .r (n + 2)).2.1 = 6 * (spine al be ga .r (n + 1)).2.1 - (spine al be ga .r
        n).2.1 + (4 * ((be:ℚ) + ga - 2 * al)) * (spine al be ga .r (n + 1)).1 := by
  have hf := spine_fixed_r al be ga n
  rw [show n + 2 = (n + 1) + 1 by omega, spine_next, spine_next]
  rcases he : spine (al:ℚ) be ga .r n with ⟨a, x, b, y, c, z⟩
  simp only [he] at hf
  rcases hf with ⟨rfl, rfl⟩
  constructor <;> dsimp [poly] <;> ring


private theorem no_nonnegative_drift (q r : ℕ → ℚ) (c : ℚ) (hc : c < 0)
    (hr : ∀ n, 0 ≤ r n ∧ r n ≤ 1)
    (hd : ∀ n, q (n + 2) - q (n + 1) ≤ r n * (q (n + 1) - q n) + c) :
    ∃ n, q n < 0 := by
  by_contra hn
  push Not at hn
  let d : ℕ → ℚ := fun n => q (n + 1) - q n
  have hd' : ∀ n, d (n + 1) ≤ r n * d n + c := hd
  have hex : ∃ N, d N ≤ 0 := by
    by_contra he
    push Not at he
    have hb : ∀ n, d n ≤ d 0 + (n:ℚ) * c := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hm := mul_le_mul_of_nonneg_right (hr n).2 (le_of_lt (he n))
        have hh := hd' n
        push_cast
        nlinarith
    obtain ⟨n, hnat⟩ := exists_nat_gt (d 0 / (-c))
    have hm : d 0 < (n:ℚ) * (-c) := (div_lt_iff₀ (by linarith : 0 < -c)).mp hnat
    have := hb n
    have := he n
    nlinarith
  obtain ⟨N, hN⟩ := hex
  have htail : ∀ m, d (N + m + 1) ≤ c := by
    intro m
    induction m with
    | zero =>
      have hm := mul_nonpos_of_nonneg_of_nonpos (hr N).1 hN
      simpa using (le_trans (hd' N) (by linarith : r N * d N + c ≤ c))
    | succ m ih =>
      have hm := mul_nonpos_of_nonneg_of_nonpos (hr (N + m + 1)).1 (show d (N + m + 1) ≤ 0 by
          linarith)
      have hh := hd' (N + m + 1)
      have heq : N + (m + 1) + 1 = N + m + 1 + 1 :=
        congrArg (fun k : ℕ => k + 1) (Nat.add_assoc N m 1).symm
      rw [heq]
      linarith
  have hq : ∀ m, q (N + 1 + m) ≤ q (N + 1) + (m:ℚ) * c := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hh := htail m
      dsimp [d] at hh
      have heq' : N + m + 1 = N + 1 + m := Nat.add_right_comm N m 1
      rw [heq'] at hh
      push_cast
      have heq'' : N + 1 + m + 1 = N + 1 + (m + 1) := Nat.add_assoc (N + 1) m 1
      rw [heq''] at hh
      nlinarith
  obtain ⟨m, hm⟩ := exists_nat_gt (q (N + 1) / (-c))
  have hmul : q (N + 1) < (m:ℚ) * (-c) := (div_lt_iff₀ (by linarith : 0 < -c)).mp hm
  have := hq m
  have := hn (N + 1 + m)
  nlinarith

private theorem real_recurrence_growth (t : ℕ → ℚ) (k : ℚ) (hk : 3 ≤ k)
    (h0 : 0 < t 0) (h01 : t 0 < t 1) (h1 : t 1 ≤ k * t 0)
    (ht : ∀ n, t (n + 2) = k * t (n + 1) - t n) :
    ∀ n, 0 < t n ∧ t n < t (n + 1) ∧ t (n + 1) ≤ k * t n := by
  intro n
  induction n with
  | zero => exact ⟨h0, h01, h1⟩
  | succ n ih =>
    have hpos : 0 < t (n + 1) := lt_trans ih.1 ih.2.1
    have hrec := ht n
    have hg := mul_nonneg (show 0 ≤ k - 3 by linarith) (le_of_lt hpos)
    refine ⟨hpos, ?_, ?_⟩ <;> rw [show n + 1 + 1 = n + 2 by omega] <;> linarith [ih.1, ih.2.1]

private theorem wronskian_step (t s : ℕ → ℚ) (k h : ℚ)
    (ht : ∀ n, t (n + 2) = k * t (n + 1) - t n)
    (hs : ∀ n, s (n + 2) = k * s (n + 1) - s n + h * t (n + 1)) (n : ℕ) :
    s (n + 2) * t (n + 1) - s (n + 1) * t (n + 2) = (s (n + 1) * t n - s n * t (n + 1)) + h * t (n
        + 1) ^ 2 := by
  rw [ht n, hs n]
  ring

private theorem resonant_negative (t s : ℕ → ℚ) (k h : ℚ) (hk : 3 ≤ k)
    (h0 : 0 < t 0) (h01 : t 0 < t 1) (h1 : t 1 ≤ k * t 0)
    (ht : ∀ n, t (n + 2) = k * t (n + 1) - t n)
    (hs : ∀ n, s (n + 2) = k * s (n + 1) - s n + h * t (n + 1))
    (hh : h < 0) : ∃ n, s n < 0 := by
  have hg := real_recurrence_growth t k hk h0 h01 h1 ht
  let q : ℕ → ℚ := fun n => s n / t n
  let r : ℕ → ℚ := fun n => t n / t (n + 2)
  have hk0 : 0 < k := lt_of_le_of_lt' hk rfl
  have hc : h / k < 0 := div_neg_of_neg_of_pos hh hk0
  have hr : ∀ n, 0 ≤ r n ∧ r n ≤ 1 := by
    intro n
    refine ⟨le_of_lt (div_pos (hg n).1 (hg (n + 2)).1), ?_⟩
    exact (div_le_one (hg (n + 2)).1).mpr (le_of_lt (lt_trans (hg n).2.1 (hg (n + 1)).2.1))
  have hd : ∀ n, q (n + 2) - q (n + 1) ≤ r n * (q (n + 1) - q n) + h / k := by
    intro n
    have ht0 : t n ≠ 0 := ne_of_gt (hg n).1
    have ht1 : t (n + 1) ≠ 0 := ne_of_gt (hg (n + 1)).1
    have ht2 : t (n + 2) ≠ 0 := ne_of_gt (hg (n + 2)).1
    have he : q (n + 2) - q (n + 1) = r n * (q (n + 1) - q n) + h * t (n + 1) / t (n + 2) := by
      dsimp [q, r]
      field_simp
      have hw := wronskian_step t s k h ht hs n
      linear_combination hw
    rw [he]
    apply add_le_add le_rfl
    apply (div_le_div_iff₀ (hg (n + 2)).1 hk0).mpr
    have hm := mul_le_mul_of_nonpos_left (hg (n + 1)).2.2 (le_of_lt hh)
    nlinarith
  obtain ⟨n, hn⟩ := no_nonnegative_drift q r (h / k) hc hr hd
  refine ⟨n, ?_⟩
  have := (div_lt_iff₀ (hg n).1).mp hn
  simpa using this

private def Region : Set (ℚ × ℚ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 2 ∧ 2 * p.1 ≤ p.2 + 1}

private theorem region_convex : Convex ℚ Region := by
  let f : (ℚ × ℚ) →ₗ[ℚ] ℚ := LinearMap.fst ℚ ℚ ℚ
  let g : (ℚ × ℚ) →ₗ[ℚ] ℚ := LinearMap.snd ℚ ℚ ℚ
  have h := (convex_halfSpace_ge f.isLinear (0 : ℚ)).inter
    ((convex_halfSpace_ge g.isLinear (0 : ℚ)).inter
      ((convex_halfSpace_le (f + g).isLinear (2 : ℚ)).inter
        (convex_halfSpace_le ((2 : ℚ) • f - g).isLinear (1 : ℚ))))
  have heq : Region = {w | 0 ≤ f w} ∩ ({w | 0 ≤ g w} ∩
      ({w | (f + g) w ≤ 2} ∩ {w | ((2 : ℚ) • f - g) w ≤ 1})) := by
    ext p
    change (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 2 ∧ 2 * p.1 ≤ p.2 + 1) ↔
      (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 2 ∧ 2 * p.1 - p.2 ≤ 1)
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, h3, by linarith⟩
  rw [heq]
  exact h

private theorem quadrilateral_region (p : ℚ × ℚ) : p ∈ quadrilateral ↔ p ∈ Region := by
  constructor
  · apply convexHull_min _ region_convex
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl|rfl|rfl|rfl <;> norm_num [Region]
  · rcases p with ⟨x, y⟩
    rintro ⟨hx, hy, hxy, hxy'⟩
    change (x, y) ∈ convexHull ℚ {(0, 0), (1 / 2, 0), (1, 1), (0, 2)}
    by_cases h : y ≤ x
    · refine mem_convexHull_of_exists_fintype
        ![1 - 2 * x + y, 2 * (x - y), y] ![(0, 0), (1 / 2, 0), (1, 1)] ?_ ?_ ?_ ?_
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_succ]; ring
      · intro i; fin_cases i <;> simp
      · (ext <;> simp [Fin.sum_univ_succ]); ring
    · have h : x ≤ y := Std.le_of_not_ge h
      refine mem_convexHull_of_exists_fintype
        ![1 - (x + y) / 2, x, (y - x) / 2] ![(0, 0), (1, 1), (0, 2)] ?_ ?_ ?_ ?_
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_succ]; ring
      · intro i; fin_cases i <;> simp
      · ext <;> simp [Fin.sum_univ_succ]

private theorem nat_node_nonneg (t : (ℚ × ℚ × ℚ × ℚ × ℚ × ℚ)) (h : IsNatNode t) : (0 ≤ t.2.1 ∧ 0 ≤
    t.2.2.2.1 ∧ 0 ≤ t.2.2.2.2.2) := by
  rcases h with ⟨a, x, b, y, c, z, rfl⟩
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, Nat.cast_nonneg _⟩

private theorem necessary (al be ga : ℕ)
    (hall : ∀ C : List Move, ∀ t ∈ path al be ga C, IsNatNode t) :
    al + be ≤ 2 * ga ∧ 2 * al ≤ be + ga := by
  have hnl : ∀ n, 0 ≤ (spine al be ga .l n).2.2.2.1 := by
    intro n
    exact (nat_node_nonneg _ (hall _ _ (spine_mem al be ga .l n))).2.1
  have hnr : ∀ n, 0 ≤ (spine al be ga .r n).2.1 := by
    intro n
    exact (nat_node_nonneg _ (hall _ _ (spine_mem al be ga .r n))).1
  have hu : 0 ≤ 2 * (ga:ℚ) - al - be := by
    by_contra hh
    have hh : 2 * (ga:ℚ) - al - be < 0 := lt_of_not_ge hh
    obtain ⟨n, hn⟩ := resonant_negative
      (fun n => (spine al be ga .l n).2.2.1) (fun n => (spine al be ga .l n).2.2.2.1)
      3 (2 * (ga:ℚ) - al - be) (by norm_num)
      (by norm_num [spine, base]) (by norm_num [spine, base, step])
      (by norm_num [spine, base, step])
      (fun n => (spine_recurrence_l al be ga n).1)
      (fun n => (spine_recurrence_l al be ga n).2) hh
    linarith [hnl n]
  have hv : 0 ≤ 4 * ((be:ℚ) + ga - 2 * al) := by
    by_contra hh
    have hh : 4 * ((be:ℚ) + ga - 2 * al) < 0 := lt_of_not_ge hh
    obtain ⟨n, hn⟩ := resonant_negative
      (fun n => (spine al be ga .r n).1) (fun n => (spine al be ga .r n).2.1)
      6 (4 * ((be:ℚ) + ga - 2 * al)) (by norm_num)
      (by norm_num [spine, base]) (by norm_num [spine, base, step])
      (by norm_num [spine, base, step])
      (fun n => (spine_recurrence_r al be ga n).1)
      (fun n => (spine_recurrence_r al be ga n).2) hh
    linarith [hnr n]
  constructor
  · exact_mod_cast (show (al:ℚ) + be ≤ 2 * ga by linarith)
  · exact_mod_cast (show 2 * (al:ℚ) ≤ be + ga by linarith)

private theorem region_chart (al be ga : ℕ) (hne : (al, be, ga) ≠ (0, 0, 0)) :
    (0 < ga ∧ ((al:ℚ) / ga, (be:ℚ) / ga) ∈ quadrilateral) ↔
      al + be ≤ 2 * ga ∧ 2 * al ≤ be + ga := by
  constructor
  · rintro ⟨hg, hq⟩
    have hgq : (0:ℚ) < ga := Rat.natCast_pos.mpr hg
    have h := (quadrilateral_region _).mp hq
    rcases h with ⟨_, _, h1, h2⟩
    have h1' : (al:ℚ) + be ≤ 2 * ga := by
      rw [← add_div] at h1
      exact (div_le_iff₀ hgq).mp h1
    have h2' : 2 * (al:ℚ) ≤ be + ga := by
      rw [← mul_div_assoc, ← div_self (ne_of_gt hgq), ← add_div] at h2
      exact (div_le_div_iff_of_pos_right hgq).mp h2
    exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
  · rintro ⟨h1, h2⟩
    have hg : 0 < ga := by
      by_contra hh
      have hgz : ga = 0 := Nat.eq_zero_of_not_pos hh
      have hal : al = 0 := by omega
      have hbe : be = 0 := by omega
      exact hne (by simp [hgz, hal, hbe])
    have hgq : (0:ℚ) < ga := Rat.natCast_pos.mpr hg
    have h1q : (al:ℚ) + be ≤ 2 * ga := by exact_mod_cast h1
    have h2q : 2 * (al:ℚ) ≤ be + ga := by exact_mod_cast h2
    refine ⟨hg, (quadrilateral_region _).mpr ⟨by positivity, by positivity, ?_, ?_⟩⟩
    · change (al:ℚ) / ga + be / ga ≤ 2
      rw [← add_div]
      exact (div_le_iff₀ hgq).mpr h1q
    · change 2 * ((al:ℚ) / ga) ≤ be / ga + 1
      rw [← mul_div_assoc, ← div_self (ne_of_gt hgq), ← add_div]
      exact (div_le_div_iff_of_pos_right hgq).mpr h2q

theorem result : claim := by
  intro al be ga hne
  rw [region_chart al be ga hne]
  exact ⟨necessary al be ga, fun h => sufficient al be ga h.1 h.2⟩

end D5.S3.Factorization.BoninShadowMarkoffPositivity
