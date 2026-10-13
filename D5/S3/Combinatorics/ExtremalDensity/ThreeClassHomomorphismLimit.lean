/- GID: D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: Three-class graph homomorphism densities equal their finite weighting sum. -/

/-
admission_basis: escape-witness
Direct dependencies frozen on the protected base: none.
DTR reading: DTR-Unregistered (Observe) for every public theorem in this module.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15978.
Both public theorems are audit targets under utility: none. The full real-coordinate and
unbounded finite-graph readouts lack source reconstruction, variation, sensitivity and
observational-dependence evidence for the enrolled DependentFamily template.
The collision estimate excludes equal images only on edges, using v^2*n^(v-1).
Definitions are bind-only encodings consumed by the named mathematical steps.
classAllowed_iff: proof_shape: bind-only; escape_witness: none; consumers: hom_admissible,
bad_collision.
weights_valid: proof_shape: bind-only; escape_witness: none; consumers: classSum_bound,
classSize_ratio_limit, weights_edge_density, fCoord_low_bound, density_h3.
floor_ratio_limit: proof_shape: bind-only; escape_witness: none; consumers:
classSize_ratio_limit.
classSum_bound: proof_shape: bind-only; escape_witness: none; consumers: classSize_yellow,
classSize_red, classSize_blue, classSize_ratio_limit.
classSize_yellow: proof_shape: bind-only; escape_witness: none; consumers:
classSize_ratio_limit.
classSize_red: proof_shape: bind-only; escape_witness: none; consumers: classSize_ratio_limit.
classSize_blue: proof_shape: bind-only; escape_witness: none; consumers: classSize_ratio_limit.
classSize_ratio_limit: proof_shape: bind-only; escape_witness: none; consumers:
idealCount_ratio_limit.
colourFibre_card: proof_shape: bind-only; escape_witness: none; consumers: idealCount_split.
idealCount_split: proof_shape: bind-only; escape_witness: none; consumers:
idealCount_ratio_limit.
collision_card_bound: proof_shape: content; escape_witness: collision_card_bound; consumers:
bad_count_bound.
hom_admissible: proof_shape: bind-only; escape_witness: none; consumers:
idealCount_homCount_diff.
bad_collision: proof_shape: bind-only; escape_witness: none; consumers: bad_count_bound.
bad_count_bound: proof_shape: content; escape_witness: bad_count_bound; consumers:
idealCount_homCount_diff.
idealCount_homCount_diff: proof_shape: content; escape_witness: bad_count_bound; consumers:
counting_limit.
idealCount_ratio_limit: proof_shape: bind-only; escape_witness: none; consumers: counting_limit.
collision_error_limit: proof_shape: bind-only; escape_witness: none; consumers: counting_limit.
counting_limit: proof_shape: content; escape_witness: bad_count_bound; consumers:
tDens_eq_weightingSum.
tDens_eq_weightingSum: proof_shape: content; escape_witness: bad_count_bound; consumers:
density_h3.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field

noncomputable section
open Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit
attribute [local instance] Classical.propDecidable

def yW (beta q : ℝ) : ℝ := Real.sqrt beta * q
def rW (beta q : ℝ) : ℝ := 1 - Real.sqrt (1 - beta * (1 - q ^ 2))
def bW (beta q : ℝ) : ℝ :=
  Real.sqrt (1 - beta * (1 - q ^ 2)) - Real.sqrt beta * q

def vertexClass (beta q : ℝ) (n : ℕ) (i : Fin n) : Fin 3 :=
  if i.val < ⌊yW beta q * n⌋₊ then 1
  else if i.val < ⌊yW beta q * n⌋₊ + ⌊rW beta q * n⌋₊ then 0 else 2

def classAllowed (a b : Fin 3) : Prop :=
  (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 0) ∨ a = 0 ∨ b = 0

def tGraph (beta q : ℝ) (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ classAllowed (vertexClass beta q n i) (vertexClass beta q n j)
  symm := ⟨by
    intro i j h
    rcases h with ⟨hne,h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl ⟨h.2,h.1⟩
    · exact Or.inr (Or.inl ⟨h.2,h.1⟩)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

def homCount {v n : ℕ} (G : SimpleGraph (Fin v)) (H : SimpleGraph (Fin n)) : ℕ :=
  Nat.card {f : Fin v → Fin n // ∀ i j, G.Adj i j → H.Adj (f i) (f j)}

def tDens {v : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ) : ℝ :=
  limUnder Filter.atTop (fun n : ℕ => (homCount G (tGraph beta q n) : ℝ) / (n : ℝ)^v)

def colourWeight (beta q : ℝ) (a : Fin 3) : ℝ :=
  if a = 0 then rW beta q else if a = 1 then yW beta q else bW beta q

def independentWeight (a : Fin 3) : ℝ := (a.val : ℝ) / 2

def admissible {v : ℕ} (G : SimpleGraph (Fin v)) (c : Fin v → Fin 3) : Prop :=
  ∀ i j, G.Adj i j → independentWeight (c i) + independentWeight (c j) ≤ 1

def weightingSum {v : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ) : ℝ :=
  by
    classical
    exact ∑ c : Fin v → Fin 3, if admissible G c then ∏ i, colourWeight beta q (c i) else 0

private theorem classAllowed_iff (a b : Fin 3) :
    classAllowed a b ↔ independentWeight a + independentWeight b ≤ 1 := by
  fin_cases a <;> fin_cases b <;> norm_num [classAllowed, independentWeight]

theorem weights_valid (beta q : ℝ) (hb : beta ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    0 ≤ yW beta q ∧ 0 ≤ rW beta q ∧ 0 ≤ bW beta q ∧
    yW beta q + rW beta q + bW beta q = 1 := by
  have hq2 : q^2 ≤ 1 := by nlinarith [hq.1,hq.2]
  have hd : 0 ≤ 1 - beta * (1-q^2) := by nlinarith [hb.2,sq_nonneg q]
  have hd1 : 1 - beta * (1-q^2) ≤ 1 := by nlinarith [hb.1]
  have hs := Real.sq_sqrt hb.1
  have hy : 0 ≤ yW beta q := mul_nonneg (Real.sqrt_nonneg _) hq.1
  refine ⟨hy, ?_, ?_, ?_⟩
  · dsimp [rW]
    have ht : Real.sqrt (1-beta*(1-q^2)) ≤ 1 := by
      exact (Real.sqrt_le_one).mpr hd1
    linarith
  · dsimp [bW]
    have h2 : (Real.sqrt beta * q)^2 ≤ 1-beta*(1-q^2) := by
      rw [mul_pow,hs]
      nlinarith [hb.2]
    exact sub_nonneg.mpr ((Real.le_sqrt (by exact hy) hd).mpr h2)
  · dsimp [yW,rW,bW]; ring

private theorem floor_ratio_limit (w : ℝ) (hw : 0 ≤ w) :
    Tendsto (fun n : ℕ => (⌊w*(n : ℝ)⌋₊ : ℝ)/(n : ℝ)) atTop (𝓝 w) := by
  exact (tendsto_nat_floor_mul_div_atTop hw).comp tendsto_natCast_atTop_atTop

private def classSize (beta q : ℝ) (n : ℕ) (a : Fin 3) : ℕ :=
  Nat.card {i : Fin n // vertexClass beta q n i = a}

private theorem classSum_bound (beta q : ℝ) (n : ℕ)
    (hb : beta ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    ⌊yW beta q * n⌋₊ + ⌊rW beta q * n⌋₊ ≤ n := by
  obtain ⟨hy,hr,hb0,hs⟩ := weights_valid beta q hb hq
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hf := add_le_add (Nat.floor_le (mul_nonneg hy hn)) (Nat.floor_le (mul_nonneg hr hn))
  have ht : yW beta q * n + rW beta q * n ≤ (n : ℝ) := by nlinarith [mul_nonneg hb0 hn]
  exact_mod_cast (hf.trans ht)

private theorem classSize_yellow (beta q : ℝ) (n : ℕ)
    (hb : beta ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    classSize beta q n 1 = ⌊yW beta q * n⌋₊ := by
  classical
  let Y := ⌊yW beta q * n⌋₊
  have hYn : Y ≤ n := (Nat.le_add_right _ _).trans (classSum_bound beta q n hb hq)
  have hclass (i : Fin n) : vertexClass beta q n i = 1 ↔ i.val < Y := by
    dsimp [vertexClass, Y]
    split_ifs <;> norm_num [Fin.ext_iff] <;> omega
  rw [classSize, Nat.card_congr (Equiv.subtypeEquivRight hclass), Nat.card_eq_fintype_card]
  exact Fintype.card_fin_lt_of_le hYn

private theorem classSize_red (beta q : ℝ) (n : ℕ)
    (hb : beta ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    classSize beta q n 0 = ⌊rW beta q * n⌋₊ := by
  classical
  let Y := ⌊yW beta q * n⌋₊
  let R := ⌊rW beta q * n⌋₊
  have hYR : Y + R ≤ n := classSum_bound beta q n hb hq
  let A : Finset (Fin n) := univ.filter (fun i => i.val < Y + R)
  let B : Finset (Fin n) := univ.filter (fun i => i.val < Y)
  have hBA : B ⊆ A := by
    intro i hi
    simp only [A, B, mem_filter, mem_univ, true_and] at hi ⊢
    omega
  have hA : A.card = Y + R := by
    rw [show A = univ.filter (fun i => i.val < Y + R) from rfl,
      ← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le hYR
  have hB : B.card = Y := by
    rw [show B = univ.filter (fun i => i.val < Y) from rfl,
      ← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le (by omega)
  have hclass (i : Fin n) : vertexClass beta q n i = 0 ↔ i ∈ A \ B := by
    simp only [A, B, mem_sdiff, mem_filter, mem_univ, true_and]
    dsimp [vertexClass, Y, R]
    split_ifs <;> norm_num [Fin.ext_iff] <;> omega
  rw [classSize, Nat.card_congr (Equiv.subtypeEquivRight hclass), Nat.card_eq_fintype_card,
    Fintype.card_coe, card_sdiff_of_subset hBA, hA, hB]
  dsimp [Y, R]
  omega

private theorem classSize_blue (beta q : ℝ) (n : ℕ)
    (hb : beta ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    classSize beta q n 2 = n - (⌊yW beta q * n⌋₊ + ⌊rW beta q * n⌋₊) := by
  classical
  let Y := ⌊yW beta q * n⌋₊
  let R := ⌊rW beta q * n⌋₊
  have hYR : Y + R ≤ n := classSum_bound beta q n hb hq
  have hclass (i : Fin n) : vertexClass beta q n i = 2 ↔ ¬ i.val < Y + R := by
    dsimp [vertexClass, Y, R]
    split_ifs <;> norm_num [Fin.ext_iff] <;> omega
  rw [classSize, Nat.card_congr (Equiv.subtypeEquivRight hclass), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_fin_lt_of_le hYR]

private theorem classSize_ratio_limit (beta q : ℝ)
    (hb : beta ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) (a : Fin 3) :
    Tendsto (fun n : ℕ => (classSize beta q n a : ℝ) / n) atTop
      (𝓝 (colourWeight beta q a)) := by
  obtain ⟨hy,hr,hb0,hs⟩ := weights_valid beta q hb hq
  have hY := floor_ratio_limit (yW beta q) hy
  have hR := floor_ratio_limit (rW beta q) hr
  fin_cases a
  · simpa [colourWeight,classSize_red beta q _ hb hq] using hR
  · simpa [colourWeight,classSize_yellow beta q _ hb hq] using hY
  · have hB := ((tendsto_const_nhds (x := (1 : ℝ))).sub hY).sub hR
    have hs' : 1-yW beta q-rW beta q = bW beta q := by linarith
    rw [hs'] at hB
    apply hB.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    change 1 - (⌊yW beta q * n⌋₊ : ℝ)/n - (⌊rW beta q * n⌋₊ : ℝ)/n = (classSize beta q n 2 : ℝ)/n
    rw [classSize_blue beta q n hb hq,Nat.cast_sub (classSum_bound beta q n hb hq),Nat.cast_add]
    field_simp [hn0]; ring

private theorem colourFibre_card {v n : ℕ} (cls : Fin n → Fin 3) (c : Fin v → Fin 3) :
    Nat.card ({f : Fin v → Fin n // ∀ i, cls (f i) = c i}) = ∏ i, Nat.card {a : Fin n // cls a = c i} := by
  classical
  exact (Nat.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin v => Fin n)
    (p := fun i a => cls a = c i))).trans Nat.card_pi

private def idealCount {v n : ℕ} (G : SimpleGraph (Fin v)) (cls : Fin n → Fin 3) : ℕ :=
  Nat.card {f : Fin v → Fin n // admissible G (cls ∘ f)}

private theorem idealCount_split {v n : ℕ} (G : SimpleGraph (Fin v)) (cls : Fin n → Fin 3) :
    idealCount G cls = ∑ c : Fin v → Fin 3,
      if admissible G c then ∏ i, Nat.card {a : Fin n // cls a = c i} else 0 := by
  classical
  let e : {f : Fin v → Fin n // admissible G (cls ∘ f)} ≃
      (Σ c : {c : Fin v → Fin 3 // admissible G c}, {f : Fin v → Fin n // ∀ i, cls (f i) = c.val i}) :=
    { toFun := fun f => ⟨⟨cls ∘ f.val, f.property⟩,⟨f.val,fun i => rfl⟩⟩
      invFun := fun p => ⟨p.2.val, by
        have h : cls ∘ p.2.val = p.1.val := funext p.2.property
        rw [h]; exact p.1.property⟩
      left_inv := by intro f; rfl
      right_inv := by
        intro p
        rcases p with ⟨⟨c,hc⟩,⟨f,hf⟩⟩
        have heq : cls ∘ f = c := funext hf
        subst c
        rfl }
  rw [idealCount,Nat.card_congr e,Nat.card_sigma]
  simp_rw [colourFibre_card]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := admissible G) (Finset.univ.filter (admissible G)) (by intro x; simp) (fun c => ∏ i, Nat.card {a : Fin n // cls a = c i})).symm

private theorem collision_card_bound {v n : ℕ} (i j : Fin v) (hij : i ≠ j) :
    Nat.card {f : Fin v → Fin n // f i = f j} ≤ n^(v-1) := by
  classical
  let restrict : {f : Fin v → Fin n // f i = f j} → ({k : Fin v // k ≠ j} → Fin n) :=
    fun f k => f.val k.val
  have hr : Function.Injective restrict := by
    intro f g heq
    apply Subtype.ext
    funext k
    by_cases hk : k = j
    · subst k
      have hi : f.val i = g.val i := congrFun heq ⟨i,hij⟩
      exact f.property.symm.trans (hi.trans g.property)
    · exact congrFun heq ⟨k,hk⟩
  have hc : Nat.card {k : Fin v // k ≠ j} = v-1 := by
    rw [Nat.card_eq_fintype_card]
    simpa using (Fintype.card_subtype_compl (fun k : Fin v => k = j))
  calc
    _ ≤ Nat.card ({k : Fin v // k ≠ j} → Fin n) := Nat.card_le_card_of_injective restrict hr
    _ = n^(v-1) := by rw [Nat.card_fun,Nat.card_fin,hc]

private def homPredicate {v n : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ) (f : Fin v → Fin n) : Prop :=
  ∀ i j, G.Adj i j → (tGraph beta q n).Adj (f i) (f j)

private theorem hom_admissible {v n : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ)
    (f : Fin v → Fin n) (hf : homPredicate G beta q f) :
    admissible G (vertexClass beta q n ∘ f) := by
  intro i j hG
  exact (classAllowed_iff _ _).mp (hf i j hG).2

private def badPredicate {v n : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ) (f : Fin v → Fin n) : Prop :=
  admissible G (vertexClass beta q n ∘ f) ∧ ¬ homPredicate G beta q f

private theorem bad_collision {v n : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ)
    (f : Fin v → Fin n) (hf : badPredicate G beta q f) :
    ∃ i j, G.Adj i j ∧ f i = f j := by
  by_contra h
  push Not at h
  apply hf.2
  intro i j hG
  exact ⟨h i j hG,(classAllowed_iff _ _).mpr (hf.1 i j hG)⟩

private theorem bad_count_bound {v n : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ) :
    Nat.card {f : Fin v → Fin n // badPredicate G beta q f} ≤ v^2*n^(v-1) := by
  classical
  let Bad := {f : Fin v → Fin n // badPredicate G beta q f}
  choose I J hAdj hEq using (fun f : Bad => bad_collision G beta q f.val f.property)
  let encode : Bad → (Σ e : {p : Fin v × Fin v // G.Adj p.1 p.2},
      {f : Fin v → Fin n // f e.val.1 = f e.val.2}) :=
    fun f => ⟨⟨(I f,J f),hAdj f⟩,⟨f.val,hEq f⟩⟩
  have hinj : Function.Injective encode := by
    intro f g h
    apply Subtype.ext
    exact congrArg (fun p => p.2.val) h
  have hcard : Nat.card {p : Fin v × Fin v // G.Adj p.1 p.2} ≤ v^2 := by
    rw [Nat.card_eq_fintype_card]
    simpa [pow_two] using Fintype.card_subtype_le (fun p : Fin v × Fin v => G.Adj p.1 p.2)
  calc
    _ ≤ Nat.card (Σ e : {p : Fin v × Fin v // G.Adj p.1 p.2},
      {f : Fin v → Fin n // f e.val.1 = f e.val.2}) := Nat.card_le_card_of_injective encode hinj
    _ = ∑ e : {p : Fin v × Fin v // G.Adj p.1 p.2},
      Nat.card {f : Fin v → Fin n // f e.val.1 = f e.val.2} := Nat.card_sigma
    _ ≤ ∑ _e : {p : Fin v × Fin v // G.Adj p.1 p.2}, n^(v-1) :=
      Finset.sum_le_sum fun e _ => collision_card_bound _ _ e.property.ne
    _ = Nat.card {p : Fin v × Fin v // G.Adj p.1 p.2} * n^(v-1) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ v^2*n^(v-1) := Nat.mul_le_mul_right _ hcard

private theorem idealCount_homCount_diff {v n : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ) :
    homCount G (tGraph beta q n) ≤ idealCount G (vertexClass beta q n) ∧
    idealCount G (vertexClass beta q n) - homCount G (tGraph beta q n) ≤ v^2*n^(v-1) := by
  classical
  let A := (Finset.univ : Finset (Fin v → Fin n)).filter
    (fun f => admissible G (vertexClass beta q n ∘ f))
  let H := (Finset.univ : Finset (Fin v → Fin n)).filter (homPredicate G beta q)
  have hHA : H ⊆ A := by
    intro f hf
    simp only [H,Finset.mem_filter,Finset.mem_univ,true_and] at hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hom_admissible G beta q f hf⟩
  have hHC : H.card = homCount G (tGraph beta q n) := by
    rw [homCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
    congr 1
    ext f
    simp [H,homPredicate]
  have hAC : A.card = idealCount G (vertexClass beta q n) := by
    simp [A,idealCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hBC : (A \ H).card = Nat.card {f : Fin v → Fin n // badPredicate G beta q f} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    congr 1
    ext f
    simp only [A, H, Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, true_and]
    rfl
  refine ⟨by rw [←hHC,←hAC];exact Finset.card_le_card hHA, ?_⟩
  rw [←hAC,←hHC,←Finset.card_sdiff_of_subset hHA,hBC]
  exact bad_count_bound G beta q

private theorem idealCount_ratio_limit {v : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ)
    (hb : beta ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    Tendsto (fun n : ℕ => (idealCount G (vertexClass beta q n) : ℝ)/(n : ℝ)^v)
      atTop (𝓝 (weightingSum G beta q)) := by
  classical
  have heq (n : ℕ) : (idealCount G (vertexClass beta q n) : ℝ)/(n : ℝ)^v =
      ∑ c : Fin v → Fin 3, if admissible G c then
        ∏ i, (classSize beta q n (c i) : ℝ)/(n : ℝ) else 0 := by
    rw [idealCount_split,Nat.cast_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : admissible G c
    · simp only [hc,if_pos,Nat.cast_prod,classSize]
      rw [Finset.prod_div_distrib]
      simp
    · simp [hc]
  simp_rw [heq]
  unfold weightingSum
  apply tendsto_finsetSum
  intro c _
  by_cases hc : admissible G c
  · simp only [hc,if_pos]
    apply tendsto_finsetProd
    intro i _
    exact classSize_ratio_limit beta q hb hq (c i)
  · simp only [hc,if_neg]
    exact tendsto_const_nhds

private theorem collision_error_limit (v : ℕ) :
    Tendsto (fun n : ℕ => ((v : ℝ)^2*(n : ℝ)^(v-1))/(n : ℝ)^v)
      atTop (𝓝 (0 : ℝ)) := by
  cases v with
  | zero => simp
  | succ v =>
    have h := (tendsto_const_nhds (x := ((v+1 : ℕ) : ℝ)^2)).mul
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [Nat.add_sub_cancel,pow_succ]
    field_simp

private theorem counting_limit {v : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ)
    (hb : beta ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    Tendsto (fun n : ℕ => (homCount G (tGraph beta q n) : ℝ)/(n : ℝ)^v)
      atTop (𝓝 (weightingSum G beta q)) := by
  classical
  have hI := idealCount_ratio_limit G beta q hb hq
  have hE := collision_error_limit v
  have hL := hI.sub hE
  simp only [sub_zero] at hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hI ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hnvp : 0 < (n : ℝ)^v := pow_pos hnpos _
    obtain ⟨hle,hbd⟩ := idealCount_homCount_diff G beta q (n := n)
    have hbdr : ((idealCount G (vertexClass beta q n) - homCount G (tGraph beta q n) : ℕ) : ℝ)
        ≤ (v : ℝ)^2*(n : ℝ)^(v-1) := by exact_mod_cast hbd
    rw [Nat.cast_sub hle] at hbdr
    have hh := div_le_div_of_nonneg_right hbdr hnvp.le
    rw [sub_div] at hh
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hle := (idealCount_homCount_diff G beta q (n := n)).1
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (pow_nonneg hnpos.le _)

theorem tDens_eq_weightingSum {v : ℕ} (G : SimpleGraph (Fin v)) (beta q : ℝ)
    (hb : beta ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    tDens G beta q = weightingSum G beta q :=
  (counting_limit G beta q hb hq).limUnder_eq

end D5.S3.Combinatorics.ExtremalDensity.ThreeClassHomomorphismLimit
