/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Universal empty-fibre kernels admit fixed occupied blocks with coherent positive signs. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-! Occupied-fibre components constrain the support of the signed empty-boundary kernel. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators Matrix

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositivePairedKernel

section Gram

variable {ι ρ ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [Fintype ε]

private theorem gram_kernel_iff (E : Matrix ε ι ℝ) (f : ι → ℝ) :
    (Eᵀ * E) *ᵥ f = 0 ↔ E *ᵥ f = 0 := by
  simp only [← Matrix.mulVecLin_apply, ← LinearMap.mem_ker,
    Matrix.ker_mulVecLin_transpose_mul_self]

private theorem gram_form (E : Matrix ε ι ℝ) (f : ι → ℝ) :
    f ⬝ᵥ ((Eᵀ * E) *ᵥ f) = ∑ y, (E *ᵥ f) y ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [Matrix.transpose_transpose, dotProduct, pow_two]

/-- Absolute values preserve the kernel after the column signs have made the occupied
matrix entrywise nonnegative. No irreducibility or contact bound is needed. -/
theorem abs_mem_kernel {O : Matrix ρ ι ℝ} {E : Matrix ε ι ℝ} {c : ℝ}
    (hGram : Oᵀ * O + Eᵀ * E = c • (1 : Matrix ι ι ℝ))
    (hO : ∀ r x, 0 ≤ O r x) {f : ι → ℝ} (hf : E *ᵥ f = 0) :
    E *ᵥ (fun x => |f x|) = 0 := by
  let u : ι → ℝ := fun x => |f x|
  let A := Oᵀ * O
  have hA (x y : ι) : 0 ≤ A x y := by
    simp only [A, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hO r x) (hO r y)
  have hNorm : u ⬝ᵥ u = f ⬝ᵥ f := by
    simp only [dotProduct, u, abs_mul_abs_self]
  have hOcc : f ⬝ᵥ (A *ᵥ f) ≤ u ⬝ᵥ (A *ᵥ u) := by
    simp only [Matrix.dot_mulVec_eq_sum_sum]
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    simpa only [u, abs_mul, abs_of_nonneg (hA y x)] using
      le_abs_self (f y * A y x * f x)
  have hD : Eᵀ * E = c • (1 : Matrix ι ι ℝ) - A := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact hGram
  have hle : u ⬝ᵥ ((Eᵀ * E) *ᵥ u) ≤ f ⬝ᵥ ((Eᵀ * E) *ᵥ f) := by
    simp only [hD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, hNorm]
    exact sub_le_sub_left hOcc _
  have hsum : (∑ r, (E *ᵥ u) r ^ 2) ≤ 0 := by
    rw [← gram_form E u]
    simpa only [← Matrix.mulVec_mulVec, hf, Matrix.mulVec_zero, dotProduct_zero] using hle
  have hzero := le_antisymm hsum (Finset.sum_nonneg fun r _ => sq_nonneg ((E *ᵥ u) r))
  funext r
  have hr := (Finset.sum_eq_zero_iff_of_nonneg
    (fun r _ => sq_nonneg ((E *ᵥ u) r))).mp hzero r (Finset.mem_univ r)
  exact eq_zero_of_pow_eq_zero hr

/-- Sharing an occupied row gives an undirected graph on the columns. -/
def occupiedGraph (contact : ρ → ι → Prop) : SimpleGraph ι where
  Adj x y := x ≠ y ∧ ∃ r, contact r x ∧ contact r y
  symm := by
    constructor
    rintro x y ⟨hne, r, hx, hy⟩
    exact ⟨hne.symm, r, hy, hx⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

/-- On each occupied component, a nonnegative empty-kernel vector is either
positive everywhere or zero everywhere. The underlying signed vector has
the same zero set by the absolute-value theorem. -/
theorem zero_iff_of_reachable {O : Matrix ρ ι ℝ} {E : Matrix ε ι ℝ} {c : ℝ}
    (hGram : Oᵀ * O + Eᵀ * E = c • (1 : Matrix ι ι ℝ))
    (hO : ∀ r x, 0 ≤ O r x) {f : ι → ℝ} (hf : E *ᵥ f = 0) {x y : ι}
    (hxy : (occupiedGraph (fun r x => 0 < O r x)).Reachable x y) :
    f x = 0 ↔ f y = 0 := by
  let u : ι → ℝ := fun x => |f x|
  let A := Oᵀ * O
  have hu : E *ᵥ u = 0 := abs_mem_kernel hGram hO hf
  have heigen : A *ᵥ u = c • u := by
    have he := congrArg (fun M : Matrix ι ι ℝ => M *ᵥ u) hGram
    have heE : (Eᵀ * E) *ᵥ u = 0 := (gram_kernel_iff E u).2 hu
    rw [Matrix.add_mulVec, heE, add_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at he
    exact he
  have hn (p q : ι) : 0 ≤ A p q := by
    simp only [A, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hO r p) (hO r q)
  let G := occupiedGraph (fun r x => 0 < O r x)
  have step {p q : ι} (hpq : G.Adj p q) (hp : u p = 0) : u q = 0 := by
    obtain ⟨_, r, hrp, hrq⟩ := hpq
    have hpos : 0 < A p q := by
      change 0 < ∑ z, O z p * O z q
      exact (mul_pos hrp hrq).trans_le
        (Finset.single_le_sum (fun z _ => mul_nonneg (hO z p) (hO z q)) (Finset.mem_univ r))
    have hrow : (∑ z, A p z * u z) = 0 := by
      simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hp, mul_zero]
        using congrFun heigen p
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => mul_nonneg (hn p z) (abs_nonneg (f z)))).mp hrow q (Finset.mem_univ q)
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos)
  have along {p q : ι} (h : G.Reachable p q) : u p = 0 → u q = 0 := by
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact id
    | cons h₁ _ ih => exact fun hp => ih (step h₁ hp)
  exact ⟨fun hx => abs_eq_zero.mp (along hxy (abs_eq_zero.mpr hx)),
    fun hy => abs_eq_zero.mp (along hxy.symm (abs_eq_zero.mpr hy))⟩

private theorem complement_block {O : Matrix ρ ι ℝ} {E : Matrix ε ι ℝ} {c : ℝ}
    (hGram : Oᵀ * O + Eᵀ * E = c • (1 : Matrix ι ι ℝ))
    {x y : ι} (hne : x ≠ y) (hO : (Oᵀ * O) x y = 0) : (Eᵀ * E) x y = 0 := by
  have he := congrFun (congrFun hGram x) y
  simpa only [Matrix.add_apply, hO, zero_add, Matrix.smul_apply,
    Matrix.one_apply_ne hne, smul_zero] using he

/-- Every block of the occupied Gram can be cut out of an arbitrary empty-kernel vector.
The summands of the empty boundary may overlap between blocks. -/
theorem restrict_mem_kernel {O : Matrix ρ ι ℝ} {E : Matrix ε ι ℝ} {c : ℝ}
    (hGram : Oᵀ * O + Eᵀ * E = c • (1 : Matrix ι ι ℝ))
    {β : Type*} [DecidableEq β] (tag : ι → β)
    (hBlock : ∀ x y, tag x ≠ tag y → (Oᵀ * O) x y = 0)
    {f : ι → ℝ} (hf : E *ᵥ f = 0) (k : β) :
    E *ᵥ (fun x => if tag x = k then f x else 0) = 0 := by
  let D := Eᵀ * E
  have hD (x y : ι) (hxy : tag x ≠ tag y) : D x y = 0 := by
    exact complement_block hGram (fun h => hxy (congrArg tag h)) (hBlock x y hxy)
  apply (gram_kernel_iff E _).mp
  have hDf := (gram_kernel_iff E f).mpr hf
  funext x
  by_cases hx : tag x = k
  · calc
      (D *ᵥ (fun y => if tag y = k then f y else 0)) x = (D *ᵥ f) x := by
        simp only [Matrix.mulVec, dotProduct]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : tag y = k
        · rw [if_pos hy]
        · rw [if_neg hy, hD x y (fun h => hy (h.symm.trans hx)), zero_mul, zero_mul]
      _ = 0 := congrFun hDf x
  · change (∑ y, D x y * (if tag y = k then f y else 0)) = 0
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : tag y = k
    · rw [hD x y (fun h => hx (h.trans hy)), zero_mul]
    · rw [if_neg hy, mul_zero]

end Gram

section Cube

open BalancedCriticalSpectrum (Q flip flip_adj flip_flip IsSwitching switching_sq)
open BalancedCubeComponentBoundary (flip_injective)
open BalancedCubeGirth (flip_comm adjacent_exists_flip)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open CoordinateHalves.Q9DominantAxisBoundary (PairedRows EmptyExterior emptyFibreBoundary)
open Q9IsotropicHuang (flipSign parity)
open Q9WeightedBoundaryGram (signed signed_transpose)
open private signed_square from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private edge edge_sq edge_curvature from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private transverseBoundary boundaryOver eval_gram_det gram_det_eq_zero_iff
  boundary_gram_eq_signed_defect from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9DominantAxisBoundary

attribute [local instance] Classical.propDecidable

variable {C : Finset (Q 9)} {b : Bool} {i : Fin 9}

/-- The retained lift of a paired column. -/
abbrev pairedVertex (x : PairedRows C b i) : Q 9 := x.1.1.1

private theorem vertex_injective : Function.Injective (pairedVertex (C := C) (b := b) (i := i)) :=
  fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext h))

private theorem vertex_parity (x : PairedRows C b i) : parity (pairedVertex x) = b :=
  (Finset.mem_filter.mp x.1.property).2

private def occupied (C : Finset (Q 9)) (i : Fin 9) (r : Q 9) : Prop :=
  r ∈ C ∨ flip r i ∈ C

/-- A transverse contact from an occupied projected fibre to a paired column.
Each transverse edge stays in its axial layer, where deleting the axis gives Q8. -/
def occupiedContact (C : Finset (Q 9)) (b : Bool) (i : Fin 9)
    (r : Q 9) (x : PairedRows C b i) : Prop :=
  occupied C i r ∧ ∃ a, a ≠ i ∧ flip r a = pairedVertex x

/-- Delete the chosen coordinate and retain the order of the other eight. -/
abbrev dropAxis (i : Fin 9) (r : Q 9) : Q 8 :=
  Fin.removeNth (α := fun _ => Bool) i r

/-- In one axial layer, occupied contacts are exactly the actual Q8 adjacencies
from projected occupied fibres to projected paired columns. -/
theorem occupiedContact_iff_projected_adj (r : Q 9) (x : PairedRows C b i) :
    occupiedContact C b i r x ↔
      (r ∈ C ∨ flip r i ∈ C) ∧ r i = pairedVertex x i ∧
        (hypercube 8).Adj (dropAxis i r) (dropAxis i (pairedVertex x)) := by
  have hkeep (a : Fin 8) : dropAxis i (flip r (i.succAbove a)) = flip (dropAxis i r) a :=
    Fin.removeNth_update_succAbove (α := fun _ => Bool) i a (!r (i.succAbove a)) r
  have hbit (a : Fin 8) : flip r (i.succAbove a) i = r i := by
    simp only [BalancedCriticalSpectrum.flip, Function.update_of_ne (Fin.ne_succAbove i a)]
  constructor
  · rintro ⟨hr, a, ha, he⟩
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
    refine ⟨hr, ?_, ?_⟩
    · rw [← he, hbit]
    · rw [← he, hkeep]
      exact flip_adj _ _
  · rintro ⟨hr, hb, he⟩
    obtain ⟨j, hj⟩ := adjacent_exists_flip he
    refine ⟨hr, i.succAbove j, Fin.succAbove_ne _ _, ?_⟩
    have h := congrArg₂ (Fin.insertNth (α := fun _ => Bool) i)
      ((hbit j).trans hb) ((hkeep j).trans hj.symm)
    simpa only [dropAxis, Fin.insertNth_self_removeNth] using h

/-- The occupied-row graph in Q8 layers, indexed by the actual paired Q9 columns. -/
def pairedGraph (C : Finset (Q 9)) (b : Bool) (i : Fin 9) : SimpleGraph (PairedRows C b i) :=
  occupiedGraph (occupiedContact C b i)

private def rowSign (C : Finset (Q 9)) (i : Fin 9) (σ : Q 9 → ℝ) (r : Q 9) : ℝ :=
  if r ∈ C then σ r else -edge r i * σ (flip r i)

private theorem rowSign_sq {σ : Q 9 → ℝ} (hs : IsSwitching C σ) {r : Q 9}
    (hr : occupied C i r) : rowSign C i σ r ^ 2 = 1 := by
  by_cases h : r ∈ C
  · rw [rowSign, if_pos h, switching_sq hs h]
  · rw [rowSign, if_neg h, mul_pow, neg_sq, edge_sq,
      switching_sq hs (hr.resolve_left h), one_mul]

/-- On the other layer of a single fibre the sign is forced by the Huang
product around the square formed by the axis and the transverse edge. -/
private theorem coherent_transverse_edge {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {r : Q 9} {x : PairedRows C b i} {a : Fin 9} (hr : occupied C i r)
    (hai : a ≠ i) (ha : flip r a = pairedVertex x) :
    edge r a * σ (pairedVertex x) = rowSign C i σ r := by
  have hx : pairedVertex x ∈ C := x.1.1.property
  have hx' : flip (pairedVertex x) i ∈ C := x.property
  by_cases h : r ∈ C
  · rw [rowSign, if_pos h]
    have he : edge r a = σ r * σ (pairedVertex x) := by
      simpa only [edge, ha] using hs.2 r h (flip r a) (ha.symm ▸ hx) (flip_adj r a)
    calc
      edge r a * σ (pairedVertex x) = σ r * σ (pairedVertex x) ^ 2 := by rw [he]; ring
      _ = σ r := by rw [switching_sq hs hx, mul_one]
  · rw [rowSign, if_neg h]
    have hr' : flip r i ∈ C := hr.resolve_left h
    have hflip : flip (flip r i) a = flip (pairedVertex x) i := by
      rw [flip_comm r i a, ha]
    have he : edge (pairedVertex x) i = σ (pairedVertex x) * σ (flip (pairedVertex x) i) :=
      hs.2 _ hx _ hx' (flip_adj _ _)
    have hd : edge (flip r i) a = σ (flip r i) * σ (flip (pairedVertex x) i) := by
      simpa only [edge, hflip] using
        hs.2 (flip r i) hr' (flip (flip r i) a) (hflip.symm ▸ hx') (flip_adj _ _)
    have hcurv : edge r a * edge (pairedVertex x) i = -(edge r i * edge (flip r i) a) := by
      simpa only [ha] using edge_curvature r hai
    have hsq := switching_sq hs hx'
    calc
      edge r a * σ (pairedVertex x) =
          (edge r a * (σ (pairedVertex x) * σ (flip (pairedVertex x) i))) * σ (flip (pairedVertex x) i) := by
        symm
        calc
          _ = edge r a * σ (pairedVertex x) * σ (flip (pairedVertex x) i) ^ 2 := by ring
          _ = _ := by rw [hsq, mul_one]
      _ = -(edge r i * (σ (flip r i) * σ (flip (pairedVertex x) i))) * σ (flip (pairedVertex x) i) := by
        rw [← he, hcurv, hd]
      _ = -edge r i * σ (flip r i) := by
        calc
          _ = -edge r i * σ (flip r i) * σ (flip (pairedVertex x) i) ^ 2 := by ring
          _ = _ := by rw [hsq, mul_one]

private def transverse (i : Fin 9) (w : Fin 9 → ℝ) : Matrix (Q 9) (Q 9) ℝ :=
  signed (fun a => if a = i then 0 else w a)

private theorem transverse_entry (w : Fin 9 → ℝ) {r y : Q 9} {a : Fin 9}
    (hai : a ≠ i) (ha : flip r a = y) : transverse i w r y = w a * edge r a := by
  simp only [transverse, signed]
  rw [Finset.sum_eq_single a]
  · rw [if_pos ha, if_neg hai, flipSign_cast]
  · intro c _ hca
    have hcy : flip r c ≠ y := fun h => hca (flip_injective r (h.trans ha.symm))
    rw [if_neg hcy]
  · simp

private theorem transverse_zero (w : Fin 9 → ℝ) {r y : Q 9}
    (h : ¬ ∃ a, a ≠ i ∧ flip r a = y) : transverse i w r y = 0 := by
  simp only [transverse, signed]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a = i
  · simp [ha]
  · rw [if_neg (fun he => h ⟨a, ha, he⟩)]

private def occupiedMatrix (C : Finset (Q 9)) (b : Bool) (i : Fin 9) (σ : Q 9 → ℝ)
    (w : Fin 9 → ℝ) : Matrix (Q 9) (PairedRows C b i) ℝ :=
  fun r x => if occupied C i r then rowSign C i σ r * transverse i w r (pairedVertex x) * σ (pairedVertex x)
    else 0

private def emptyMatrix (C : Finset (Q 9)) (b : Bool) (i : Fin 9) (σ : Q 9 → ℝ)
    (w : Fin 9 → ℝ) : Matrix (Q 9) (PairedRows C b i) ℝ :=
  fun r x => if occupied C i r then 0 else transverse i w r (pairedVertex x) * σ (pairedVertex x)

private theorem occupied_entry {σ : Q 9 → ℝ} (hs : IsSwitching C σ) (w : Fin 9 → ℝ)
    {r : Q 9} {x : PairedRows C b i} {a : Fin 9}
    (hr : occupied C i r) (ha : a ≠ i) (he : flip r a = pairedVertex x) :
    occupiedMatrix C b i σ w r x = w a := by
  rw [occupiedMatrix, if_pos hr, transverse_entry w ha he]
  calc
    _ = w a * (rowSign C i σ r * (edge r a * σ (pairedVertex x))) := by ring
    _ = w a := by rw [coherent_transverse_edge hs hr ha he, ← pow_two, rowSign_sq hs hr, mul_one]

private theorem occupied_entry_zero (σ : Q 9 → ℝ) (w : Fin 9 → ℝ)
    {r : Q 9} {x : PairedRows C b i} (h : ¬ occupiedContact C b i r x) :
    occupiedMatrix C b i σ w r x = 0 := by
  by_cases hr : occupied C i r
  · rw [occupiedMatrix, if_pos hr, transverse_zero w (fun he => h ⟨hr, he⟩),
      mul_zero, zero_mul]
  · simp only [occupiedMatrix, if_neg hr]

private theorem split_gram {σ : Q 9 → ℝ} (hs : IsSwitching C σ) (w : Fin 9 → ℝ) :
    (occupiedMatrix C b i σ w)ᵀ * occupiedMatrix C b i σ w +
      (emptyMatrix C b i σ w)ᵀ * emptyMatrix C b i σ w =
      (∑ a : Fin 9, (if a = i then 0 else w a) ^ 2) •
        (1 : Matrix (PairedRows C b i) (PairedRows C b i) ℝ) := by
  let O := occupiedMatrix C b i σ w
  let E := emptyMatrix C b i σ w
  let H := transverse i w
  let c : ℝ := ∑ a : Fin 9, (if a = i then 0 else w a) ^ 2
  have hH : Hᵀ * H = c • (1 : Matrix (Q 9) (Q 9) ℝ) := by
    dsimp only [H, c, transverse]
    rw [signed_transpose, signed_square]
  ext x y
  change (Oᵀ * O + Eᵀ * E) x y = (c • (1 : Matrix _ _ ℝ)) x y
  calc
    _ = σ (pairedVertex x) * σ (pairedVertex y) * (Hᵀ * H) (pairedVertex x) (pairedVertex y) := by
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : occupied C i r
      · simp only [O, E, H, occupiedMatrix, emptyMatrix, if_pos hr, zero_mul, add_zero]
        calc
          _ = rowSign C i σ r ^ 2 *
              (σ (pairedVertex x) * σ (pairedVertex y) * (transverse i w r (pairedVertex x) * transverse i w r (pairedVertex y))) := by
            ring
          _ = _ := by rw [rowSign_sq hs hr, one_mul]
      · simp only [O, E, H, occupiedMatrix, emptyMatrix, if_neg hr, zero_mul, zero_add]
        ring
    _ = _ := by
      rw [hH]
      by_cases h : x = y
      · subst y
        rw [Matrix.smul_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
          ← pow_two (σ (pairedVertex x)), switching_sq hs x.1.1.property, one_mul]
      · rw [Matrix.smul_apply, Matrix.one_apply_ne (fun hv => h (vertex_injective hv)),
          Matrix.smul_apply, Matrix.one_apply_ne h, smul_zero, mul_zero]

private theorem empty_boundary_iff (σ : Q 9 → ℝ) (w : Fin 9 → ℝ)
    (f : PairedRows C b i → ℝ) :
    emptyMatrix C b i σ w *ᵥ f = 0 ↔
      emptyFibreBoundary C b i w *ᵥ (fun x => σ (pairedVertex x) * f x) = 0 := by
  have hrow (r : Q 9) (hC : r ∉ C) (hi : flip r i ∉ C) (hb : parity r ≠ b) :
      (emptyMatrix C b i σ w *ᵥ f) r =
        (emptyFibreBoundary C b i w *ᵥ (fun x => σ (pairedVertex x) * f x))
          ⟨⟨⟨r, hb⟩, hC⟩, hi⟩ := by
    have hocc : ¬ occupied C i r := not_or.mpr ⟨hC, hi⟩
    simp only [Matrix.mulVec, dotProduct, emptyMatrix, ite_eq_right hocc,
      emptyFibreBoundary, Matrix.submatrix_apply, transverseBoundary, boundaryOver, transverse,
      pairedVertex, mul_assoc]
  constructor
  · intro hf
    funext y
    exact (hrow y.1.1.1 y.1.property y.property y.1.1.property).symm.trans
      (congrFun hf y.1.1.1)
  · intro hf
    funext r
    by_cases hr : occupied C i r
    · simp [Matrix.mulVec, dotProduct, emptyMatrix, hr]
    · by_cases hb : parity r = b
      · change (∑ x, emptyMatrix C b i σ w r x * f x) = 0
        apply Finset.sum_eq_zero
        intro x _
        have hz : transverse i w r (pairedVertex x) = 0 := by
          apply transverse_zero
          rintro ⟨a, _, ha⟩
          have hpar : parity r ≠ !b := by
            rw [hb]
            cases b <;> decide
          exact Q9IsotropicHuang.flip_off_parity (b := b) a hpar
            (ha.symm ▸ vertex_parity x)
        rw [emptyMatrix, if_neg hr, hz, zero_mul, zero_mul]
      · have hC : r ∉ C := fun h => hr (Or.inl h)
        have hi : flip r i ∉ C := fun h => hr (Or.inr h)
        exact (hrow r hC hi hb).trans (congrFun hf _)

private theorem switch_twice {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    (f : PairedRows C b i → ℝ) :
    (fun x => σ (pairedVertex x) * (σ (pairedVertex x) * f x)) = f := by
  funext x
  rw [← mul_assoc, ← pow_two (σ (pairedVertex x)), switching_sq hs x.1.1.property, one_mul]

private theorem switch_zero_iff {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    (x : PairedRows C b i) (a : ℝ) : σ (pairedVertex x) * a = 0 ↔ a = 0 := by
  rcases hs.1 (pairedVertex x) x.1.1.property with h | h <;> simp [h]

private theorem occupied_pos_iff {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {w : Fin 9 → ℝ} (hw : ∀ a, a ≠ i → 0 < w a) (r : Q 9) (x : PairedRows C b i) :
    0 < occupiedMatrix C b i σ w r x ↔ occupiedContact C b i r x := by
  by_cases h : occupiedContact C b i r x
  · obtain ⟨hr, a, ha, he⟩ := h
    rw [occupied_entry hs w hr ha he]
    exact ⟨fun _ => ⟨hr, a, ha, he⟩, fun _ => hw a ha⟩
  · rw [occupied_entry_zero σ w h]
    simp [h]

private theorem occupied_nonneg {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {w : Fin 9 → ℝ} (hw : ∀ a, a ≠ i → 0 ≤ w a) (r : Q 9) (x : PairedRows C b i) :
    0 ≤ occupiedMatrix C b i σ w r x := by
  by_cases h : occupiedContact C b i r x
  · obtain ⟨hr, a, ha, he⟩ := h
    rw [occupied_entry hs w hr ha he]
    exact hw a ha
  · rw [occupied_entry_zero σ w h]

/-- The signs are taken from a single switching of the actual Q9 support. Taking
the absolute values of an empty-fibre kernel and applying these signs preserves
the kernel and the exact support, at every nonnegative transverse weighting. -/
theorem switching_abs_mem_emptyFibre_kernel {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {w : Fin 9 → ℝ} (hw : ∀ a, a ≠ i → 0 ≤ w a)
    {f : PairedRows C b i → ℝ} (hf : emptyFibreBoundary C b i w *ᵥ f = 0) :
    (emptyFibreBoundary C b i w *ᵥ (fun x => σ (pairedVertex x) * |f x|) = 0) ∧
      ∀ x, σ (pairedVertex x) * |f x| = 0 ↔ f x = 0 := by
  have hE := (empty_boundary_iff σ w (fun x => σ (pairedVertex x) * f x)).mpr
    (by rw [switch_twice hs f]; exact hf)
  have hAbs := abs_mem_kernel (split_gram hs w) (occupied_nonneg hs hw) hE
  have hsame (x : PairedRows C b i) : |σ (pairedVertex x) * f x| = |f x| := by
    rcases hs.1 (pairedVertex x) x.1.1.property with h | h <;> simp [h]
  simp only [hsame] at hAbs
  exact ⟨(empty_boundary_iff σ w _).mp hAbs, fun x =>
    (switch_zero_iff hs x |f x|).trans abs_eq_zero⟩

/-- At positive transverse weights the support of every empty-fibre kernel is a
union of components of the actual occupied-row graph. -/
theorem emptyFibre_kernel_zero_iff_of_reachable {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {w : Fin 9 → ℝ} (hw : ∀ a, a ≠ i → 0 < w a) {f : PairedRows C b i → ℝ}
    (hf : emptyFibreBoundary C b i w *ᵥ f = 0) {x y : PairedRows C b i}
    (hxy : (pairedGraph C b i).Reachable x y) : f x = 0 ↔ f y = 0 := by
  have hE := (empty_boundary_iff σ w (fun z => σ (pairedVertex z) * f z)).mpr
    (by rw [switch_twice hs f]; exact hf)
  have hcontact : (fun r z => 0 < occupiedMatrix C b i σ w r z) = occupiedContact C b i :=
    funext fun r => funext fun z => propext (occupied_pos_iff hs hw r z)
  have hp : (occupiedGraph (fun r z => 0 < occupiedMatrix C b i σ w r z)).Reachable x y := by
    rw [hcontact]
    exact hxy
  have hz := zero_iff_of_reachable (split_gram hs w) (occupied_nonneg hs fun a ha =>
    (hw a ha).le) hE hp
  exact (switch_zero_iff hs x (f x)).symm.trans (hz.trans (switch_zero_iff hs y (f y)))

private theorem occupied_gram_block (σ : Q 9 → ℝ) (w : Fin 9 → ℝ)
    {x y : PairedRows C b i}
    (h : (pairedGraph C b i).connectedComponentMk x ≠
      (pairedGraph C b i).connectedComponentMk y) :
    ((occupiedMatrix C b i σ w)ᵀ * occupiedMatrix C b i σ w) x y = 0 := by
  have hne : x ≠ y := fun he => h (congrArg (pairedGraph C b i).connectedComponentMk he)
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hx : occupiedContact C b i r x
  · have hy : ¬ occupiedContact C b i r y := fun hy =>
      h (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (pairedGraph C b i).Adj x y from ⟨hne, r, hx, hy⟩))
    rw [occupied_entry_zero σ w hy, mul_zero]
  · rw [occupied_entry_zero σ w hx, zero_mul]

/-- Restrict an actual empty-fibre kernel to one occupied component. This remains
valid with zero, negative, or masked transverse weights. -/
theorem emptyFibre_kernel_restrict_component {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {w : Fin 9 → ℝ} {f : PairedRows C b i → ℝ} (hf : emptyFibreBoundary C b i w *ᵥ f = 0)
    (k : (pairedGraph C b i).ConnectedComponent) :
    emptyFibreBoundary C b i w *ᵥ
      (fun x => if (pairedGraph C b i).connectedComponentMk x = k then f x else 0) = 0 := by
  let tag := (pairedGraph C b i).connectedComponentMk
  have hE := (empty_boundary_iff σ w (fun x => σ (pairedVertex x) * f x)).mpr
    (by rw [switch_twice hs f]; exact hf)
  have hk := restrict_mem_kernel (split_gram hs w) tag
    (fun _ _ h => occupied_gram_block σ w h) hE k
  have he := (empty_boundary_iff σ w _).mp hk
  have hswitch :
      (fun x => σ (pairedVertex x) * (if tag x = k then σ (pairedVertex x) * f x else 0)) =
        (fun x => if tag x = k then f x else 0) := by
    funext x
    by_cases hx : tag x = k
    · simp only [if_pos hx]
      exact congrFun (switch_twice hs f) x
    · simp only [if_neg hx, mul_zero]
  rw [hswitch] at he
  exact he

/-- On each occupied component, the coordinate ratios of any two kernels agree.
This gives a one-dimensional kernel on every component carrying nonzero mass
when the transverse weights are positive. -/
theorem emptyFibre_kernel_cross_mul_of_reachable {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    {w : Fin 9 → ℝ} (hw : ∀ a, a ≠ i → 0 < w a) {f g : PairedRows C b i → ℝ}
    (hf : emptyFibreBoundary C b i w *ᵥ f = 0) (hg : emptyFibreBoundary C b i w *ᵥ g = 0)
    {x y : PairedRows C b i} (hxy : (pairedGraph C b i).Reachable x y) :
    f x * g y = g x * f y := by
  let h : PairedRows C b i → ℝ := f x • g - g x • f
  have hker : emptyFibreBoundary C b i w *ᵥ h = 0 := by
    simp [h, Matrix.mulVec_sub, Matrix.mulVec_smul, hf, hg]
  have hx : h x = 0 := by
    change f x * g x - g x * f x = 0
    rw [mul_comm (f x) (g x), sub_self]
  have hy := (emptyFibre_kernel_zero_iff_of_reachable hs hw hker hxy).mp hx
  exact sub_eq_zero.mp (show f x * g y - g x * f y = 0 from hy)

private def emptyPolynomial (C : Finset (Q 9)) (b : Bool) (i : Fin 9) (σ : Q 9 → ℝ) :
    Matrix (Q 9) (PairedRows C b i) (MvPolynomial (Fin 9) ℝ) :=
  fun r x => if occupied C i r then 0 else
    signed (fun a => if a = i then 0 else MvPolynomial.X a) r (pairedVertex x) *
      MvPolynomial.C (σ (pairedVertex x))

private theorem eval_emptyPolynomial (σ : Q 9 → ℝ) (w : Fin 9 → ℝ) :
    (emptyPolynomial C b i σ).map (MvPolynomial.eval w) = emptyMatrix C b i σ w := by
  ext r x
  by_cases hr : occupied C i r
  · simp only [Matrix.map_apply, emptyPolynomial, emptyMatrix, if_pos hr, map_zero]
  · have hH :
        MvPolynomial.eval w
          (signed (fun a => if a = i then 0 else MvPolynomial.X a) r (pairedVertex x)) =
          transverse i w r (pairedVertex x) := by
      simp only [transverse, signed, map_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    simp only [Matrix.map_apply, emptyPolynomial, emptyMatrix, if_neg hr,
      map_mul, MvPolynomial.eval_C, hH]

/-- Universal singularity of the real empty-fibre boundary selects a single occupied
component, independently of the transverse weights. At positive transverse weights
the kernel has exactly that support and all its entries have the given switching signs. -/
theorem exists_fixed_occupiedComponent_emptyFibre_kernel {σ : Q 9 → ℝ} (hs : IsSwitching C σ)
    (hker : ∀ w : Fin 9 → ℝ, ∃ f ≠ 0, emptyFibreBoundary C b i w *ᵥ f = 0) :
    ∃ k : (pairedGraph C b i).ConnectedComponent, ∀ w : Fin 9 → ℝ,
      ∃ f : PairedRows C b i → ℝ, f ≠ 0 ∧ emptyFibreBoundary C b i w *ᵥ f = 0 ∧
        (∀ x, (pairedGraph C b i).connectedComponentMk x ≠ k → f x = 0) ∧
        ((∀ a, a ≠ i → 0 < w a) →
          ∀ x, (pairedGraph C b i).connectedComponentMk x = k →
            0 < σ (pairedVertex x) * f x) := by
  classical
  let G := pairedGraph C b i
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let idx := Fintype.equivFin G.ConnectedComponent
  let tag (x : PairedRows C b i) := idx (G.connectedComponentMk x)
  let P := emptyPolynomial C b i σ
  have hmap (w : Fin 9 → ℝ) : P.map (MvPolynomial.eval w) = emptyMatrix C b i σ w :=
    eval_emptyPolynomial σ w
  have hdet : (Pᵀ * P).det = 0 := by
    apply MvPolynomial.funext
    intro w
    rw [map_zero, eval_gram_det, hmap]
    obtain ⟨f, hf, hfker⟩ := hker w
    let u : PairedRows C b i → ℝ := fun x => σ (pairedVertex x) * f x
    have hu : u ≠ 0 := fun h => hf (funext fun x =>
      (switch_zero_iff hs x (f x)).mp (congrFun h x))
    have huKer := (empty_boundary_iff σ w u).mpr (by
      change emptyFibreBoundary C b i w *ᵥ
        (fun x => σ (pairedVertex x) * (σ (pairedVertex x) * f x)) = 0
      rw [switch_twice hs f]
      exact hfker)
    apply (Matrix.exists_mulVec_eq_zero_iff (M := (emptyMatrix C b i σ w)ᵀ *
      emptyMatrix C b i σ w)).mp
    exact ⟨u, hu, (gram_kernel_iff _ u).mpr huKer⟩
  have htri : (Pᵀ * P).BlockTriangular tag := by
    intro x y hxy
    have hne : G.connectedComponentMk x ≠ G.connectedComponentMk y :=
      fun h => (ne_of_gt hxy) (congrArg idx h)
    apply MvPolynomial.funext
    intro w
    rw [map_zero]
    change ((Pᵀ * P).map (MvPolynomial.eval w)) x y = 0
    rw [Matrix.map_mul, Matrix.transpose_map, hmap]
    exact complement_block (split_gram hs w) (fun h => hne (congrArg G.connectedComponentMk h))
      (occupied_gram_block σ w hne)
  have hprod := htri.det_fintype.symm.trans hdet
  obtain ⟨t, _, ht⟩ := Finset.prod_eq_zero_iff.mp hprod
  refine ⟨idx.symm t, fun w => ?_⟩
  let E := emptyMatrix C b i σ w
  let Pt := P.submatrix id (Subtype.val : {x // tag x = t} → PairedRows C b i)
  let Et := E.submatrix id (Subtype.val : {x // tag x = t} → PairedRows C b i)
  have hmapt : Pt.map (MvPolynomial.eval w) = Et := by
    ext r x
    exact congrFun (congrFun (hmap w) r) x.1
  have ht' : (Ptᵀ * Pt).det = 0 := ht
  have hdet' := congrArg (MvPolynomial.eval w) ht'
  rw [eval_gram_det, hmapt, map_zero] at hdet'
  obtain ⟨v, hv, hvG⟩ := (Matrix.exists_mulVec_eq_zero_iff
    (M := Etᵀ * Et)).mpr hdet'
  have hvE := (gram_kernel_iff Et v).mp hvG
  let u (x : PairedRows C b i) : ℝ := if hx : tag x = t then v ⟨x, hx⟩ else 0
  have huv (x : {x // tag x = t}) : u x.1 = v x := dif_pos x.property
  have hu : u ≠ 0 := fun h => hv (funext fun x => (huv x).symm.trans (congrFun h x.1))
  have huE : E *ᵥ u = 0 := by
    funext r
    calc
      (E *ᵥ u) r = (Et *ᵥ v) r := by
        simp only [Matrix.mulVec, dotProduct, Et, Matrix.submatrix_apply, id_eq]
        symm
        refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _ ?_ ?_
        · intro x hx
          have hn : tag x ≠ t := fun ht => hx ⟨⟨x, ht⟩, rfl⟩
          simp [u, hn]
        · intro x
          rw [huv]
      _ = 0 := congrFun hvE r
  let f : PairedRows C b i → ℝ := fun x => σ (pairedVertex x) * u x
  have hf : f ≠ 0 := fun h => hu (funext fun x =>
    (switch_zero_iff hs x (u x)).mp (congrFun h x))
  have hfE := (empty_boundary_iff σ w u).mp huE
  have htag (x : PairedRows C b i) : tag x = t ↔ G.connectedComponentMk x = idx.symm t := by
    change idx (G.connectedComponentMk x) = t ↔ _
    rw [Equiv.eq_symm_apply]
  have hfs (x : PairedRows C b i) (hx : G.connectedComponentMk x ≠ idx.symm t) : f x = 0 := by
    have hxt : tag x ≠ t := fun h => hx ((htag x).mp h)
    simp [f, u, hxt]
  by_cases hw : ∀ a, a ≠ i → 0 < w a
  · obtain ⟨habs, hz⟩ := switching_abs_mem_emptyFibre_kernel hs
      (fun a ha => (hw a ha).le) hfE
    refine ⟨fun x => σ (pairedVertex x) * |f x|, ?_, habs, ?_, ?_⟩
    · intro h
      exact hf (funext fun x => (hz x).mp (congrFun h x))
    · exact fun x hx => (hz x).mpr (hfs x hx)
    · intro _ x hx
      obtain ⟨y, hy⟩ := Function.ne_iff.mp hf
      have hyc : G.connectedComponentMk y = idx.symm t := by
        by_contra hn
        exact hy (hfs y hn)
      have hreach : G.Reachable x y := SimpleGraph.ConnectedComponent.exact (hx.trans hyc.symm)
      have hfx : f x ≠ 0 := fun h =>
        hy ((emptyFibre_kernel_zero_iff_of_reachable hs hw hfE hreach).mp h)
      rw [← mul_assoc, ← pow_two (σ (pairedVertex x)), switching_sq hs x.1.1.property, one_mul]
      exact abs_pos.mpr hfx
  · exact ⟨f, hf, hfE, hfs, fun h => (hw h).elim⟩

open Q9ComponentSaturation (componentDefect exists_two_weighted_singular_components)
open TwoBalancedComponents (componentFinset)
open CoordinateHalves.Q9DominantAxisBoundary (boundary exists_emptyFibreBoundary_kernel)
open Translation.Q9ActualAperiodicity (signed_defect_det_eq_component)
open private regular_and_balanced_of_component_singular from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity

/-- The two singular components of a 258-vertex subcubic support, at retained
parity false, each have a single switching and a single occupied component per
axis carrying kernels for every transverse weighting. -/
theorem exists_two_components_with_fixed_occupied_kernel (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ A B : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      A ≠ B ∧ ∀ K, K = A ∨ K = B →
        let C := componentFinset U K
        ∃ σ : Q 9 → ℝ, IsSwitching C σ ∧ ∀ i : Fin 9,
          ∃ k : (pairedGraph C false i).ConnectedComponent, ∀ w : Fin 9 → ℝ,
            ∃ f : PairedRows C false i → ℝ,
              f ≠ 0 ∧ emptyFibreBoundary C false i w *ᵥ f = 0 ∧
              (∀ x, (pairedGraph C false i).connectedComponentMk x ≠ k → f x = 0) ∧
              ((∀ a, a ≠ i → 0 < w a) →
                ∀ x, (pairedGraph C false i).connectedComponentMk x = k →
                  0 < σ (pairedVertex x) * f x) := by
  obtain ⟨A, B, hAB, hdet⟩ := exists_two_weighted_singular_components U hU hdeg false
  refine ⟨A, B, hAB, fun K hK => ?_⟩
  have hKdet (w : Fin 9 → ℝ) : (componentDefect w U false K).det = 0 := by
    rcases hK with rfl | rfl
    · exact (hdet w).1
    · exact (hdet w).2
  obtain ⟨_, hbal⟩ := regular_and_balanced_of_component_singular U K hdeg (hKdet fun _ => 1)
  obtain ⟨σ, hs⟩ := hbal
  refine ⟨σ, hs, fun i => exists_fixed_occupiedComponent_emptyFibre_kernel hs (fun w => ?_)⟩
  apply exists_emptyFibreBoundary_kernel (componentFinset U K) false _ i w
  intro v
  apply (gram_det_eq_zero_iff _).mp
  rw [boundary_gram_eq_signed_defect, signed_defect_det_eq_component]
  exact hKdet v

end Cube

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositivePairedKernel
