import D5.S3.Combinatorics.SpectralGraph.MandalMannaDQDilworthRefutation
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Distance multiplicity for a universal-clique family of cographs

The graph is the join of a clique with a disjoint union of a balanced complete
bipartite graph and isolated vertices. The family addresses the explicit-family
clause of Open Problem 14.2(ii) in arXiv:2611.06981v1, p. 22.
-/

namespace D5.S3.Combinatorics.SpectralGraph.UniversalCliqueCographDistance

open SimpleGraph
open MandalMannaDQDilworthRefutation (vicinal HasChainCover dilworthNumber)

abbrev Vertex (r s b : ℕ) := Fin r ⊕ ((Fin s ⊕ Fin s) ⊕ Fin b)

variable {r s b : ℕ}

private abbrev hub (i : Fin r) : Vertex r s b := .inl i
private abbrev left (i : Fin s) : Vertex r s b := .inr (.inl (.inl i))
private abbrev right (i : Fin s) : Vertex r s b := .inr (.inl (.inr i))
private abbrev isolate (i : Fin b) : Vertex r s b := .inr (.inr i)

/-- The universal-clique join on its native disjoint-sum carrier. -/
def graph (r s b : ℕ) : SimpleGraph (Vertex r s b) :=
  (((⊤ : SimpleGraph (Fin r))ᶜ).sum
    (((completeBipartiteGraph (Fin s) (Fin s)).sum (⊥ : SimpleGraph (Fin b)))ᶜ))ᶜ

local notation "G" => graph r s b

private theorem hub_universal (i : Fin r) : (G).IsUniversal (hub i) := by
  intro v hv
  cases v <;> simp_all [graph]

theorem connected (hr : 0 < r) : (graph r s b).Connected :=
  Connected.of_isUniversal (hub_universal ⟨0, hr⟩)

open scoped Classical in
theorem distance (hr : 0 < r) (u v : Vertex r s b) :
    (G).dist u v = if u = v then 0 else if (G).Adj u v then 1 else 2 := by
  classical
  split_ifs with heq hadj
  · subst v
    exact dist_self
  · exact dist_eq_one_iff_adj.mpr hadj
  · let h : Vertex r s b := hub ⟨0, hr⟩
    have hu : u ≠ h := by
      intro e
      subst u
      exact hadj (hub_universal ⟨0, hr⟩ heq)
    have hv : v ≠ h := by
      intro e
      subst v
      exact hadj (hub_universal ⟨0, hr⟩ (Ne.symm heq)).symm
    have hed := (G).edist_eq_two_iff.mpr
      ⟨heq, hadj, h, (hub_universal ⟨0, hr⟩ (Ne.symm hu)).symm,
        (hub_universal ⟨0, hr⟩ (Ne.symm hv)).symm⟩
    simp [SimpleGraph.dist, hed]

private theorem not_hub_of_nonadjacent {u v : Vertex r s b} (hne : u ≠ v)
    (hn : ¬ (G).Adj u v) : ∃ z, u = Sum.inr z := by
  cases u with
  | inl i => exact (hn (hub_universal i hne)).elim
  | inr z => exact ⟨z, rfl⟩

theorem induced_path_excluded (r s b : ℕ) :
    ¬ (pathGraph 4).IsIndContained (graph r s b) := by
  rintro ⟨e⟩
  have nonedge (i j : Fin 4) (h : ¬ (pathGraph 4).Adj i j) :
      ¬ (graph r s b).Adj (e i) (e j) := fun h' => h (e.map_rel_iff.mp h')
  have edge (i j : Fin 4) (h : (pathGraph 4).Adj i j) :
      (graph r s b).Adj (e i) (e j) := e.map_rel_iff.mpr h
  have h02 := nonedge 0 2 (by decide)
  have h13 := nonedge 1 3 (by decide)
  obtain ⟨x0, hx0⟩ := not_hub_of_nonadjacent (e.injective.ne (by decide : (0 : Fin 4) ≠ 2)) h02
  obtain ⟨x1, hx1⟩ := not_hub_of_nonadjacent (e.injective.ne (by decide : (1 : Fin 4) ≠ 3)) h13
  obtain ⟨x2, hx2⟩ := not_hub_of_nonadjacent (e.injective.ne (by decide : (2 : Fin 4) ≠ 0))
    (fun h => h02 h.symm)
  obtain ⟨x3, hx3⟩ := not_hub_of_nonadjacent (e.injective.ne (by decide : (3 : Fin 4) ≠ 1))
    (fun h => h13 h.symm)
  have h01 := edge 0 1 (by decide)
  have h12 := edge 1 2 (by decide)
  have h23 := edge 2 3 (by decide)
  have h03 := nonedge 0 3 (by decide)
  rw [hx0, hx1] at h01
  rw [hx1, hx2] at h12
  rw [hx2, hx3] at h23
  rw [hx0, hx3] at h03
  rcases x0 with (i | i) | i <;> rcases x1 with (j | j) | j <;>
    simp [graph, completeBipartiteGraph_adj] at h01
  all_goals
    rcases x2 with (k | k) | k <;> simp [graph, completeBipartiteGraph_adj] at h12
  all_goals
    rcases x3 with (l | l) | l <;> simp [graph, completeBipartiteGraph_adj] at h23
  all_goals
    simp [graph, completeBipartiteGraph_adj] at h03

private theorem vicinal_hub (u : Vertex r s b) (i : Fin r) : vicinal G u (hub i) := by
  intro w _
  by_cases h : w = hub i
  · exact Or.inl h
  · exact Or.inr (hub_universal i (Ne.symm h))

private theorem vicinal_left (i j : Fin s) : vicinal G (left i) (left j) := by
  intro w h
  refine Or.inr ?_
  rcases w with x | ((x | x) | x) <;>
    simp_all [graph, completeBipartiteGraph_adj, mem_neighborSet]

private theorem vicinal_right (i j : Fin s) : vicinal G (right i) (right j) := by
  intro w h
  refine Or.inr ?_
  rcases w with x | ((x | x) | x) <;>
    simp_all [graph, completeBipartiteGraph_adj, mem_neighborSet]

private theorem vicinal_isolate (i : Fin b) (u : Vertex r s b) : vicinal G (isolate i) u := by
  intro w h
  rcases w with x | ((x | x) | x)
  · by_cases he : hub x = u
    · exact Or.inl he
    · exact Or.inr (hub_universal x he).symm
  all_goals simp [graph, mem_neighborSet] at h

private def chain (v : Vertex r s b) : Fin 2 :=
  match v with
  | .inr (.inl (.inr _)) => 1
  | _ => 0

theorem two_chain_cover (r s b : ℕ) : HasChainCover (graph r s b) 2 := by
  refine ⟨chain, ?_⟩
  intro u v h
  rcases u with i | ((i | i) | i) <;> rcases v with j | ((j | j) | j) <;>
    first
    | exact Or.inr (vicinal_hub _ _)
    | exact Or.inl (vicinal_hub _ _)
    | exact Or.inl (vicinal_left _ _)
    | exact Or.inl (vicinal_right _ _)
    | exact Or.inl (vicinal_isolate _ _)
    | exact Or.inr (vicinal_isolate _ _)
    | exfalso; exact (by decide : (0 : Fin 2) ≠ 1) h
    | exfalso; exact (by decide : (1 : Fin 2) ≠ 0) h

theorem incomparable_parts (hs : 2 ≤ s) (i j : Fin s) :
    ¬ vicinal G (left i) (right j) ∧ ¬ vicinal G (right j) (left i) := by
  have other (x : Fin s) : ∃ y : Fin s, y ≠ x := by
    let z : Fin s := ⟨0, by omega⟩
    let o : Fin s := ⟨1, by omega⟩
    by_cases h : x = z
    · refine ⟨o, ?_⟩
      intro h'
      have := congrArg Fin.val (h'.trans h)
      contradiction
    · exact ⟨z, Ne.symm h⟩
  obtain ⟨j', hj⟩ := other j
  obtain ⟨i', hi⟩ := other i
  constructor
  · intro h
    have hh := h (show right j' ∈ (G).neighborSet (left i) by
      simp [graph, completeBipartiteGraph_adj, mem_neighborSet])
    simp [graph, completeBipartiteGraph_adj, mem_neighborSet, hj] at hh
  · intro h
    have hh := h (show left i' ∈ (G).neighborSet (right j) by
      simp [graph, completeBipartiteGraph_adj, mem_neighborSet])
    simp [graph, completeBipartiteGraph_adj, mem_neighborSet, hi] at hh

theorem width (hs : 2 ≤ s) : dilworthNumber G = 2 := by
  apply le_antisymm
  · exact sInf_le ⟨2, by norm_num, two_chain_cover r s b⟩
  · apply le_sInf
    rintro _ ⟨k, rfl, c, hc⟩
    have hk : 2 ≤ k := by
      by_contra! hk
      let i : Fin s := ⟨0, by omega⟩
      have hval := (c (left i)).isLt
      have hval' := (c (right i)).isLt
      have heq : c (left i) = c (right i) := Fin.ext (by omega)
      have hn := incomparable_parts (r := r) (b := b) hs i i
      exact (hc _ _ heq).elim hn.1 hn.2
    exact_mod_cast hk

/-- The ordinary real shortest-path distance matrix of the family. -/
noncomputable def distanceMatrix (r s b : ℕ) : Matrix (Vertex r s b) (Vertex r s b) ℝ :=
  Matrix.of fun u v => ((graph r s b).dist u v : ℝ)

/-- The ordinary distance matrix minus the shift `s - 2` times the identity. -/
noncomputable def shiftedDistance (r s b : ℕ) : Matrix (Vertex r s b) (Vertex r s b) ℝ :=
  distanceMatrix r s b - ((s : ℝ) - 2) • 1

/-- The kernel of the ordinary distance matrix shifted by `s - 2`. -/
noncomputable def shiftedKernel (r s b : ℕ) : Submodule ℝ (Vertex r s b → ℝ) :=
  LinearMap.ker (shiftedDistance r s b).mulVecLin

private def weight (u v : Vertex r s b) : ℝ :=
  match u, v with
  | .inl _, _ | _, .inl _ => 1
  | .inr (.inl (.inl _)), .inr (.inl (.inr _))
  | .inr (.inl (.inr _)), .inr (.inl (.inl _)) => 1
  | _, _ => 2

private def diagonalWeight (v : Vertex r s b) : ℝ :=
  match v with
  | .inl _ => (s : ℝ) - 1
  | .inr _ => s

private theorem shiftedDistance_entry (hr : 0 < r) (u v : Vertex r s b) :
    shiftedDistance r s b u v =
      weight u v - if u = v then diagonalWeight u else 0 := by
  classical
  simp only [shiftedDistance, distanceMatrix, Matrix.sub_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, distance hr]
  by_cases h : u = v
  · subst v
    rcases u with i | ((i | i) | i) <;> simp [weight, diagonalWeight]
    ring
  · simp only [ite_eq_right h, mul_zero, sub_zero]
    rcases u with i | ((i | i) | i) <;> rcases v with j | ((j | j) | j) <;>
      simp_all [graph, weight, completeBipartiteGraph_adj]

private abbrev total {n : ℕ} (f : Fin n → ℝ) := ∑ i, f i

private theorem mulVec_rows (hr : 0 < r) (f : Vertex r s b → ℝ) (u : Vertex r s b) :
    ((shiftedDistance r s b).mulVecLin f) u =
      (∑ v, weight u v * f v) - diagonalWeight u * f u := by
  classical
  change (∑ v, shiftedDistance r s b u v * f v) = _
  simp_rw [shiftedDistance_entry hr, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  simp

private theorem mem_shiftedKernel_iff_rows (hr : 0 < r) (f : Vertex r s b → ℝ) :
    f ∈ shiftedKernel r s b ↔
      (∀ i : Fin r, total (f ∘ hub) + total (f ∘ left) + total (f ∘ right) +
        total (f ∘ isolate) = ((s : ℝ) - 1) * f (hub i)) ∧
      (∀ i : Fin s, total (f ∘ hub) + 2 * total (f ∘ left) + total (f ∘ right) +
        2 * total (f ∘ isolate) = (s : ℝ) * f (left i)) ∧
      (∀ i : Fin s, total (f ∘ hub) + total (f ∘ left) + 2 * total (f ∘ right) +
        2 * total (f ∘ isolate) = (s : ℝ) * f (right i)) ∧
      (∀ i : Fin b, total (f ∘ hub) + 2 * total (f ∘ left) + 2 * total (f ∘ right) +
        2 * total (f ∘ isolate) = (s : ℝ) * f (isolate i)) := by
  change (shiftedDistance r s b).mulVecLin f = 0 ↔ _
  rw [funext_iff]
  simp only [Pi.zero_apply, mulVec_rows hr, sub_eq_zero, Sum.forall, Fintype.sum_sum_type,
    weight, diagonalWeight, one_mul, ← Finset.mul_sum, and_assoc, ← add_assoc]
  rfl

private def coordinates (x p q z : ℝ) : Vertex r s b → ℝ
  | .inl _ => x
  | .inr (.inl (.inl _)) => p
  | .inr (.inl (.inr _)) => q
  | .inr (.inr _) => z

private theorem constant_coordinates_of_mem (hr : 0 < r) (hs : 2 ≤ s) (hb : 0 < b)
    {f : Vertex r s b → ℝ} (hf : f ∈ shiftedKernel r s b) :
    ∃ x p q z, f = coordinates x p q z := by
  obtain ⟨hh, hl, hright, hi⟩ := (mem_shiftedKernel_iff_rows hr f).mp hf
  let h0 : Fin r := ⟨0, hr⟩
  let s0 : Fin s := ⟨0, by omega⟩
  let b0 : Fin b := ⟨0, hb⟩
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  refine ⟨f (hub h0), f (left s0), f (right s0), f (isolate b0), ?_⟩
  funext v
  rcases v with i | ((i | i) | i)
  · change f (hub i) = f (hub h0)
    exact mul_left_cancel₀ (show (s : ℝ) - 1 ≠ 0 by linarith)
      ((hh i).symm.trans (hh h0))
  · exact mul_left_cancel₀ (show (s : ℝ) ≠ 0 by linarith)
      ((hl i).symm.trans (hl s0))
  · exact mul_left_cancel₀ (show (s : ℝ) ≠ 0 by linarith)
      ((hright i).symm.trans (hright s0))
  · exact mul_left_cancel₀ (show (s : ℝ) ≠ 0 by linarith)
      ((hi i).symm.trans (hi b0))

private theorem coordinate_rows (hr : 0 < r) (hs : 2 ≤ s) (hb : 0 < b)
    (x p q z : ℝ) :
    coordinates (r := r) (s := s) (b := b) x p q z ∈ shiftedKernel r s b ↔
      (r : ℝ) * x + s * p + s * q + b * z = ((s : ℝ) - 1) * x ∧
      (r : ℝ) * x + 2 * (s * p) + s * q + 2 * (b * z) = s * p ∧
      (r : ℝ) * x + s * p + 2 * (s * q) + 2 * (b * z) = s * q ∧
      (r : ℝ) * x + 2 * (s * p) + 2 * (s * q) + 2 * (b * z) = s * z := by
  let : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  let : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  rw [mem_shiftedKernel_iff_rows hr]
  simp [coordinates, Function.comp_def, nsmul_eq_mul]

private def residual (r s b : ℕ) : ℝ :=
  (r : ℝ) * b - ((s : ℝ) - 1) * ((s : ℝ) + 2 * b)

private noncomputable def mode (r s b : ℕ) : (ℝ × ℝ) →ₗ[ℝ] (Vertex r s b → ℝ) where
  toFun v := coordinates (-(((s : ℝ) + 2 * b) / r) * v.2) v.1 (v.2 - v.1) v.2
  map_add' u v := by
    funext i
    rcases i with i | ((i | i) | i) <;> simp [coordinates] <;> ring
  map_smul' c v := by
    funext i
    rcases i with i | ((i | i) | i) <;> simp [coordinates] <;> ring

private theorem mode_injective (hs : 2 ≤ s) (hb : 0 < b) :
    Function.Injective (mode r s b) := by
  intro u v h
  apply Prod.ext
  · exact congrFun h (left ⟨0, by omega⟩)
  · exact congrFun h (isolate ⟨0, hb⟩)

private theorem mem_kernel_mode (hr : 0 < r) (hs : 2 ≤ s) (hb : 0 < b)
    (f : Vertex r s b → ℝ) :
    f ∈ shiftedKernel r s b ↔
      ∃ v : ℝ × ℝ, residual r s b * v.2 = 0 ∧ mode r s b v = f := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  constructor
  · intro hf
    obtain ⟨x, p, q, z, rfl⟩ := constant_coordinates_of_mem hr hs hb hf
    obtain ⟨e₁, e₂, _, e₄⟩ := (coordinate_rows hr hs hb x p q z).mp hf
    have hz' : (s : ℝ) * (z - (p + q)) = 0 := by linear_combination e₂ - e₄
    have hz : z = p + q := sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left hs')
    have hmain : (r : ℝ) * x + ((s : ℝ) + 2 * b) * z = 0 := by
      linear_combination e₂ + (s : ℝ) * hz
    have hfirst : ((s : ℝ) - 1) * x + (b : ℝ) * z = 0 := by
      linear_combination e₂ - e₁
    have hx : -(((s : ℝ) + 2 * b) / r) * z = x := by
      apply mul_left_cancel₀ hr'
      calc
        (r : ℝ) * (-(((s : ℝ) + 2 * b) / r) * z) = -(((s : ℝ) + 2 * b) * z) := by
          field_simp
        _ = (r : ℝ) * x := by linarith
    refine ⟨(p, z), ?_, ?_⟩
    · unfold residual
      linear_combination (r : ℝ) * hfirst - ((s : ℝ) - 1) * hmain
    · change coordinates (-(((s : ℝ) + 2 * b) / r) * z) p (z - p) z = coordinates x p q z
      rw [hx, show z - p = q by linarith]
  · rintro ⟨⟨p, z⟩, hres, rfl⟩
    let x : ℝ := -(((s : ℝ) + 2 * b) / r) * z
    change coordinates x p (z - p) z ∈ shiftedKernel r s b
    have hmain : (r : ℝ) * x + ((s : ℝ) + 2 * b) * z = 0 := by
      dsimp [x]
      field_simp
      ring
    have hfirst : ((s : ℝ) - 1) * x + (b : ℝ) * z = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hr'
      change residual r s b * z = 0 at hres
      unfold residual at hres
      linear_combination ((s : ℝ) - 1) * hmain + hres
    refine (coordinate_rows hr hs hb x p (z - p) z).mpr ⟨?_, ?_, ?_, ?_⟩
    · linear_combination hmain - hfirst
    · linear_combination hmain
    · linear_combination hmain
    · linear_combination hmain

private theorem residual_eq_zero_iff :
    residual r s b = 0 ↔
      (b : ℤ) * ((r : ℤ) - 2 * ((s : ℤ) - 1)) = (s : ℤ) * ((s : ℤ) - 1) := by
  have h : residual r s b = 0 ↔
      (b : ℝ) * ((r : ℝ) - 2 * ((s : ℝ) - 1)) = (s : ℝ) * ((s : ℝ) - 1) := by
    unfold residual
    constructor <;> intro h <;> linear_combination h
  rw [h]
  exact_mod_cast Iff.rfl

/-- Exact geometric multiplicity at the ordinary distance shift `s - 2`. -/
theorem shiftedKernel_finrank (hr : 0 < r) (hs : 2 ≤ s) (hb : 0 < b) :
    Module.finrank ℝ (shiftedKernel r s b) =
      if (b : ℤ) * ((r : ℤ) - 2 * ((s : ℤ) - 1)) = (s : ℤ) * ((s : ℤ) - 1)
        then 2 else 1 := by
  simp only [← residual_eq_zero_iff (r := r) (s := s) (b := b)]
  split_ifs with h
  · let embedding := (mode r s b).codRestrict (shiftedKernel r s b) fun v =>
      (mem_kernel_mode hr hs hb _).mpr ⟨v, by simp [h], rfl⟩
    have hbij : Function.Bijective embedding := by
      constructor
      · intro u v heq
        exact mode_injective hs hb (congrArg Subtype.val heq)
      · intro f
        obtain ⟨v, _, hv⟩ := (mem_kernel_mode hr hs hb f.val).mp f.property
        exact ⟨v, Subtype.ext hv⟩
    simpa [Module.finrank_prod] using (LinearEquiv.ofBijective embedding hbij).finrank_eq.symm
  · let line := (mode r s b).comp (LinearMap.inl ℝ ℝ ℝ)
    let embedding := line.codRestrict (shiftedKernel r s b) fun p =>
      (mem_kernel_mode hr hs hb _).mpr ⟨(p, 0), mul_zero _, rfl⟩
    have hbij : Function.Bijective embedding := by
      constructor
      · intro p q heq
        exact congrArg Prod.fst (mode_injective hs hb (congrArg Subtype.val heq))
      · intro f
        obtain ⟨⟨p, z⟩, hz, hp⟩ := (mem_kernel_mode hr hs hb f.val).mp f.property
        have hz0 : z = 0 := (mul_eq_zero.mp hz).resolve_left h
        subst z
        exact ⟨p, Subtype.ext hp⟩
    simpa using (LinearEquiv.ofBijective embedding hbij).finrank_eq.symm

/-- Positive divisors parameterize the multiplicity-two locus. -/
theorem parameter_iff_divisor (hs : 2 ≤ s) (hb : 0 < b) :
    (b : ℤ) * ((r : ℤ) - 2 * ((s : ℤ) - 1)) = (s : ℤ) * ((s : ℤ) - 1) ↔
      ∃ d : ℕ, 0 < d ∧ d ∣ s * (s - 1) ∧ r = 2 * (s - 1) + d ∧
        b = s * (s - 1) / d := by
  let delta := (r : ℤ) - 2 * ((s : ℤ) - 1)
  have hs1 : (1 : ℤ) < s := by exact_mod_cast (show 1 < s by omega)
  have hsCast : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by omega
  change (b : ℤ) * delta = (s : ℤ) * ((s : ℤ) - 1) ↔ _
  constructor
  · intro h
    have hdelta : 0 < delta := by
      have hpos : 0 < (b : ℤ) * delta := by rw [h]; positivity
      exact (mul_pos_iff.mp hpos).resolve_right (by omega) |>.2
    let d := delta.toNat
    have hdCast : (d : ℤ) = delta := Int.toNat_of_nonneg hdelta.le
    have hd : 0 < d := by omega
    have hrCast : (r : ℤ) = 2 * ((s - 1 : ℕ) : ℤ) + (d : ℤ) := by
      rw [hdCast, hsCast]
      dsimp [delta]
      ring
    have hprodCast : (b : ℤ) * (d : ℤ) = (s : ℤ) * ((s - 1 : ℕ) : ℤ) := by
      rwa [hdCast, hsCast]
    have hprod : b * d = s * (s - 1) := by exact_mod_cast hprodCast
    refine ⟨d, hd, ⟨b, by simpa [Nat.mul_comm] using hprod.symm⟩, ?_, ?_⟩
    · exact_mod_cast hrCast
    · rw [← hprod, Nat.mul_div_cancel _ hd]
  · rintro ⟨d, _, hdiv, hr, hb'⟩
    have hprod : b * d = s * (s - 1) := by rw [hb', Nat.div_mul_cancel hdiv]
    have hprodCast : (b : ℤ) * (d : ℤ) = (s : ℤ) * ((s - 1 : ℕ) : ℤ) := by
      exact_mod_cast hprod
    have hdCast : delta = (d : ℤ) := by
      dsimp [delta]
      rw [hr]
      push_cast
      rw [hsCast]
      ring
    rwa [hdCast, ← hsCast]

private theorem shiftedKernel_eq_eigenspace :
    shiftedKernel r s b =
      Module.End.eigenspace (Matrix.toLinAlgEquiv' (distanceMatrix r s b)) ((s : ℝ) - 2) := by
  rw [Module.End.eigenspace_def, shiftedKernel, shiftedDistance]
  congr 1
  change Matrix.toLin' _ = Matrix.toLin' _ - _ • _
  rw [map_sub, map_smul, Matrix.toLin'_one]
  rfl

private theorem shift_mem_spectrum (hr : 0 < r) (hs : 2 ≤ s) (hb : 0 < b) :
    (s : ℝ) - 2 ∈ spectrum ℝ (distanceMatrix r s b) := by
  rw [← AlgEquiv.spectrum_eq Matrix.toLinAlgEquiv' (distanceMatrix r s b)]
  apply Module.End.HasEigenvalue.mem_spectrum
  rw [Module.End.hasEigenvalue_iff, ← shiftedKernel_eq_eigenspace]
  intro h
  have hzero := (Submodule.finrank_eq_zero).mpr h
  rw [shiftedKernel_finrank hr hs hb] at hzero
  split_ifs at hzero <;> contradiction

/-- The family obtained with clique size `3 * (s - 1)` and `s` isolates has
strictly increasing orders and attains its width at the eligible shift `s - 2`. -/
theorem family (hs : 2 ≤ s) :
    Fintype.card (Vertex (3 * (s - 1)) s s) = 6 * s - 3 ∧
    (graph (3 * (s - 1)) s s).Connected ∧
    ¬ (pathGraph 4).IsIndContained (graph (3 * (s - 1)) s s) ∧
    dilworthNumber (graph (3 * (s - 1)) s s) = 2 ∧
    ((s : ℝ) - 2 ≠ -1 ∧ (s : ℝ) - 2 ≠ -2) ∧
    (s : ℝ) - 2 ∈ spectrum ℝ (distanceMatrix (3 * (s - 1)) s s) ∧
    Module.finrank ℝ (shiftedKernel (3 * (s - 1)) s s) = 2 := by
  have hr : 0 < 3 * (s - 1) := by omega
  have hb : 0 < s := by omega
  have hsReal : (2 : ℝ) ≤ s := by exact_mod_cast hs
  refine ⟨?_, connected hr, induced_path_excluded _ _ _, width hs,
    ⟨by linarith, by linarith⟩, shift_mem_spectrum hr hs hb, ?_⟩
  · simp only [Vertex, Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [shiftedKernel_finrank hr hs hb, ite_eq_left]
    apply (parameter_iff_divisor hs hb).mpr
    refine ⟨s - 1, by omega, ⟨s, Nat.mul_comm _ _⟩, by omega, ?_⟩
    rw [Nat.mul_div_cancel _ (by omega)]

/-- Every order threshold is exceeded by an eligible width-two witness. -/
theorem unbounded_family (n : ℕ) :
    ∃ s : ℕ, 2 ≤ s ∧ n < Fintype.card (Vertex (3 * (s - 1)) s s) ∧
      (graph (3 * (s - 1)) s s).Connected ∧
      ¬ (pathGraph 4).IsIndContained (graph (3 * (s - 1)) s s) ∧
      dilworthNumber (graph (3 * (s - 1)) s s) = 2 ∧
      ((s : ℝ) - 2 ≠ -1 ∧ (s : ℝ) - 2 ≠ -2) ∧
      (s : ℝ) - 2 ∈ spectrum ℝ (distanceMatrix (3 * (s - 1)) s s) ∧
      Module.finrank ℝ (shiftedKernel (3 * (s - 1)) s s) = 2 := by
  have hs : 2 ≤ n + 2 := by omega
  obtain ⟨hcard, hfamily⟩ := family hs
  exact ⟨n + 2, hs, by rw [hcard]; omega, hfamily⟩

end D5.S3.Combinatorics.SpectralGraph.UniversalCliqueCographDistance
