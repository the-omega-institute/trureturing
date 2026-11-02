/- GID: D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration
   mirror-E: none(waiver:actual-carrier-transport-pending)
   anchors: [D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional]
   utility: none
   digest: An exact two-path configuration-series identity with an arbitrary residual factor. -/

import D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
import D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
import Mathlib.Combinatorics.SimpleGraph.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset PowerSeries
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
namespace D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration

local attribute [instance] Classical.propDecidable

local instance : DecidableRel (SimpleGraph.hasse ℕ).Adj := Classical.decRel _

private lemma path_two : pathSeries 2 = 1 - 2 * X := by
  rw [show 2 = 0 + 2 by omega, path_rec, path_one, path_zero]
  ring

private lemma path_three : pathSeries 3 = 1 - 3 * X + X ^ 2 := by
  rw [show 3 = 1 + 2 by omega, path_rec, path_two, path_one]
  ring

private lemma path_four : pathSeries 4 = 1 - 4 * X + 3 * X ^ 2 := by
  rw [show 4 = 2 + 2 by omega, path_rec, path_three, path_two]
  ring

private lemma path_five : pathSeries 5 = 1 - 5 * X + 6 * X ^ 2 - X ^ 3 := by
  rw [path_rec 3, path_four, path_three]
  ring

private lemma path_six : pathSeries 6 = 1 - 6 * X + 10 * X ^ 2 - 4 * X ^ 3 := by
  rw [path_rec 4, path_five, path_four]
  ring

private lemma path_seven : pathSeries 7 = 1 - 7 * X + 15 * X ^ 2 - 10 * X ^ 3 + X ^ 4 := by
  rw [path_rec 5, path_six, path_five]
  ring

private lemma two_path_series (n k : ℕ) (hn : 3 ≤ n) (hk : 3 ≤ k) :
    (pathSeries n * pathSeries k - pathSeries (n + k - 1) * pathSeries 1) =
      X ^ 3 * pathSeries (n - 3) * pathSeries (k - 3) := by
  induction hs : n + k using Nat.strong_induction_on generalizing n k with
  | h t ih =>
      subst t
      by_cases hn5 : 5 ≤ n
      · have hn2 : 3 ≤ n - 2 := by omega
        have hn1 : 3 ≤ n - 1 := by omega
        have hsum2 : (n - 2) + k < n + k := by omega
        have hsum1 : (n - 1) + k < n + k := by omega
        have h₂ := ih ((n - 2) + k) hsum2 (n - 2) k hn2 hk rfl
        have h₁ := ih ((n - 1) + k) hsum1 (n - 1) k hn1 hk rfl
        have hna : n - 2 + 2 = n := by omega
        rw [← hna, path_rec (n - 2), hna,
          show n + k - 1 = (n + k - 3) + 2 by omega,
          path_rec (n + k - 3), show n - 3 = (n - 5) + 2 by omega,
          path_rec (n - 5)] at ⊢
        have hi₁ : n - 2 + 1 = n - 1 := by omega
        have hi₂ : n + k - 3 + 1 = n - 1 + k - 1 := by omega
        have hi₃ : n - 5 + 1 = n - 4 := by omega
        have hi₄ : n - 1 - 3 = n - 4 := by omega
        have hi₅ : n - 2 - 3 = n - 5 := by omega
        have hiC : n + k - 3 = n - 2 + k - 1 := by omega
        rw [hi₄] at h₁
        rw [hi₅] at h₂
        rw [hi₁, hi₂, hi₃, hiC] at ⊢
        linear_combination h₁ - X * h₂
      · have hn34 : n = 3 ∨ n = 4 := by omega
        rcases hn34 with rfl | rfl
        · by_cases hk5 : 5 ≤ k
          · have hk2 : 3 ≤ k - 2 := by omega
            have hk1 : 3 ≤ k - 1 := by omega
            have hsum2 : 3 + (k - 2) < 3 + k := by omega
            have hsum1 : 3 + (k - 1) < 3 + k := by omega
            have h₂ := ih (3 + (k - 2)) hsum2 3 (k - 2) (by omega) hk2 rfl
            have h₁ := ih (3 + (k - 1)) hsum1 3 (k - 1) (by omega) hk1 rfl
            have hka : k - 2 + 2 = k := by omega
            rw [← hka, path_rec (k - 2), hka,
              show 3 + k - 1 = k + 2 by omega,
              path_rec k, show k - 3 = (k - 5) + 2 by omega,
              path_rec (k - 5)] at ⊢
            have hi₁ : k - 2 + 1 = k - 1 := by omega
            have hi₂ : k - 1 - 3 = k - 5 + 1 := by omega
            have hi₃ : k - 2 - 3 = k - 5 := by omega
            have hiC₂ : 3 + (k - 2) - 1 = k := by omega
            have hiC₁ : 3 + (k - 1) - 1 = k + 1 := by omega
            rw [hi₃, hiC₂] at h₂
            rw [hi₂, hiC₁] at h₁
            rw [hi₁] at ⊢
            linear_combination h₁ - X * h₂
          · have hk34 : k = 3 ∨ k = 4 := by omega
            rcases hk34 with rfl | rfl
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_three, path_five, path_one, path_zero]
              ring_nf
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_three, path_four, path_one, path_six, path_zero]
              ring_nf
        · by_cases hk5 : 5 ≤ k
          · have hk2 : 3 ≤ k - 2 := by omega
            have hk1 : 3 ≤ k - 1 := by omega
            have hsum2 : 4 + (k - 2) < 4 + k := by omega
            have hsum1 : 4 + (k - 1) < 4 + k := by omega
            have h₂ := ih (4 + (k - 2)) hsum2 4 (k - 2) (by omega) hk2 rfl
            have h₁ := ih (4 + (k - 1)) hsum1 4 (k - 1) (by omega) hk1 rfl
            have hka : k - 2 + 2 = k := by omega
            rw [← hka, path_rec (k - 2), hka,
              show 4 + k - 1 = (k + 1) + 2 by omega,
              path_rec (k + 1), show k - 3 = (k - 5) + 2 by omega,
              path_rec (k - 5)] at ⊢
            have hi₁ : k - 2 + 1 = k - 1 := by omega
            have hi₂ : k + 1 + 1 = k + 2 := by omega
            have hi₃ : k - 1 - 3 = k - 5 + 1 := by omega
            have hi₄ : k - 2 - 3 = k - 5 := by omega
            have hiC₁ : 4 + (k - 1) - 1 = k + 2 := by omega
            have hiC₂ : 4 + (k - 2) - 1 = k + 1 := by omega
            rw [hi₄] at h₂
            rw [hiC₂] at h₂
            rw [hiC₁, hi₃] at h₁
            rw [hi₁] at ⊢
            rw [hi₂] at ⊢
            linear_combination h₁ - X * h₂
          · have hk34 : k = 3 ∨ k = 4 := by omega
            rcases hk34 with rfl | rfl
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_four, path_three, path_one, path_six, path_zero]
              ring_nf
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_four, path_one, path_seven]
              ring_nf

/-- The exact series law behind the two-path concentration move.
The factor `R` is arbitrary, so it may be the actual partition series of any
untouched finite residual graph. -/
theorem two_path_series_concentration (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (R : PowerSeries ℤ) :
    (pathSeries (2 * p + 1) * pathSeries (2 * q + 1) * R -
      pathSeries (2 * p + 2 * q + 1) * pathSeries 1 * R) =
      X ^ 3 * pathSeries (2 * p - 2) * pathSeries (2 * q - 2) * R := by
  have h := two_path_series (2 * p + 1) (2 * q + 1) (by omega) (by omega)
  have h' := congrArg (fun t : PowerSeries ℤ => t * R) h
  have hp' : 2 * p + 1 - 3 = 2 * p - 2 := by omega
  have hq' : 2 * q + 1 - 3 = 2 * q - 2 := by omega
  have hL : 2 * p + 1 + (2 * q + 1) - 1 = 2 * p + 2 * q + 1 := by omega
  rw [hp', hq'] at h'
  rw [hL] at h'
  convert h' using 1 <;> ring


open SimpleGraph
open D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling

private lemma configurations_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (V : Finset α) (W : Finset β) :
    configurations (G ⊕g H) (V.disjSum W) =
      ((configurations G V) ×ˢ (configurations H W)).image
        (fun st => st.1.disjSum st.2) := by
  classical
  have hi (S : Finset α) (T : Finset β) :
      (G ⊕g H).IsIndepSet (S.disjSum T : Set (α ⊕ β)) ↔
        G.IsIndepSet (S : Set α) ∧ H.IsIndepSet (T : Set β) := by
    constructor
    · intro h
      constructor
      · intro x hx y hy hn he
        exact h (a := Sum.inl x) (b := Sum.inl y) (by simpa using hx) (by simpa using hy)
          (by simpa using hn) (by simpa using he)
      · intro x hx y hy hn he
        exact h (a := Sum.inr x) (b := Sum.inr y) (by simpa using hx) (by simpa using hy)
          (by simpa using hn) (by simpa using he)
    · rintro ⟨hs, ht⟩ (x | x) hx (y | y) hy hn he
      · exact hs (by simpa using hx) (by simpa using hy)
          (by simpa using hn) he
      · simpa using he
      · simpa using he
      · exact ht (by simpa using hx) (by simpa using hy)
          (by simpa using hn) he
  ext U
  constructor
  · intro hU
    have hh := Finset.mem_filter.mp hU
    have hs := Finset.subset_disjSum.mp (Finset.mem_powerset.mp hh.1)
    have hind := (hi U.toLeft U.toRight).mp (by
      simpa only [Finset.toLeft_disjSum_toRight] using hh.2)
    exact Finset.mem_image.mpr ⟨(U.toLeft, U.toRight),
      Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs.1, hind.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs.2, hind.2⟩⟩,
      Finset.toLeft_disjSum_toRight⟩
  · rintro hU
    obtain ⟨⟨S,T⟩, hST, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨hS,hT⟩ := Finset.mem_product.mp hST
    obtain ⟨hs, hiS⟩ := Finset.mem_filter.mp hS
    obtain ⟨ht, hiT⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.disjSum_mono (Finset.mem_powerset.mp hs) (Finset.mem_powerset.mp ht)),
      (hi S T).mpr ⟨hiS,hiT⟩⟩

private lemma partition_sum {α β K : Type*} [DecidableEq α] [DecidableEq β]
    [CommSemiring K] (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (V : Finset α) (W : Finset β) (w : α ⊕ β → K) :
    partition (G ⊕g H) (V.disjSum W) w =
      partition G V (fun x => w (.inl x)) * partition H W (fun x => w (.inr x)) := by
  classical
  unfold partition
  rw [configurations_sum]
  rw [Finset.sum_image (by
    intro x hx y hy he
    exact Prod.ext (Finset.disjSum_inj.mp he).1 (Finset.disjSum_inj.mp he).2)]
  simp only [Finset.prod_disjSum]
  rw [Finset.sum_product]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

private lemma partition_subtype {α K : Type*} [DecidableEq α] [CommSemiring K]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (w : α → K) :
    partition (G.induce (V : Set α)) univ (fun x => w x.val) = partition G V w := by
  classical
  unfold partition
  apply Finset.sum_bij (fun S _ => S.image Subtype.val)
  · intro S hS
    have hh := Finset.mem_filter.mp hS
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro x hx
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hx
      exact x.property
    · intro x hx y hy hn he
      obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,hby⟩ := Finset.mem_image.mp hy
      subst x
      subst y
      exact hh.2 ha hb (fun h => hn (congrArg Subtype.val h)) he
  · intro S hS T hT he
    exact Finset.image_injective (Subtype.val_injective) he
  · intro S hS
    have hh := Finset.mem_filter.mp hS
    let T : Finset (V : Set α) := S.attach.image
      (fun x => (⟨x.val, (Finset.mem_powerset.mp hh.1) x.property⟩ : (V : Set α)))
    refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ T), ?_⟩, ?_⟩
    · intro x hx y hy hn he
      obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,hby⟩ := Finset.mem_image.mp hy
      exact hh.2 (by simpa [← hax] using a.property)
        (by simpa [← hby] using b.property) (fun h => hn (Subtype.ext h)) he
    · ext x
      simp [T]
      exact (Finset.mem_powerset.mp hh.1)
  · intro S hS
    exact (Finset.prod_image (fun x _ y _ h => Subtype.ext h)).symm

private lemma partition_path (n : ℕ) :
    partition (pathGraph n) univ (fun _ => (-X : PowerSeries ℤ)) = pathSeries n := by
  classical
  let e : Fin n ≃ (range n : Set ℕ) :=
    { toFun := fun i => ⟨i.val, by simpa using i.isLt⟩
      invFun := fun i => ⟨i.val, by simpa using i.property⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  have he : ∀ i j, ((SimpleGraph.hasse ℕ).induce (range n : Set ℕ)).Adj (e i) (e j) ↔
      (pathGraph n).Adj i j := by
    intro i j
    change (SimpleGraph.hasse ℕ).Adj i.val j.val ↔ (pathGraph n).Adj i j
    rw [path_adj, pathGraph_adj]
  have hh := partition_relabel (pathGraph n) ((SimpleGraph.hasse ℕ).induce (range n : Set ℕ))
    e he univ (fun _ => (-X : PowerSeries ℤ))
  rw [Finset.image_univ_equiv] at hh
  rw [partition_subtype] at hh
  exact hh.symm


private lemma partition_embedding {α β K : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] [CommSemiring K]
    (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (f : α ↪ β) (hf : ∀ x y, H.Adj (f x) (f y) ↔ G.Adj x y) (w : β → K) :
    partition H (univ.image f) w = partition G univ (fun x => w (f x)) := by
  classical
  let V := univ.image f
  let e : α ≃ (V : Set β) := Equiv.ofBijective
    (fun x => ⟨f x, Finset.mem_image.mpr ⟨x, mem_univ x, rfl⟩⟩)
    ⟨fun x y h => f.injective (congrArg Subtype.val h), by
      intro y
      obtain ⟨x,hx,he⟩ := Finset.mem_image.mp y.property
      exact ⟨x, Subtype.ext he⟩⟩
  have h := partition_relabel G (H.induce (V : Set β)) e
    (fun x y => hf x y) univ (fun x => w x.val)
  rw [Finset.image_univ_equiv, partition_subtype] at h
  exact h

/-- Separate the last B vertex of the first path and concatenate its even
prefix with the entire second path. -/
def joinEquiv (p q : ℕ) :
    Fin (2 * p + 1) ⊕ Fin (2 * q + 1) ≃
      Fin (2 * p + (2 * q + 1)) ⊕ Fin 1 :=
  (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)).trans
    ((Equiv.sumAssoc _ _ _).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
        ((Equiv.sumAssoc _ _ _).symm.trans
          (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)))))

private lemma join_left (p q : ℕ) (i : Fin (2 * p)) :
    joinEquiv p q (.inl (i.castAdd 1)) =
      .inl (i.castAdd (2 * q + 1)) := by
  simp [joinEquiv]

private lemma join_right (p q : ℕ) (i : Fin (2 * q + 1)) :
    joinEquiv p q (.inr i) = .inl (i.natAdd (2 * p)) := by
  simp [joinEquiv]

private lemma join_isolate (p q : ℕ) :
    joinEquiv p q (.inl (Fin.last (2 * p))) = .inr 0 := by
  simp [joinEquiv]

/-- A complete actual component witness; the residual is the given induced
subgraph on `R`, and its labels are fixed by the coordinate map. -/
structure ActualTwoPaths {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (A B R : Finset α) (p q : ℕ) where
  labels : α ≃ ((Fin (2 * p + 1) ⊕ Fin (2 * q + 1)) ⊕ (R : Set α))
  rest : ∀ r : (R : Set α), labels r.val = .inr r
  adjacency : ∀ x y, G.Adj x y ↔
    (((pathGraph (2 * p + 1)) ⊕g (pathGraph (2 * q + 1))) ⊕g
      (G.induce (R : Set α))).Adj (labels x) (labels y)
  left_A : ∀ i, labels.symm (.inl (.inl i)) ∈ A ↔ Odd i.val
  left_B : ∀ i, labels.symm (.inl (.inl i)) ∈ B ↔ Even i.val
  right_A : ∀ i, labels.symm (.inl (.inr i)) ∈ A ↔ Odd i.val
  right_B : ∀ i, labels.symm (.inl (.inr i)) ∈ B ↔ Even i.val

namespace ActualTwoPaths
variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} {A B R : Finset α} {p q : ℕ}

/-- Coordinates of the new long path, the B isolate, and the untouched R. -/
def afterLabels (w : ActualTwoPaths G A B R p q) :
    α ≃ ((Fin (2 * p + (2 * q + 1)) ⊕ Fin 1) ⊕ (R : Set α)) :=
  w.labels.trans (Equiv.sumCongr (joinEquiv p q) (Equiv.refl _))

/-- The graph after the move has the complete original carrier. -/
def after (w : ActualTwoPaths G A B R p q) : SimpleGraph α :=
  (((pathGraph (2 * p + (2 * q + 1))) ⊕g (pathGraph 1)) ⊕g
    (G.induce (R : Set α))).comap w.afterLabels

/-- The actual embedding of the two shortened paths and the original R. -/
def residualEmbedding (w : ActualTwoPaths G A B R p q) :
    ((Fin (2 * p - 2) ⊕ Fin (2 * q - 2)) ⊕ (R : Set α)) ↪ α :=
  (Function.Embedding.sumMap
    (Function.Embedding.sumMap
      (Fin.castLEEmb (by omega : 2 * p - 2 ≤ 2 * p + 1))
      (Fin.castLEEmb (by omega : 2 * q - 2 ≤ 2 * q + 1)))
    (Function.Embedding.refl _)).trans w.labels.symm.toEmbedding

/-- The residual domain consists of original vertices, with no padding. -/
def residual (w : ActualTwoPaths G A B R p q) : Finset α :=
  univ.image w.residualEmbedding

private lemma residual_adjacency (w : ActualTwoPaths G A B R p q)
    (x y : ((Fin (2 * p - 2) ⊕ Fin (2 * q - 2)) ⊕ (R : Set α))) :
    G.Adj (w.residualEmbedding x) (w.residualEmbedding y) ↔
      (((pathGraph (2 * p - 2)) ⊕g (pathGraph (2 * q - 2))) ⊕g
        (G.induce (R : Set α))).Adj x y := by
  rw [w.adjacency]
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
    simp [residualEmbedding, SimpleGraph.sum_adj, pathGraph_adj]

private lemma residual_card (w : ActualTwoPaths G A B R p q)
    (hp : 1 ≤ p) (hq : 1 ≤ q) :
    w.residual.card + 6 = Fintype.card α := by
  have h := Fintype.card_congr w.labels
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at h
  simp only [residual, Finset.card_image_of_injective _ w.residualEmbedding.injective,
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe]
  omega

private lemma residual_rest (w : ActualTwoPaths G A B R p q) : R ⊆ w.residual := by
  intro r hr
  apply Finset.mem_image.mpr
  refine ⟨.inr ⟨r,hr⟩, mem_univ _, ?_⟩
  change w.labels.symm (.inr ⟨r,hr⟩) = r
  exact w.labels.symm_apply_eq.mpr (w.rest ⟨r,hr⟩).symm

private lemma after_rest (w : ActualTwoPaths G A B R p q) (x y : (R : Set α)) :
    w.after.Adj x.val y.val ↔ G.Adj x.val y.val := by
  simp [after, afterLabels, w.rest, SimpleGraph.comap_adj, SimpleGraph.sum_adj]

end ActualTwoPaths

#print axioms two_path_series_concentration
end D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration
