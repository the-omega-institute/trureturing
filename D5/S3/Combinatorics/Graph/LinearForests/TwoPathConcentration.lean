/- GID: D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration
   mirror-E: none(waiver:exact-symbolic-configuration-correspondence)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Sum]
   utility: none
   digest: Two actual B-ended paths concentrate on their original labelled bipartition with an exact six-vertex residual and Catalan shift. -/

import D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
import D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan
import D5.S3.StatisticalMechanics.HardCore.PartitionRelabeling
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset PowerSeries
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
namespace D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration

attribute [local instance] Classical.propDecidable

local instance : DecidableRel (SimpleGraph.hasse ℕ).Adj := Classical.decRel _

private lemma localPathAdj (u v : ℕ) :
    (SimpleGraph.hasse ℕ).Adj u v ↔ u + 1 = v ∨ v + 1 = u := by
  simp [SimpleGraph.hasse_adj, ← Order.succ_eq_iff_covBy]

private def localPathSeries (v : ℕ) : PowerSeries ℤ :=
  partition (SimpleGraph.hasse ℕ) (range v) (fun _ => -X)

private lemma localPathZero : localPathSeries 0 = 1 := by
  simp [localPathSeries, partition_empty]

private lemma localPathRec (v : ℕ) :
    localPathSeries (v + 2) = localPathSeries (v + 1) - X * localPathSeries v := by
  have he : (range (v + 2)).erase (v + 1) = range (v + 1) := by
    ext x
    simp only [mem_erase, mem_range]
    omega
  have hc : closedComplement (SimpleGraph.hasse ℕ) (range (v + 2)) (v + 1) =
      range v := by
    ext x
    simp only [closedComplement, mem_filter, mem_erase, mem_range, localPathAdj]
    omega
  simpa [localPathSeries, he, hc, sub_eq_add_neg] using
    partition_delete (SimpleGraph.hasse ℕ) (range (v + 2)) (v + 1)
      (by simp) (fun _ => (-X : PowerSeries ℤ))

private lemma localPathOne : localPathSeries 1 = 1 - X := by
  have he : (range 1).erase 0 = ∅ := by decide
  have hc : closedComplement (SimpleGraph.hasse ℕ) (range 1) 0 = ∅ := by
    simp [closedComplement]
  have hh := partition_delete (SimpleGraph.hasse ℕ) (range 1) 0
    (by simp) (fun _ => (-X : PowerSeries ℤ))
  rw [he, hc, partition_empty] at hh
  simpa [localPathSeries, partition_empty, sub_eq_add_neg] using hh

private def localCatalanIntegerSeries : PowerSeries ℤ :=
  PowerSeries.catalanSeries.map (Nat.castRingHom ℤ)

private lemma localCoeffPartitionPhi {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (V : Finset α) (m : ℕ) (hm : V.card ≤ m) :
    PowerSeries.coeff m (partition G V (fun _ => -PowerSeries.X) * localCatalanIntegerSeries) =
      phi G V m := by
  open PowerSeries in
    unfold partition phi
    rw [Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro S hS
    have hsm : S.card ≤ m := (Finset.card_le_card
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)).trans hm
    have he : (-X : PowerSeries ℤ) ^ S.card = C ((-1 : ℤ) ^ S.card) * X ^ S.card := by
      rw [neg_eq_neg_one_mul, mul_pow]
      simp
    rw [Finset.prod_const, he, mul_assoc, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hsm]
    simp [localCatalanIntegerSeries]

private lemma path_two : localPathSeries 2 = 1 - 2 * X := by
  rw [show 2 = 0 + 2 by omega, localPathRec, localPathOne, localPathZero]
  ring

private lemma path_three : localPathSeries 3 = 1 - 3 * X + X ^ 2 := by
  rw [show 3 = 1 + 2 by omega, localPathRec, path_two, localPathOne]
  ring

private lemma path_four : localPathSeries 4 = 1 - 4 * X + 3 * X ^ 2 := by
  rw [show 4 = 2 + 2 by omega, localPathRec, path_three, path_two]
  ring

private lemma path_five : localPathSeries 5 = 1 - 5 * X + 6 * X ^ 2 - X ^ 3 := by
  rw [localPathRec 3, path_four, path_three]
  ring

private lemma path_six : localPathSeries 6 = 1 - 6 * X + 10 * X ^ 2 - 4 * X ^ 3 := by
  rw [localPathRec 4, path_five, path_four]
  ring

private lemma path_seven : localPathSeries 7 = 1 - 7 * X + 15 * X ^ 2 - 10 * X ^ 3 + X ^ 4 := by
  rw [localPathRec 5, path_six, path_five]
  ring

private lemma two_path_series (n k : ℕ) (hn : 3 ≤ n) (hk : 3 ≤ k) :
    (localPathSeries n * localPathSeries k - localPathSeries (n + k - 1) * localPathSeries 1) =
      X ^ 3 * localPathSeries (n - 3) * localPathSeries (k - 3) := by
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
        rw [← hna, localPathRec (n - 2), hna,
          show n + k - 1 = (n + k - 3) + 2 by omega,
          localPathRec (n + k - 3), show n - 3 = (n - 5) + 2 by omega,
          localPathRec (n - 5)] at ⊢
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
            rw [← hka, localPathRec (k - 2), hka,
              show 3 + k - 1 = k + 2 by omega,
              localPathRec k, show k - 3 = (k - 5) + 2 by omega,
              localPathRec (k - 5)] at ⊢
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
              rw [path_three, path_five, localPathOne, localPathZero]
              ring_nf
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_three, path_four, localPathOne, path_six, localPathZero]
              ring_nf
        · by_cases hk5 : 5 ≤ k
          · have hk2 : 3 ≤ k - 2 := by omega
            have hk1 : 3 ≤ k - 1 := by omega
            have hsum2 : 4 + (k - 2) < 4 + k := by omega
            have hsum1 : 4 + (k - 1) < 4 + k := by omega
            have h₂ := ih (4 + (k - 2)) hsum2 4 (k - 2) (by omega) hk2 rfl
            have h₁ := ih (4 + (k - 1)) hsum1 4 (k - 1) (by omega) hk1 rfl
            have hka : k - 2 + 2 = k := by omega
            rw [← hka, localPathRec (k - 2), hka,
              show 4 + k - 1 = (k + 1) + 2 by omega,
              localPathRec (k + 1), show k - 3 = (k - 5) + 2 by omega,
              localPathRec (k - 5)] at ⊢
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
              rw [path_four, path_three, localPathOne, path_six, localPathZero]
              ring_nf
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_four, localPathOne, path_seven]
              ring_nf

/-- The exact series law behind the two-path concentration move.
The factor `R` is arbitrary, so it may be the actual partition series of any
untouched finite residual graph. -/
private theorem two_path_series_concentration (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (R : PowerSeries ℤ) :
    (localPathSeries (2 * p + 1) * localPathSeries (2 * q + 1) * R -
      localPathSeries (2 * p + 2 * q + 1) * localPathSeries 1 * R) =
      X ^ 3 * localPathSeries (2 * p - 2) * localPathSeries (2 * q - 2) * R := by
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

lemma configurations_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
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
        exact h (x := Sum.inl x) (y := Sum.inl y) (by simpa using hx) (by simpa using hy)
          (by simpa using hn) (by simpa using he)
      · intro x hx y hy hn he
        exact h (x := Sum.inr x) (y := Sum.inr y) (by simpa using hx) (by simpa using hy)
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

lemma partition_sum {α β K : Type*} [DecidableEq α] [DecidableEq β]
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
      exact fun hx => (Finset.mem_powerset.mp hh.1) hx
  · intro S hS
    exact (Finset.prod_image (fun x _ y _ h => Subtype.ext h)).symm

private lemma partition_path (n : ℕ) :
    partition (pathGraph n) univ (fun _ => (-X : PowerSeries ℤ)) = localPathSeries n := by
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
    rw [localPathAdj, pathGraph_adj]
  have hh := partition_relabel (pathGraph n) ((SimpleGraph.hasse ℕ).induce (range n : Set ℕ))
    e he univ (fun _ => (-X : PowerSeries ℤ))
  rw [Finset.image_univ_equiv] at hh
  rw [partition_subtype (SimpleGraph.hasse ℕ) (range n) (fun _ => (-X : PowerSeries ℤ))] at hh
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
  rw [Finset.image_univ_equiv, partition_subtype H V w] at h
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
  left_start : labels.symm (.inl (.inl 0)) ∈ B
  right_start : labels.symm (.inl (.inr 0)) ∈ B

namespace ActualTwoPaths
variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} {A B R : Finset α} {p q : ℕ}

private lemma path_colours (n : ℕ) (f : Fin (n + 1) → α)
    (hf : ∀ i j, (pathGraph (n + 1)).Adj i j → G.Adj (f i) (f j))
    (hA : G.IsIndepSet (A : Set α)) (hB : G.IsIndepSet (B : Set α))
    (hAB : Disjoint A B) (hcover : A ∪ B = univ) (hzero : f 0 ∈ B)
    (i : Fin (n + 1)) : (f i ∈ A ↔ Odd i.val) ∧ (f i ∈ B ↔ Even i.val) := by
  have cover (x : α) : x ∈ A ∨ x ∈ B := by simpa [← hcover] using mem_univ x
  let beta : (pathGraph (n + 1)).Coloring Bool := Coloring.mk
    (fun i => decide (f i ∈ B)) (by
      intro i j hij
      have hadj := hf i j hij
      have hne : f i ≠ f j := hadj.ne
      by_cases hi : f i ∈ B
      · have hj : f j ∉ B := fun hj => hB hi hj hne hadj
        simp [hi, hj]
      · have hiA := (cover (f i)).resolve_right hi
        have hj : f j ∈ B := by
          by_contra hj
          exact hA hiA ((cover (f j)).resolve_right hj) hne hadj
        simp [hi, hj])
  have hbzero : beta 0 = true := by exact decide_eq_true hzero
  have hpzero : (pathGraph.bicoloring (n + 1)) 0 = true := by rfl
  obtain ⟨walk⟩ := (connected_pathGraph_add_one n) 0 i
  have hb := beta.even_length_iff_congr walk
  have ht := (pathGraph.bicoloring (n + 1)).even_length_iff_congr walk
  have hbi : f i ∈ B ↔ Even i.val := by
    have hsame : (beta i : Prop) ↔ ((pathGraph.bicoloring (n + 1)) i : Prop) := by
      simpa only [hbzero, hpzero, Bool.true_eq, true_iff] using hb.symm.trans ht
    change (decide (f i ∈ B) = true) ↔ (decide (i.val % 2 = 0) = true) at hsame
    simpa only [decide_eq_true_eq, ← Nat.even_iff] using hsame
  refine ⟨?_, hbi⟩
  have hab : f i ∈ A ↔ f i ∉ B := by
    constructor
    · intro hi hj; exact disjoint_left.mp hAB hi hj
    · intro hi; exact (cover (f i)).resolve_right hi
  rw [hab, hbi, Nat.not_even_iff_odd]

private lemma left_colours (w : ActualTwoPaths G A B R p q)
    (hA : G.IsIndepSet (A : Set α)) (hB : G.IsIndepSet (B : Set α))
    (hAB : Disjoint A B) (hc : A ∪ B = univ) (i : Fin (2 * p + 1)) :
    (w.labels.symm (.inl (.inl i)) ∈ A ↔ Odd i.val) ∧
    (w.labels.symm (.inl (.inl i)) ∈ B ↔ Even i.val) := by
  apply path_colours (2 * p) (fun j => w.labels.symm (.inl (.inl j)))
    (fun j k hjk => (w.adjacency _ _).mpr (by simpa using hjk)) hA hB hAB hc w.left_start

private lemma right_colours (w : ActualTwoPaths G A B R p q)
    (hA : G.IsIndepSet (A : Set α)) (hB : G.IsIndepSet (B : Set α))
    (hAB : Disjoint A B) (hc : A ∪ B = univ) (i : Fin (2 * q + 1)) :
    (w.labels.symm (.inl (.inr i)) ∈ A ↔ Odd i.val) ∧
    (w.labels.symm (.inl (.inr i)) ∈ B ↔ Even i.val) := by
  apply path_colours (2 * q) (fun j => w.labels.symm (.inl (.inr j)))
    (fun j k hjk => (w.adjacency _ _).mpr (by simpa using hjk)) hA hB hAB hc w.right_start

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


namespace ActualTwoPaths
variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} {A B R : Finset α} {p q : ℕ}

private lemma after_colours (w : ActualTwoPaths G A B R p q)
    (hA : G.IsIndepSet (A : Set α)) (hB : G.IsIndepSet (B : Set α))
    (hAB : Disjoint A B) (hc : A ∪ B = univ)
    (i : Fin (2 * p + (2 * q + 1))) :
    (w.afterLabels.symm (.inl (.inl i)) ∈ A ↔ Odd i.val) ∧
    (w.afterLabels.symm (.inl (.inl i)) ∈ B ↔ Even i.val) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have he : w.afterLabels.symm (.inl (.inl (j.castAdd (2 * q + 1)))) =
        w.labels.symm (.inl (.inl (j.castAdd 1))) := by
      apply w.afterLabels.symm_apply_eq.mpr
      simp [afterLabels, join_left]
    rw [he, (w.left_colours hA hB hAB hc _).1, (w.left_colours hA hB hAB hc _).2]
    simp
  · have he : w.afterLabels.symm (.inl (.inl (j.natAdd (2 * p)))) =
        w.labels.symm (.inl (.inr j)) := by
      apply w.afterLabels.symm_apply_eq.mpr
      simp [afterLabels, join_right]
    rw [he, (w.right_colours hA hB hAB hc _).1, (w.right_colours hA hB hAB hc _).2]
    simp [Nat.odd_iff, Nat.even_iff, Nat.add_mod, Nat.mul_mod]

private lemma after_isolate (w : ActualTwoPaths G A B R p q)
    (hA : G.IsIndepSet (A : Set α)) (hB : G.IsIndepSet (B : Set α))
    (hAB : Disjoint A B) (hc : A ∪ B = univ) (i : Fin 1) :
    w.afterLabels.symm (.inl (.inr i)) ∈ B := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have he : w.afterLabels.symm (.inl (.inr 0)) =
      w.labels.symm (.inl (.inl (Fin.last (2 * p)))) := by
    apply w.afterLabels.symm_apply_eq.mpr
    simp [afterLabels, join_isolate]
  rw [he, (w.left_colours hA hB hAB hc _).2]
  simp [Nat.even_iff]

private lemma after_rest_label (w : ActualTwoPaths G A B R p q) (r : (R : Set α)) :
    w.afterLabels r.val = .inr r := by
  simp [afterLabels, w.rest]

private lemma after_independent (w : ActualTwoPaths G A B R p q)
    (D : Finset α) (hD : G.IsIndepSet (D : Set α)) (t : ℕ)
    (hpar : ∀ i : Fin (2 * p + (2 * q + 1)),
      w.afterLabels.symm (.inl (.inl i)) ∈ D → i.val % 2 = t) :
    w.after.IsIndepSet (D : Set α) := by
  intro x hx y hy hn hxy
  change ((((pathGraph (2 * p + (2 * q + 1))) ⊕g (pathGraph 1)) ⊕g
    (G.induce (R : Set α))).Adj (w.afterLabels x) (w.afterLabels y)) at hxy
  have hx' : w.afterLabels.symm (w.afterLabels x) ∈ D := by simpa using hx
  have hy' : w.afterLabels.symm (w.afterLabels y) ∈ D := by simpa using hy
  rcases hEx : w.afterLabels x with (i | i) | i <;>
    rcases hEy : w.afterLabels y with (j | j) | j
  · rw [hEx] at hx'
    rw [hEy] at hy'
    have hi := hpar i hx'
    have hj := hpar j hy'
    rw [hEx, hEy] at hxy
    have hadj := pathGraph_adj.mp (by simpa using hxy)
    omega
  · simpa [hEx,hEy] using hxy
  · simpa [hEx,hEy] using hxy
  · simpa [hEx,hEy] using hxy
  · have hi : i.val = 0 := by omega
    have hj : j.val = 0 := by omega
    have hadj := pathGraph_adj.mp (by simpa [hEx,hEy] using hxy)
    omega
  · simpa [hEx,hEy] using hxy
  · simpa [hEx,hEy] using hxy
  · simpa [hEx,hEy] using hxy
  · have hxi : x = i.val := w.afterLabels.injective (hEx.trans (w.after_rest_label i).symm)
    have hyj : y = j.val := w.afterLabels.injective (hEy.trans (w.after_rest_label j).symm)
    subst x
    subst y
    exact hD hx hy hn ((w.after_rest i j).mp hxy)

end ActualTwoPaths

private lemma partition_paths {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (a b : ℕ) (T : SimpleGraph ρ) [DecidableRel T.Adj] :
    partition (((pathGraph a) ⊕g (pathGraph b)) ⊕g T) univ
        (fun _ => (-X : PowerSeries ℤ)) =
      localPathSeries a * localPathSeries b * partition T univ (fun _ => -X) := by
  have hu : (univ : Finset ((Fin a ⊕ Fin b) ⊕ ρ)) =
      (univ : Finset (Fin a ⊕ Fin b)).disjSum (univ : Finset ρ) := by
    ext (x | x) <;> simp
  have hu' : (univ : Finset (Fin a ⊕ Fin b)) =
      (univ : Finset (Fin a)).disjSum (univ : Finset (Fin b)) := by
    ext (x | x) <;> simp
  rw [hu, partition_sum, hu', partition_sum, partition_path, partition_path]

namespace ActualTwoPaths
variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} {A B R : Finset α} {p q : ℕ}

private lemma before_partition (w : ActualTwoPaths G A B R p q) :
    partition G univ (fun _ => (-X : PowerSeries ℤ)) =
      localPathSeries (2 * p + 1) * localPathSeries (2 * q + 1) *
        partition G R (fun _ => -X) := by
  have h := partition_relabel
    (((pathGraph (2 * p + 1)) ⊕g (pathGraph (2 * q + 1))) ⊕g
      (G.induce (R : Set α))) G w.labels.symm
    (fun x y => by simpa using w.adjacency (w.labels.symm x) (w.labels.symm y))
    univ (fun _ => (-X : PowerSeries ℤ))
  rw [Finset.image_univ_equiv, partition_paths, partition_subtype G R (fun _ => (-X : PowerSeries ℤ))] at h
  exact h

private lemma after_partition (w : ActualTwoPaths G A B R p q) :
    partition w.after univ (fun _ => (-X : PowerSeries ℤ)) =
      localPathSeries (2 * p + (2 * q + 1)) * localPathSeries 1 *
        partition G R (fun _ => -X) := by
  have h := partition_relabel
    (((pathGraph (2 * p + (2 * q + 1))) ⊕g (pathGraph 1)) ⊕g
      (G.induce (R : Set α))) w.after w.afterLabels.symm
    (fun x y => by simp [after, SimpleGraph.comap_adj])
    univ (fun _ => (-X : PowerSeries ℤ))
  rw [Finset.image_univ_equiv, partition_paths, partition_subtype G R (fun _ => (-X : PowerSeries ℤ))] at h
  exact h

private lemma residual_partition (w : ActualTwoPaths G A B R p q) :
    partition G w.residual (fun _ => (-X : PowerSeries ℤ)) =
      localPathSeries (2 * p - 2) * localPathSeries (2 * q - 2) *
        partition G R (fun _ => -X) := by
  have h := partition_embedding
    (((pathGraph (2 * p - 2)) ⊕g (pathGraph (2 * q - 2))) ⊕g
      (G.induce (R : Set α))) G w.residualEmbedding
    (fun x y => w.residual_adjacency x y) (fun _ => (-X : PowerSeries ℤ))
  rw [partition_paths, partition_subtype G R (fun _ => (-X : PowerSeries ℤ))] at h
  exact h

end ActualTwoPaths

namespace ActualTwoPaths
variable {α : Type*} [Fintype α] [DecidableEq α]
  {G : SimpleGraph α} {A B R : Finset α} {p q : ℕ}

private lemma phi_difference (w : ActualTwoPaths G A B R p q)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (m : ℕ) (hm : Fintype.card α ≤ m) :
    phi G univ m - phi w.after univ m = phi G w.residual (m - 3) := by
  open D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan in
    have hc := w.residual_card hp hq
    have hm3 : 3 ≤ m := by omega
    have hr : w.residual.card ≤ m - 3 := by omega
    have hs : partition G univ (fun _ => (-X : PowerSeries ℤ)) -
        partition w.after univ (fun _ => (-X : PowerSeries ℤ)) =
        X ^ 3 * partition G w.residual (fun _ => (-X : PowerSeries ℤ)) := by
      rw [w.before_partition, w.after_partition, w.residual_partition]
      simpa only [Nat.add_assoc, mul_assoc] using
        two_path_series_concentration p q hp hq (partition G R (fun _ => (-X : PowerSeries ℤ)))
    have ht := congrArg (fun F : PowerSeries ℤ => coeff m (F * localCatalanIntegerSeries)) hs
    rw [sub_mul, map_sub,
      localCoeffPartitionPhi G univ m (by simpa using hm),
      localCoeffPartitionPhi w.after univ m (by simpa using hm)] at ht
    rw [mul_assoc, coeff_X_pow_mul', if_pos hm3,
      localCoeffPartitionPhi G w.residual (m - 3) hr] at ht
    exact ht

end ActualTwoPaths

/-- A concentration move on the complete actual carrier with its original
bipartition, an induced residual of exactly six fewer vertices, and the exact
signed-Catalan shift. The equality permits arbitrary residual graphs. -/
theorem actual_two_path_concentration {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (A B R : Finset α)
    (hA : G.IsIndepSet (A : Set α)) (hB : G.IsIndepSet (B : Set α))
    (hAB : Disjoint A B) (hcover : A ∪ B = univ)
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (w : ActualTwoPaths G A B R p q) (m : ℕ) (hm : Fintype.card α ≤ m) :
    (∀ x y, w.after.Adj x y ↔
      (((pathGraph (2 * p + (2 * q + 1))) ⊕g (pathGraph 1)) ⊕g
        (G.induce (R : Set α))).Adj (w.afterLabels x) (w.afterLabels y)) ∧
    (∀ r : (R : Set α), w.afterLabels r.val = .inr r) ∧
    (∀ i : Fin (2 * p + (2 * q + 1)),
      (w.afterLabels.symm (.inl (.inl i)) ∈ A ↔ Odd i.val) ∧
      (w.afterLabels.symm (.inl (.inl i)) ∈ B ↔ Even i.val)) ∧
    (∀ i : Fin 1, w.afterLabels.symm (.inl (.inr i)) ∈ B) ∧
    w.after.IsIndepSet (A : Set α) ∧ w.after.IsIndepSet (B : Set α) ∧
    (∀ x y : (R : Set α), w.after.Adj x.val y.val ↔ G.Adj x.val y.val) ∧
    w.residual.card + 6 = Fintype.card α ∧ R ⊆ w.residual ∧
    (∀ x y : ((Fin (2 * p - 2) ⊕ Fin (2 * q - 2)) ⊕ (R : Set α)),
      G.Adj (w.residualEmbedding x) (w.residualEmbedding y) ↔
        (((pathGraph (2 * p - 2)) ⊕g (pathGraph (2 * q - 2))) ⊕g
          (G.induce (R : Set α))).Adj x y) ∧
    configurations G univ =
      (configurations (((pathGraph (2 * p + 1)) ⊕g (pathGraph (2 * q + 1))) ⊕g
        (G.induce (R : Set α))) univ).image (Finset.image w.labels.symm) ∧
    configurations w.after univ =
      (configurations (((pathGraph (2 * p + (2 * q + 1))) ⊕g (pathGraph 1)) ⊕g
        (G.induce (R : Set α))) univ).image (Finset.image w.afterLabels.symm) ∧
    phi G univ m - phi w.after univ m = phi G w.residual (m - 3) ∧
    ((G.induce (w.residual : Set α)).IsAcyclic →
      (∀ x : (w.residual : Set α), (G.induce (w.residual : Set α)).degree x ≤ 2) →
      0 ≤ phi G univ m - phi w.after univ m) := by
  have hdiff := w.phi_difference hp hq m hm
  refine ⟨fun _ _ => Iff.rfl, w.after_rest_label, w.after_colours hA hB hAB hcover, w.after_isolate hA hB hAB hcover,
    w.after_independent A hA 1 ?_, w.after_independent B hB 0 ?_,
    w.after_rest, w.residual_card hp hq, w.residual_rest, w.residual_adjacency,
    ?_, ?_, hdiff, ?_⟩
  · intro i hi
    exact Nat.odd_iff.mp ((w.after_colours hA hB hAB hcover i).1.mp hi)
  · intro i hi
    exact Nat.even_iff.mp ((w.after_colours hA hB hAB hcover i).2.mp hi)
  · have h := configurations_relabel
      (((pathGraph (2 * p + 1)) ⊕g (pathGraph (2 * q + 1))) ⊕g
        (G.induce (R : Set α))) G w.labels.symm
      (fun x y => by simpa using w.adjacency (w.labels.symm x) (w.labels.symm y)) univ
    simpa only [Finset.image_univ_equiv] using h
  · have h := configurations_relabel
      (((pathGraph (2 * p + (2 * q + 1))) ⊕g (pathGraph 1)) ⊕g
        (G.induce (R : Set α))) w.after w.afterLabels.symm
      (fun x y => by simp [ActualTwoPaths.after, SimpleGraph.comap_adj]) univ
    simpa only [Finset.image_univ_equiv] using h
  · intro ha hd
    rw [hdiff, ← D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan.phi_subtype]
    apply D5.S3.Combinatorics.Graph.LinearForests.FiniteForestCatalan.finite_forest_phi_nonnegative
      (G.induce (w.residual : Set α)) ha hd (m - 3)
    have hc := w.residual_card hp hq
    simpa only [SetLike.coe_sort_coe, Fintype.card_coe] using
      (show w.residual.card ≤ m - 3 by omega)

#print axioms actual_two_path_concentration

end D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration
