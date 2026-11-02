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
        exact h (by simpa using hx) (by simpa using hy)
          (by simpa using hn) he
      · intro x hx y hy hn he
        exact h (by simpa using hx) (by simpa using hy)
          (by simpa using hn) he
    · rintro ⟨hs, ht⟩ (x | x) hx (y | y) hy hn he
      · exact hs (by simpa using hx) (by simpa using hy)
          (by simpa using hn) he
      · exact he
      · exact he
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
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hy
      exact hh.2 hx hy (fun h => hn (congrArg Subtype.val h)) he
  · intro S hS T hT he
    exact Finset.image_injective (Subtype.val_injective) he
  · intro S hS
    have hh := Finset.mem_filter.mp hS
    let T : Finset (V : Set α) := S.attach.image
      (fun x => (⟨x.val, (Finset.mem_powerset.mp hh.1) x.property⟩ : (V : Set α)))
    refine ⟨T, Finset.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
    · intro x hx y hy hn he
      obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,hby⟩ := Finset.mem_image.mp hy
      exact hh.2 (by simpa [← hax] using a.property)
        (by simpa [← hby] using b.property) (fun h => hn (Subtype.ext h)) he
    · ext x
      simp [T]
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
  rw [Equiv.image_univ] at hh
  rw [partition_subtype] at hh
  exact hh.symm

#print axioms two_path_series_concentration
end D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration
