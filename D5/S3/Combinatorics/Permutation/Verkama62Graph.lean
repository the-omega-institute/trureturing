/- GID: D5/S3/Combinatorics/Permutation/Verkama62Graph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/Verkama62Graph
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordinary deletion connectivity gives an anchored triangle or square in an inversion graph. -/

import D5.S3.Combinatorics.Permutation.Verkama62Representation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The source graph is labelled by values, with the sign product evaluated in the integers. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.Verkama62Local

/-- The value-labelled inversion graph. A value and a position represented by
    `i : Fin n` denote the source label `i.val + 1`. -/
def valueGraph {n : ℕ} (π : Equiv.Perm (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := (((u.val : ℤ) + 1) - ((v.val : ℤ) + 1)) *
    ((((π.symm u).val : ℤ) + 1) - (((π.symm v).val : ℤ) + 1)) < 0
  symm := ⟨by
    intro u v h
    have heq : (((v.val : ℤ) + 1) - ((u.val : ℤ) + 1)) *
        ((((π.symm v).val : ℤ) + 1) - (((π.symm u).val : ℤ) + 1)) =
        (((u.val : ℤ) + 1) - ((v.val : ℤ) + 1)) *
        ((((π.symm u).val : ℤ) + 1) - (((π.symm v).val : ℤ) + 1)) := by ring
    rwa [heq]⟩
  loopless := ⟨by intro u; simp⟩

theorem value_adj {n : ℕ} (π : Equiv.Perm (Fin n)) (u v : Fin n) :
    (valueGraph π).Adj u v ↔
      (u < v ∧ π.symm v < π.symm u) ∨ (v < u ∧ π.symm u < π.symm v) := by
  change (((u.val : ℤ) + 1) - ((v.val : ℤ) + 1)) *
    ((((π.symm u).val : ℤ) + 1) - (((π.symm v).val : ℤ) + 1)) < 0 ↔ _
  rw [mul_neg_iff]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · right; constructor <;> omega
    · left; constructor <;> omega
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · right; constructor <;> omega
    · left; constructor <;> omega

private theorem two_neighbours {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 3 ≤ n)
    (hconn : G.Connected) (hdelete : ∀ v, (G.induce {v}ᶜ).Connected) (v : Fin n) :
    ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  classical
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨a, ha⟩ := hconn.preconnected.exists_adj_of_nontrivial v
  have hcard : ({v, a} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have hpair := Finset.card_le_two (a := v) (b := a)
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  let v' : {w : Fin n // w ∈ ({a}ᶜ : Set (Fin n))} := ⟨v, by simpa using ha.ne⟩
  let b' : {w : Fin n // w ∈ ({a}ᶜ : Set (Fin n))} := ⟨b, by simpa using hb.2⟩
  letI : Nontrivial {w : Fin n // w ∈ ({a}ᶜ : Set (Fin n))} :=
    ⟨⟨v', b', by intro h; exact hb.1 (congrArg Subtype.val h).symm⟩⟩
  obtain ⟨c, hc⟩ := (hdelete a).preconnected.exists_adj_of_nontrivial v'
  have hca : c.val ≠ a := fun h => c.property (Set.mem_singleton_iff.mpr h)
  exact ⟨a, c.val, hca.symm, ha, hc⟩

/-- Every ordinarily vertex-2-connected inversion graph has an initial triangle
    or 3412 containing the original leftmost and bottommost points. -/
theorem anchored_start {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 3 ≤ n)
    (hconn : (valueGraph π).Connected)
    (hdelete : ∀ v, ((valueGraph π).induce {v}ᶜ).Connected) :
    ∃ S : Finset (Fin n), EarRun π S ∧
      (⟨0, by omega⟩ : Fin n) ∈ S ∧ π.symm ⟨0, by omega⟩ ∈ S := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let i := π.symm z
  have hz (v : Fin n) : z ≤ v := by change 0 ≤ v.val; omega
  have hzπ : π i = z := π.apply_symm_apply z
  have hfirst : 2 ≤ (π z).val := by
    obtain ⟨a, b, hab, ha, hb⟩ := two_neighbours (valueGraph π) hn hconn hdelete (π z)
    rw [value_adj] at ha hb
    simp only [Equiv.symm_apply_apply] at ha hb
    have hal : a < π z := by rcases ha with ha | ha <;> have := hz (π.symm a) <;> omega
    have hbl : b < π z := by rcases hb with hb | hb <;> have := hz (π.symm b) <;> omega
    by_contra h
    have heq : a = b := Fin.ext (by omega)
    exact hab heq
  have hbottom : 2 ≤ i.val := by
    obtain ⟨a, b, hab, ha, hb⟩ := two_neighbours (valueGraph π) hn hconn hdelete z
    rw [value_adj] at ha hb
    have hal : π.symm a < i := by rcases ha with ha | ha <;> have := hz a <;> omega
    have hbl : π.symm b < i := by rcases hb with hb | hb <;> have := hz b <;> omega
    by_contra h
    have heq : π.symm a = π.symm b := Fin.ext (by omega)
    exact hab (π.symm.injective heq)
  by_cases hex : ∃ j : Fin n, z < j ∧ j < i ∧ z < π j ∧ π j < π z
  · obtain ⟨j, hzj, hji, hvj, hjv⟩ := hex
    exact ⟨{z, j, i}, EarRun.triangle z j i hzj hji hjv (hzπ ▸ hvj),
      by simp [z], by simp [i, z]⟩
  · have ho : z < o := by change 0 < 1; omega
    have hoi : o < i := by change 1 < i.val; omega
    have hzo : z < π o := by
      have hne : π o ≠ z := by
        intro h
        have heq : o = i := π.injective (h.trans hzπ.symm)
        exact (ne_of_lt hoi) heq
      have := hz (π o)
      exact lt_of_le_of_ne this hne.symm
    have htop : π z < π o := by
      have hne : π o ≠ π z := π.injective.ne (ne_of_gt ho)
      by_contra h
      exact hex ⟨o, ho, hoi, hzo, lt_of_le_of_ne (le_of_not_gt h) hne⟩
    let k := π.symm o
    have hk : π k = o := π.apply_symm_apply o
    have hzk : z < k := by
      have hne : k ≠ z := by
        intro h
        have := congrArg π h
        rw [hk] at this
        change (o : Fin n) = π z at this
        have : o.val = (π z).val := congrArg Fin.val this
        change 1 = (π z).val at this
        omega
      exact lt_of_le_of_ne (hz k) hne.symm
    have hik : i < k := by
      have hne : k ≠ i := by
        intro h
        have := congrArg π h
        rw [hk, hzπ] at this
        exact (ne_of_gt ho) this
      by_contra h
      have hki : k < i := lt_of_le_of_ne (le_of_not_gt h) hne
      have hov : o < π z := by change 1 < (π z).val; omega
      exact hex ⟨k, hzk, hki, hk ▸ ho, hk ▸ hov⟩
    have hov : o < π z := by change 1 < (π z).val; omega
    refine ⟨{z, o, i, k}, EarRun.square z o i k ho hoi hik ?_ ?_ htop,
      by simp [z], by simp [i, z]⟩
    · rw [hzπ, hk]; exact ho
    · rw [hk]; exact hov

end D5.S3.Combinatorics.Permutation.Verkama62Local
