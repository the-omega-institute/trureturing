/- GID: D5/S3/Geometry/Hyperideal/CycleDegreeElevenObstruction
   generality: G
   mirror-B: none(waiver:cycle-degree-eleven-topological-obstruction)
   mirror-E: none(waiver:finite-center-link-count)
   anchors: []
   utility: none
   digest: The role-homogeneous pure three-cycle degree-(8,11) center-link count forces 88-divisibility. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.CycleDegreeElevenObstruction

/-- Integer data for one center-link component of a role-homogeneous
pure three-cycle packet with degree-eight low edges and degree-eleven high
edges. -/
structure CenterLinkComponent where
  tetrahedra : ℕ
  edgeCount : ℕ
  highVertices : ℕ
  genus : ℕ
  edge_balance : 2 * edgeCount = 3 * tetrahedra
  high_balance : 11 * highVertices = 3 * tetrahedra
  euler :
    (highVertices : ℤ) - (edgeCount : ℤ) + (tetrahedra : ℤ) =
      2 - 2 * (genus : ℤ)

/-- A finite collection of center-link components, together with the global
low-edge count. The component decomposition makes the global divisibility
statement apply even when the center link is disconnected. -/
structure PureCycleInventory where
  Component : Type
  finiteComponent : Fintype Component
  data : Component → CenterLinkComponent
  tetrahedra : ℕ
  lowEdges : ℕ
  total_eq : tetrahedra = ∑ i : Component, (data i).tetrahedra
  low_edge_balance : 8 * lowEdges = 3 * tetrahedra

/-- One degree-(8,11) center-link component has the exact genus-deficit
shape and its tetrahedron count is divisible by 44. -/
theorem component_shape_and_div44 (d : CenterLinkComponent) :
    5 * d.tetrahedra = 44 * (d.genus - 1) ∧ 44 ∣ d.tetrahedra := by
  have hE : 2 * (d.edgeCount : ℤ) = 3 * (d.tetrahedra : ℤ) := by
    exact_mod_cast d.edge_balance
  have hV : 11 * (d.highVertices : ℤ) = 3 * (d.tetrahedra : ℤ) := by
    exact_mod_cast d.high_balance
  have hN : 5 * (d.tetrahedra : ℤ) = 44 * (d.genus : ℤ) - 44 := by
    linarith [d.euler, hE, hV]
  have hg : 1 ≤ d.genus := by
    omega
  have hN' : 5 * d.tetrahedra = 44 * (d.genus - 1) := by
    apply Int.ofNat_inj.mp
    norm_num [Nat.cast_mul, Nat.cast_sub hg]
    linarith [hN]
  have h44mul : 44 ∣ 5 * d.tetrahedra := by
    exact ⟨d.genus - 1, hN'⟩
  have h44mul' : 44 ∣ d.tetrahedra * 5 := by
    simpa [Nat.mul_comm] using h44mul
  have h44 : 44 ∣ d.tetrahedra := by
    exact (Nat.Coprime.dvd_of_dvd_mul_right
      (show Nat.Coprime 44 5 by norm_num) h44mul')
  exact ⟨hN', h44⟩

/-- A role-homogeneous pure three-cycle inventory with low degree eight and
high degree eleven has global tetrahedron count divisible by 88. -/
theorem inventory_tetrahedra_div88 (inv : PureCycleInventory) :
    (∀ i : inv.Component,
      5 * (inv.data i).tetrahedra = 44 * ((inv.data i).genus - 1) ∧
        44 ∣ (inv.data i).tetrahedra) ∧
      88 ∣ inv.tetrahedra := by
  letI : Fintype inv.Component := inv.finiteComponent
  have hcomponent (i : inv.Component) :
      5 * (inv.data i).tetrahedra = 44 * ((inv.data i).genus - 1) ∧
        44 ∣ (inv.data i).tetrahedra :=
    component_shape_and_div44 (inv.data i)
  have h44sum : 44 ∣ ∑ i : inv.Component, (inv.data i).tetrahedra := by
    apply Finset.dvd_sum
    intro i hi
    exact (hcomponent i).2
  have h44 : 44 ∣ inv.tetrahedra := by
    rw [inv.total_eq]
    exact h44sum
  have h8mul : 8 ∣ 3 * inv.tetrahedra := by
    exact ⟨inv.lowEdges, inv.low_edge_balance.symm⟩
  have h8mul' : 8 ∣ inv.tetrahedra * 3 := by
    simpa [Nat.mul_comm] using h8mul
  have h8 : 8 ∣ inv.tetrahedra := by
    exact (Nat.Coprime.dvd_of_dvd_mul_right
      (show Nat.Coprime 8 3 by norm_num) h8mul')
  have h88 : Nat.lcm 44 8 ∣ inv.tetrahedra :=
    Nat.lcm_dvd h44 h8
  refine ⟨hcomponent, ?_⟩
  have hlcm : Nat.lcm 44 8 = 88 := by norm_num
  rw [hlcm] at h88
  exact h88

#print axioms component_shape_and_div44
#print axioms inventory_tetrahedra_div88

end D5.S3.Geometry.Hyperideal.CycleDegreeElevenObstruction
