import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9Residual252Certificate
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoExtension
import Batteries.Tactic.OpenPrivate

/-! Transport the cardinality certificate from the orbit counts back to
subsets of the residual cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9Residual252Bound

open Finset

private theorem orbit_rows {V : Type*} {n m : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (R S : Finset V) (hS : S ⊆ R)
    (hdeg : ∀ v ∈ S, (S.filter (G.Adj v)).card ≤ 3)
    (label : V → Fin n) (rowPart : Fin m → Fin n) (d : Fin m → ℤ)
    (a : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (sizes : Fin n → ℤ)
    (hsize : ∀ j, ((R.filter fun v => label v = j).card : ℤ) = sizes j)
    (hdegree : ∀ i v, v ∈ R → label v = rowPart i → ((R.filter (G.Adj v)).card : ℤ) = d i)
    (hcoef : ∀ i v, v ∈ R →
      ((R.filter fun u => label u = rowPart i ∧ G.Adj v u).card : ℤ) +
        (if label v = rowPart i then d i - 3 else 0) = a i (label v))
    (hrhs : ∀ i, d i * sizes (rowPart i) = b i) :
    ∃ x : Fin n → ℤ, (∑ j, x j) = S.card ∧
      (∀ j, 0 ≤ x j) ∧ (∀ j, x j ≤ sizes j) ∧
        ∀ i, (∑ j, a i j * x j) ≤ b i := by
  classical
  let part (j : Fin n) := R.filter fun v => label v = j
  let z (v : V) : ℤ := if v ∈ S then 1 else 0
  let x (j : Fin n) : ℤ := ∑ v ∈ part j, z v
  have hselected (T : Finset V) : (∑ v ∈ T, z v) = (T.filter (· ∈ S)).card :=
    sum_boole (· ∈ S) T
  have htotal : (∑ j, x j) = S.card := by
    change (∑ j, ∑ v ∈ R with label v = j, z v) = _
    have hf : R.filter (· ∈ S) = S := by
      ext v
      exact mem_filter.trans ⟨And.right, fun h => ⟨hS h, h⟩⟩
    rw [sum_fiberwise R label z, hselected, hf]
  refine ⟨x, htotal, (fun j => by rw [show x j = _ from hselected (part j)]; positivity), ?_, ?_⟩
  · intro j
    rw [← hsize]
    change (∑ v ∈ part j, z v) ≤ _
    rw [hselected]
    exact_mod_cast card_le_card (filter_subset (· ∈ S) (part j))
  · intro i
    let c := rowPart i
    let coeff (v : V) : ℤ := if label v = c then d i - 3 else 0
    have hneighbors (T : Finset V) (v : V) :
        ((T.filter (G.Adj v)).card : ℤ) = ∑ u ∈ T, if G.Adj v u then 1 else 0 :=
      (sum_boole (G.Adj v) T).symm
    have hlocal (v : V) (hv : v ∈ part c) :
        (d i - 3) * z v + (∑ u ∈ R, if G.Adj v u then z u else 0) ≤ d i := by
      obtain ⟨hvR, hlabel⟩ := mem_filter.mp hv
      have hdi := hdegree i v hvR hlabel
      change label v = rowPart i at hlabel
      by_cases hvS : v ∈ S
      · have hf : (R.filter (G.Adj v)).filter (· ∈ S) = S.filter (G.Adj v) := by
          ext u
          simp only [mem_filter]
          exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hS h.1, h.2⟩, h.1⟩⟩
        rw [← sum_filter, hselected, hf]
        simp only [z, ite_eq_left hvS, mul_one]
        have hs' : ((S.filter (G.Adj v)).card : ℤ) ≤ 3 := by exact_mod_cast hdeg v hvS
        omega
      · simp only [z, ite_eq_right hvS, mul_zero, zero_add]
        rw [← hdi, hneighbors]
        apply sum_le_sum
        intro u _
        by_cases h : G.Adj v u
        · simp only [ite_eq_left h]
          split <;> decide
        · simp [h]
    have hterm (v : V) (hv : v ∈ R) :
        a i (label v) * z v =
          coeff v * z v + ∑ u ∈ part c, if G.Adj u v then z v else 0 := by
      have hf : (R.filter fun u => label u = rowPart i ∧ G.Adj v u) =
          (part c).filter (fun u => G.Adj u v) := by
        ext u
        simp only [part, c, mem_filter]
        exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2.symm⟩, fun h => ⟨h.1.1, h.1.2, h.2.symm⟩⟩
      rw [← hcoef i v hv, hf, ← sum_filter, sum_const, nsmul_eq_mul]
      change (_ + coeff v) * z v = _
      ring
    have hsum : (∑ j, a i j * x j) = ∑ v ∈ R, a i (label v) * z v := by
      change (∑ j, a i j * ∑ v ∈ R with label v = j, z v) = _
      simp_rw [mul_sum]
      rw [← sum_fiberwise R label (fun v => a i (label v) * z v)]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro v hv
      rw [(mem_filter.mp hv).2]
    have hdiag : (∑ v ∈ R, coeff v * z v) = ∑ v ∈ part c, (d i - 3) * z v := by
      simp only [coeff, ite_mul, zero_mul, part, sum_filter]
    rw [hsum]
    calc
      (∑ v ∈ R, a i (label v) * z v) =
          (∑ v ∈ part c, (d i - 3) * z v) +
            ∑ u ∈ part c, ∑ v ∈ R, if G.Adj u v then z v else 0 := by
        rw [← hdiag, sum_comm (s := part c), ← sum_add_distrib]
        exact sum_congr rfl hterm
      _ = ∑ u ∈ part c, ((d i - 3) * z u + ∑ v ∈ R, if G.Adj u v then z v else 0) := by
        rw [sum_add_distrib]
      _ ≤ ∑ _u ∈ part c, d i := sum_le_sum hlocal
      _ = b i := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
        exact (congrArg (d i * ·) (hsize c)).trans (hrhs i)

open Q9Residual252Certificate (matrix rhs orbitSizes orbit_total_lt)
open Q9GrayCrossedPlacement (cube)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open private adjacent adjacent_iff toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private fastCube from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoExtension

private abbrev Vertex := BitVec 9

private instance : Fintype Vertex :=
  Fintype.ofEquiv (Fin (2 ^ 9)) (BitVec.equivFin (m := 9)).toEquiv.symm

private instance : DecidableRel fastCube.Adj := fun x y =>
  inferInstanceAs (Decidable (adjacent x y = true))

private def countAround (P : Vertex → Prop) [DecidablePred P] (v : Vertex) : ℕ :=
  (univ.filter fun i : Fin 9 => P (toggle v i)).card

private theorem countAround_eq (P : Vertex → Prop) [DecidablePred P] (v : Vertex) :
    (univ.filter fun u => P u ∧ fastCube.Adj v u).card = countAround P v := by
  have hinj : Function.Injective (toggle v) := by
    intro i j h
    have he := (BitVec.xor_right_inj v).mp h
    have hpow : ∀ (a b : Fin 9),
        BitVec.ofNat 9 (2 ^ a.val) = BitVec.ofNat 9 (2 ^ b.val) → a = b := by
      decide +kernel
    exact hpow i j he
  let e : Fin 9 ↪ Vertex := ⟨toggle v, hinj⟩
  unfold countAround
  rw [← card_map e]
  apply congrArg Finset.card
  ext u
  rw [mem_filter, mem_map]
  constructor
  · rintro ⟨_, hP, ha⟩
    obtain ⟨i, hi⟩ := adjacent_exists_flip ((adjacent_iff v u).mp ha)
    have he : e i = u := by
      apply (cubeBitVec 9).injective
      change cubeBitVec 9 (toggle v i) = _
      rw [toggle, cubeBitVec_xor_single, hi]
      rfl
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, show P (e i) from he.symm ▸ hP⟩, he⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨mem_univ _, (mem_filter.mp hi).2, (adjacent_iff _ _).mpr ?_⟩
    change (hypercube 9).Adj (cubeBitVec 9 v) (cubeBitVec 9 (toggle v i))
    rw [toggle, cubeBitVec_xor_single]
    exact BalancedCriticalSpectrum.flip_adj _ _

private def digit (width packed i : ℕ) : ℕ :=
  (packed >>> (width * i)) &&& ((1 <<< width) - 1)

private def supportMask : ℕ :=
    0x20a00888022a7cc0100004003d00004030d00cc4033d |||
    (0x8002a00008020a00888022aa880200008002a000080 <<< 176) |||
    (0xa8802000 <<< 352)

/-- The representative whose closed neighborhood leaves 252 vertices. -/
def support : Finset Vertex :=
  univ.filter fun v => supportMask.testBit v.toNat

private def residual : Finset Vertex :=
  univ.filter fun v => v ∉ support ∧ ∀ i : Fin 9, toggle v i ∉ support

private def inResidual (v : Vertex) : Bool :=
  (((0x577fdffff7ffd5ffff7fdf5ff777fdd50117455f517740d557174d057111d440 <<< 256) |||
    0x117455f517740d557174d057111d4400003822f823b00c2832b0c023002c000) : ℕ).testBit v.toNat

set_option maxRecDepth 4096 in
private theorem mem_residual : ∀ v : Vertex, v ∈ residual ↔ inResidual v = true := by
  decide +kernel

private def labelCode : ℕ :=
    0x3baebaebaebaebae0ae040baebaebaebaebaebaebae |||
    (0xe248bae1ee1ee185baebae103baebaebaebae0aebae1 <<< 176) |||
    (0xbae2481ee185baebaebaebae103baebae0ae2aebaeba <<< 352) |||
    (0xaebae30b2aebaebae1eebae1ee2481852aebaebae1ee <<< 528) |||
    (0xeb8f00eb8db8dbaeb8dbaebaebaebaebaebaebaebaeb <<< 704) |||
    (0xb92bae0d1b90baebaeb90b8fb920d1baeb90baeb90ba <<< 880) |||
    (0xaebaebae0d1b90b90b8fb97b96b96215baeb94b94153 <<< 1056) |||
    (0x6b94b96b94215153b97b96baeb94b96215b94153b92b <<< 1232) |||
    (0xb8dbaebaebaebaebaebaeb99baeb99b992d8b97baeb9 <<< 1408) |||
    (0xaeb90b8fb920d1baeb90baeb90baeb8f00eb8db8dbae <<< 1584) |||
    (0xb8fb97b96b96215baeb94b94153b92bae0d1b90baeb <<< 1760) |||
    (0xb97b96baeb94b96215b94153b92baebaebae0d1b90b9 <<< 1936) |||
    (0xaebaeb99baeb99b992d8b97baeb96b94b96b94215153 <<< 2112) |||
    (0x1420ba1420b9f3de39d35c35cb9b35cb9bb9bb9abaeb <<< 2288) |||
    (0xba65255254e44a3ba1462420ba1b9f4203de4a3462ba <<< 2464) |||
    (0x675254e44a3ba1ba1b9f4624204203de5e95a85a8567 <<< 2640) |||
    (0xb62a5e9ba65a85255a85255674e45e95a8ba65255a85 <<< 2816) |||
    (0xbadbacbac66bbac66b66 <<< 2992)

private def label (v : Vertex) : Fin 46 :=
  Fin.ofNat 46 (digit 6 labelCode v.toNat)

private def center (i : Fin 38) : Fin 46 :=
  Fin.ofNat 46 (digit 6 (0x648e28607de75c6da6585d65544d24503ce30b248185 |||
    (0xb6caeaa689e69 <<< 176)) i.val)

private def degree (i : Fin 38) : ℤ :=
  digit 4 (0x66999996999969699966595595959559664495) i.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check orbit sizes and each local degree and neighbor count.
private theorem geometry :
    support.card = 72 ∧
    (∀ j, ((residual.filter fun v => label v = j).card : ℤ) = orbitSizes j) ∧
    (∀ i v, inResidual v = true → label v = center i →
      (countAround (fun u => inResidual u = true) v : ℤ) = degree i) ∧
    (∀ i v, inResidual v = true →
      (countAround (fun u => inResidual u = true ∧ label u = center i) v : ℤ) +
        (if label v = center i then degree i - 3 else 0) = matrix i (label v)) ∧
    (∀ i, degree i * orbitSizes (center i) = rhs i) := by
  decide +kernel

private theorem residual_card_lt (S : Finset Vertex) (hS : S ⊆ residual)
    (hdeg : ∀ v ∈ S, (S.filter (fastCube.Adj v)).card ≤ 3) : S.card < 186 := by
  obtain ⟨_, hsize, hdegree, hcoef, hrhs⟩ := geometry
  have hdegree' (i : Fin 38) (v : Vertex) (hv : v ∈ residual) (hl : label v = center i) :
      ((residual.filter (fastCube.Adj v)).card : ℤ) = degree i := by
    have he : residual.filter (fastCube.Adj v) =
        univ.filter (fun u => u ∈ residual ∧ fastCube.Adj v u) := by ext u; simp
    rw [he, countAround_eq]
    have hfilter : (univ.filter fun j : Fin 9 => toggle v j ∈ residual) =
        univ.filter (fun j => inResidual (toggle v j) = true) :=
      filter_congr fun j _ => mem_residual (toggle v j)
    unfold countAround
    rw [hfilter]
    exact hdegree i v ((mem_residual v).mp hv) hl
  have hcoef' (i : Fin 38) (v : Vertex) (hv : v ∈ residual) :
      ((residual.filter fun u => label u = center i ∧ fastCube.Adj v u).card : ℤ) +
        (if label v = center i then degree i - 3 else 0) = matrix i (label v) := by
    have he : (residual.filter fun u => label u = center i ∧ fastCube.Adj v u) =
        univ.filter (fun u => (u ∈ residual ∧ label u = center i) ∧ fastCube.Adj v u) := by
      ext u
      simp [and_assoc]
    rw [he, countAround_eq]
    have hfilter : (univ.filter fun j : Fin 9 =>
        toggle v j ∈ residual ∧ label (toggle v j) = center i) =
        univ.filter (fun j => inResidual (toggle v j) = true ∧ label (toggle v j) = center i) :=
      filter_congr fun j _ => and_congr_left' (mem_residual (toggle v j))
    unfold countAround
    rw [hfilter]
    exact hcoef i v ((mem_residual v).mp hv)
  obtain ⟨x, hsum, hlo, hhi, hrows⟩ :=
    orbit_rows fastCube residual S hS hdeg label center degree matrix rhs orbitSizes
      hsize hdegree' hcoef' hrhs
  have h := orbit_total_lt x hlo hhi hrows
  rw [hsum] at h
  exact_mod_cast h

/-- A degree-three induced graph containing the representative as a
component has at most 257 vertices. -/
theorem card_le_of_closed_support (U : Finset Vertex) (hU : support ⊆ U)
    (hclosed : ∀ x ∈ support, ∀ y ∈ U, cube.Adj x y → y ∈ support)
    (hdeg : ∀ v ∈ U, (U.filter (cube.Adj v)).card ≤ 3) : U.card ≤ 257 := by
  have hsub : U \ support ⊆ residual := by
    intro x hx
    obtain ⟨hxU, hxS⟩ := mem_sdiff.mp hx
    refine mem_filter.mpr ⟨mem_univ _, hxS, fun i hi => hxS (hclosed _ hi _ hxU ?_)⟩
    apply SimpleGraph.Adj.symm
    change (hypercube 9).Adj (cubeBitVec 9 x) (cubeBitVec 9 (toggle x i))
    rw [toggle, cubeBitVec_xor_single]
    exact BalancedCriticalSpectrum.flip_adj _ _
  have hdeg' : ∀ v ∈ U \ support, ((U \ support).filter (fastCube.Adj v)).card ≤ 3 := by
    intro v hv
    have hsub' : (U \ support).filter (fastCube.Adj v) ⊆ U.filter (cube.Adj v) := by
      intro x hx
      obtain ⟨hx, ha⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_sdiff.mp hx).1, (adjacent_iff v x).mp ha⟩
    exact (card_le_card hsub').trans (hdeg v (mem_sdiff.mp hv).1)
  have h := residual_card_lt (U \ support) hsub hdeg'
  rw [card_sdiff_of_subset hU, geometry.1] at h
  have hsize := card_le_card hU
  rw [geometry.1] at hsize
  omega

#print axioms card_le_of_closed_support

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9Residual252Bound
