import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.PathRigidity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.PathRigidity

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace DetachedRemote

abbrev signature : Signature where
  Params := ℤ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ L n => pathEdges L n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (j : Bool) {k : ℕ} (hk : 1 ≤ k) (L : ℤ) (hq : j.toInt ∉ pathVertices L k), ∃ e ∈ R.readout () L k, (2 * k + 1 : ℤ) ≤ |2 * e + (!j).toInt - j.toInt|

private theorem actual_law : arena.Law actual := by
  exact @detached_path_remote

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h false (k := 1) (by decide) 1 (by decide)
  simpa [rejected, realize] using hb

def evidence : Registration arena (type_of% (@detached_path_remote)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨0, 0, 1, ?_⟩
    change pathEdges 0 0 ≠ pathEdges 0 1
    decide

end DetachedRemote

namespace ZeroPathBlock

abbrev signature : Signature where
  Params := ℤ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ L n => pathVertices L n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℤ) (n : ℕ), SpinWindow.zeroEdges (pathEdges L n) = SpinWindow.monoBlock (R.readout () L n)

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.zero_path_eq_block

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 1
  change SpinWindow.zeroEdges (pathEdges 0 1) = SpinWindow.monoBlock ∅ at hb
  let S : Spins := fun e => decide (e = 0)
  have hm : S ∈ SpinWindow.monoBlock ∅ := by simp [SpinWindow.monoBlock, SpinWindow.constant]
  have hs : S ∈ SpinWindow.zeroEdges (pathEdges 0 1) := by rw [hb]; exact hm
  have hc := hs 0 (by decide)
  norm_num [S] at hc

def evidence : Registration arena (type_of% (@SpinWindow.zero_path_eq_block)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨0, 0, 1, ?_⟩
    change pathVertices 0 0 ≠ pathVertices 0 1
    decide

end ZeroPathBlock

namespace SupportedVertices

abbrev signature : Signature where
  Params := ℤ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ L n => pathVertices L n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => {0}) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (V : Finset ℤ) (L : ℤ) {n : ℕ} (hn : 1 ≤ n) (h : ∀ e ∈ pathEdges L n, e ∈ V ∧ e + 1 ∈ V), R.readout () L n ⊆ V

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.path_vertices_supported

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : ∀ e ∈ pathEdges 1 1, e ∈ ({1, 2} : Finset ℤ) ∧ e + 1 ∈ ({1, 2} : Finset ℤ) := by
    intro e he
    have heq : e = 1 := by simpa [pathEdges] using he
    subst e
    norm_num
  have hb := h {1, 2} 1 (n := 1) (by decide) hh
  have hc := hb (by simp [rejected, realize] : (0 : ℤ) ∈ rejected.readout () 1 1)
  norm_num at hc

def evidence : Registration arena (type_of% (@SpinWindow.path_vertices_supported)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨0, 0, 1, ?_⟩
    change pathVertices 0 0 ≠ pathVertices 0 1
    decide

end SupportedVertices

namespace ConsecutivePrefixes

abbrev signature : Signature where
  Params := ℤ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ L n => pathEdges L n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (es : List ℤ)
    (hV : SpinWindow.SupportsEdges V es) (hm : SpinWindow.PrefixMasses β V es) (hk : 1 ≤ es.length),
    es.Nodup ∧ ∃ L : ℤ, es.toFinset = R.readout () L es.length

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.prefixes_force_consecutive

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let V : Finset ℤ := {0, 1, 2}
  have hV : SpinWindow.SupportsEdges V [0] := by
    intro e he
    have heq : e = 0 := by simpa using he
    subst e
    norm_num [V]
  have hm : SpinWindow.PrefixMasses β V [0] := by
    intro r hr hlen
    have hre : r = 1 := by simp only [List.length_singleton] at hlen; omega
    subst r
    have he : (([0] : List ℤ).take 1).toFinset = pathEdges 0 1 := by decide
    rw [he, SpinWindow.zero_path_eq_block]
    have hb := SpinWindow.block_constant_prob β V (pathVertices 0 1) ∅
      (by dsimp [V]; decide) (by simp) (by simp) (by decide) false
    have hce : SpinWindow.constant ∅ false = (Set.univ : Set Spins) := by
      ext S
      simp [SpinWindow.constant]
    rw [hce, Set.inter_univ, Finset.card_empty, pow_zero, mul_one, vertices_card] at hb
    exact hb
  obtain ⟨_, L, hL⟩ := h β V [0] hV hm (by decide)
  simpa [rejected, realize] using hL

def evidence : Registration arena (type_of% (@SpinWindow.prefixes_force_consecutive)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨0, 0, 1, ?_⟩
    change pathEdges 0 0 ≠ pathEdges 0 1
    decide

end ConsecutivePrefixes

namespace FiniteGeometry

abbrev signature : Signature where
  Params := ℤ
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ L n => pathEdges L n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (β : Bias) (V : Finset ℤ) (es : List ℤ) (q : ℤ)
    (hk : 1 ≤ es.length) (hV : SpinWindow.SupportsEdges V es) (hm : SpinWindow.PrefixMasses β V es)
    (htarget : ∀ s : Bool, SpinWindow.prob β V (SpinWindow.zeroEdges es.toFinset ∩ {S | S q = s}) = β.π s * β.T (es.length + 1)),
    es.Nodup ∧ ∃ L : ℤ, es.toFinset = R.readout () L es.length ∧ q ∉ pathVertices L es.length

private theorem actual_law : arena.Law actual := by
  exact @SpinWindow.finite_path_geometry

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let β : Bias := ⟨1 / 3, by norm_num, by norm_num, by norm_num⟩
  let V : Finset ℤ := {0, 1, 2}
  have hV : SpinWindow.SupportsEdges V [0] := by
    intro e he
    have heq : e = 0 := by simpa using he
    subst e
    norm_num [V]
  have hm : SpinWindow.PrefixMasses β V [0] := by
    intro r hr hlen
    have hre : r = 1 := by simp only [List.length_singleton] at hlen; omega
    subst r
    have he : (([0] : List ℤ).take 1).toFinset = pathEdges 0 1 := by decide
    rw [he, SpinWindow.zero_path_eq_block]
    have hb := SpinWindow.block_constant_prob β V (pathVertices 0 1) ∅
      (by dsimp [V]; decide) (by simp) (by simp) (by decide) false
    have hce : SpinWindow.constant ∅ false = (Set.univ : Set Spins) := by
      ext S
      simp [SpinWindow.constant]
    rw [hce, Set.inter_univ, Finset.card_empty, pow_zero, mul_one, vertices_card] at hb
    exact hb
  have ht : ∀ s : Bool, SpinWindow.prob β V
      (SpinWindow.zeroEdges ([0] : List ℤ).toFinset ∩ {S | S 2 = s}) = β.π s * β.T (([0] : List ℤ).length + 1) := by
    intro s
    have he : ([0] : List ℤ).toFinset = pathEdges 0 1 := by decide
    rw [he, SpinWindow.zero_path_eq_block]
    have hse : {S : Spins | S 2 = s} = SpinWindow.constant {2} s := by
      ext S
      simp [SpinWindow.constant]
    rw [hse]
    have hb := SpinWindow.block_constant_prob β V (pathVertices 0 1) {2}
      (by dsimp [V]; decide) (by dsimp [V]; decide) (by decide) (by decide) s
    simpa [vertices_card, mul_comm] using hb
  obtain ⟨_, L, hL, _⟩ := h β V [0] 2 (by decide) hV hm ht
  simpa [rejected, realize] using hL

def evidence : Registration arena (type_of% (@SpinWindow.finite_path_geometry)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    dsimp only [Sensitivity, arena, signature]
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim j i))
    · intro i
      exact nomatch i
  dependence := by
    dsimp only [ObservationalDependence, arena, signature]
    intro i
    cases i
    refine ⟨0, 0, 1, ?_⟩
    change pathEdges 0 0 ≠ pathEdges 0 1
    decide

end FiniteGeometry

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.PathRigidity
