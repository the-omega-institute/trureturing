/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart13
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart13
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25BPart13.traversal_882
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart10
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25BPart12
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_871 (fuel : Nat) (hf : 871 < fuel) :
    walk nodes fuel 871 = List.range' 871 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 871).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_872 (fuel : Nat) (hf : 872 < fuel) :
    walk nodes fuel 872 = List.range' 870 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 872).rule = .split 2 (5/4) 870 871 := by rfl
      simp only [walk, hr]
      rw [traversal_870 f (by omega), traversal_871 f (by omega)]
      change (List.range' 870 1 ++ List.range' (870+1) 1) ++
        [870+(1+1)] = List.range' 870 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 870) (n := 1+1)).symm

private theorem traversal_873 (fuel : Nat) (hf : 873 < fuel) :
    walk nodes fuel 873 = List.range' 873 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 873).rule = .bound .leftEnd 3 0 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_874 (fuel : Nat) (hf : 874 < fuel) :
    walk nodes fuel 874 = List.range' 870 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 874).rule = .split 1 (15/4) 872 873 := by rfl
      simp only [walk, hr]
      rw [traversal_872 f (by omega), traversal_873 f (by omega)]
      change (List.range' 870 3 ++ List.range' (870+3) 1) ++
        [870+(3+1)] = List.range' 870 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 870) (n := 3+1)).symm

private theorem traversal_875 (fuel : Nat) (hf : 875 < fuel) :
    walk nodes fuel 875 = List.range' 875 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 875).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_876 (fuel : Nat) (hf : 876 < fuel) :
    walk nodes fuel 876 = List.range' 870 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 876).rule = .split 0 (3/10) 874 875 := by rfl
      simp only [walk, hr]
      rw [traversal_874 f (by omega), traversal_875 f (by omega)]
      change (List.range' 870 5 ++ List.range' (870+5) 1) ++
        [870+(5+1)] = List.range' 870 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 870) (n := 5+1)).symm

private theorem traversal_877 (fuel : Nat) (hf : 877 < fuel) :
    walk nodes fuel 877 = List.range' 877 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 877).rule = .infeasible 16 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_878 (fuel : Nat) (hf : 878 < fuel) :
    walk nodes fuel 878 = List.range' 870 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 878).rule = .split 3 (3/2) 876 877 := by rfl
      simp only [walk, hr]
      rw [traversal_876 f (by omega), traversal_877 f (by omega)]
      change (List.range' 870 7 ++ List.range' (870+7) 1) ++
        [870+(7+1)] = List.range' 870 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 870) (n := 7+1)).symm

private theorem traversal_879 (fuel : Nat) (hf : 879 < fuel) :
    walk nodes fuel 879 = List.range' 879 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 879).rule = .infeasible 0 := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_880 (fuel : Nat) (hf : 880 < fuel) :
    walk nodes fuel 880 = List.range' 870 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 880).rule = .split 2 (5/2) 878 879 := by rfl
      simp only [walk, hr]
      rw [traversal_878 f (by omega), traversal_879 f (by omega)]
      change (List.range' 870 9 ++ List.range' (870+9) 1) ++
        [870+(9+1)] = List.range' 870 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 870) (n := 9+1)).symm

private theorem traversal_881 (fuel : Nat) (hf : 881 < fuel) :
    walk nodes fuel 881 = List.range' 733 149 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 881).rule = .split 1 (5/2) 869 880 := by rfl
      simp only [walk, hr]
      rw [traversal_869 f (by omega), traversal_880 f (by omega)]
      change (List.range' 733 137 ++ List.range' (733+137) 11) ++
        [733+(137+11)] = List.range' 733 ((137+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 733) (n := 137+11)).symm

theorem traversal_882 (fuel : Nat) (hf : 882 < fuel) :
    walk nodes fuel 882 = List.range' 0 883 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 882).rule = .split 0 (1/10) 732 881 := by rfl
      simp only [walk, hr]
      rw [traversal_732 f (by omega), traversal_881 f (by omega)]
      change (List.range' 0 733 ++ List.range' (0+733) 149) ++
        [0+(733+149)] = List.range' 0 ((733+149)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 0) (n := 733+149)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
