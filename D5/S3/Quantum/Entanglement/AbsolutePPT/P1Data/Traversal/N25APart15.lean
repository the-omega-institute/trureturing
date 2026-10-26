/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart15
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart15
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart15.traversal_1031,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart15.traversal_1070,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart15.traversal_1071
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart13
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart14
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_1006 (fuel : Nat) (hf : 1006 < fuel) :
    walk nodes fuel 1006 = List.range' 1004 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1006).rule = .split 3 (1827/2048) 1004 1005 := by rfl
      simp only [walk, hr]
      rw [traversal_1004 f (by omega), traversal_1005 f (by omega)]
      change (List.range' 1004 1 ++ List.range' (1004+1) 1) ++
        [1004+(1+1)] = List.range' 1004 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1004) (n := 1+1)).symm

private theorem traversal_1007 (fuel : Nat) (hf : 1007 < fuel) :
    walk nodes fuel 1007 = List.range' 1007 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1007).rule = .bound .leftEnd 2 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1008 (fuel : Nat) (hf : 1008 < fuel) :
    walk nodes fuel 1008 = List.range' 1004 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1008).rule = .split 2 (18293/8192) 1006 1007 := by rfl
      simp only [walk, hr]
      rw [traversal_1006 f (by omega), traversal_1007 f (by omega)]
      change (List.range' 1004 3 ++ List.range' (1004+3) 1) ++
        [1004+(3+1)] = List.range' 1004 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1004) (n := 3+1)).symm

private theorem traversal_1009 (fuel : Nat) (hf : 1009 < fuel) :
    walk nodes fuel 1009 = List.range' 1009 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1009).rule = .bound .leftEnd 2 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1010 (fuel : Nat) (hf : 1010 < fuel) :
    walk nodes fuel 1010 = List.range' 1004 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1010).rule = .split 1 (4695/2048) 1008 1009 := by rfl
      simp only [walk, hr]
      rw [traversal_1008 f (by omega), traversal_1009 f (by omega)]
      change (List.range' 1004 5 ++ List.range' (1004+5) 1) ++
        [1004+(5+1)] = List.range' 1004 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1004) (n := 5+1)).symm

private theorem traversal_1011 (fuel : Nat) (hf : 1011 < fuel) :
    walk nodes fuel 1011 = List.range' 1011 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1011).rule = .bound .leftEnd 1 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1012 (fuel : Nat) (hf : 1012 < fuel) :
    walk nodes fuel 1012 = List.range' 1004 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1012).rule = .split 0 (1/2560) 1010 1011 := by rfl
      simp only [walk, hr]
      rw [traversal_1010 f (by omega), traversal_1011 f (by omega)]
      change (List.range' 1004 7 ++ List.range' (1004+7) 1) ++
        [1004+(7+1)] = List.range' 1004 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1004) (n := 7+1)).symm

private theorem traversal_1013 (fuel : Nat) (hf : 1013 < fuel) :
    walk nodes fuel 1013 = List.range' 1013 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1013).rule = .bound .leftEnd 1 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1014 (fuel : Nat) (hf : 1014 < fuel) :
    walk nodes fuel 1014 = List.range' 1004 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1014).rule = .split 3 (915/1024) 1012 1013 := by rfl
      simp only [walk, hr]
      rw [traversal_1012 f (by omega), traversal_1013 f (by omega)]
      change (List.range' 1004 9 ++ List.range' (1004+9) 1) ++
        [1004+(9+1)] = List.range' 1004 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1004) (n := 9+1)).symm

private theorem traversal_1015 (fuel : Nat) (hf : 1015 < fuel) :
    walk nodes fuel 1015 = List.range' 1003 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1015).rule = .split 2 (9137/4096) 1003 1014 := by rfl
      simp only [walk, hr]
      rw [traversal_1003 f (by omega), traversal_1014 f (by omega)]
      change (List.range' 1003 1 ++ List.range' (1003+1) 11) ++
        [1003+(1+11)] = List.range' 1003 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1003) (n := 1+11)).symm

private theorem traversal_1016 (fuel : Nat) (hf : 1016 < fuel) :
    walk nodes fuel 1016 = List.range' 908 109 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1016).rule = .split 1 (2345/1024) 1002 1015 := by rfl
      simp only [walk, hr]
      rw [traversal_1002 f (by omega), traversal_1015 f (by omega)]
      change (List.range' 908 95 ++ List.range' (908+95) 13) ++
        [908+(95+13)] = List.range' 908 ((95+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 908) (n := 95+13)).symm

private theorem traversal_1017 (fuel : Nat) (hf : 1017 < fuel) :
    walk nodes fuel 1017 = List.range' 1017 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1017).rule = .bound .leftEnd 1 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1018 (fuel : Nat) (hf : 1018 < fuel) :
    walk nodes fuel 1018 = List.range' 1018 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1018).rule = .bound .leftEnd 3 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1019 (fuel : Nat) (hf : 1019 < fuel) :
    walk nodes fuel 1019 = List.range' 1017 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1019).rule = .split 2 (9137/4096) 1017 1018 := by rfl
      simp only [walk, hr]
      rw [traversal_1017 f (by omega), traversal_1018 f (by omega)]
      change (List.range' 1017 1 ++ List.range' (1017+1) 1) ++
        [1017+(1+1)] = List.range' 1017 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1017) (n := 1+1)).symm

private theorem traversal_1020 (fuel : Nat) (hf : 1020 < fuel) :
    walk nodes fuel 1020 = List.range' 1020 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1020).rule = .bound .leftEnd 1 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1021 (fuel : Nat) (hf : 1021 < fuel) :
    walk nodes fuel 1021 = List.range' 1017 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1021).rule = .split 1 (2345/1024) 1019 1020 := by rfl
      simp only [walk, hr]
      rw [traversal_1019 f (by omega), traversal_1020 f (by omega)]
      change (List.range' 1017 3 ++ List.range' (1017+3) 1) ++
        [1017+(3+1)] = List.range' 1017 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1017) (n := 3+1)).symm

private theorem traversal_1022 (fuel : Nat) (hf : 1022 < fuel) :
    walk nodes fuel 1022 = List.range' 908 115 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1022).rule = .split 0 (1/1280) 1016 1021 := by rfl
      simp only [walk, hr]
      rw [traversal_1016 f (by omega), traversal_1021 f (by omega)]
      change (List.range' 908 109 ++ List.range' (908+109) 5) ++
        [908+(109+5)] = List.range' 908 ((109+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 908) (n := 109+5)).symm

private theorem traversal_1023 (fuel : Nat) (hf : 1023 < fuel) :
    walk nodes fuel 1023 = List.range' 1023 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1023).rule = .bound .leftEnd 1 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1024 (fuel : Nat) (hf : 1024 < fuel) :
    walk nodes fuel 1024 = List.range' 908 117 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1024).rule = .split 3 (459/512) 1022 1023 := by rfl
      simp only [walk, hr]
      rw [traversal_1022 f (by omega), traversal_1023 f (by omega)]
      change (List.range' 908 115 ++ List.range' (908+115) 1) ++
        [908+(115+1)] = List.range' 908 ((115+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 908) (n := 115+1)).symm

private theorem traversal_1025 (fuel : Nat) (hf : 1025 < fuel) :
    walk nodes fuel 1025 = List.range' 907 119 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1025).rule = .split 2 (4559/2048) 907 1024 := by rfl
      simp only [walk, hr]
      rw [traversal_907 f (by omega), traversal_1024 f (by omega)]
      change (List.range' 907 1 ++ List.range' (907+1) 117) ++
        [907+(1+117)] = List.range' 907 ((1+117)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 907) (n := 1+117)).symm

private theorem traversal_1026 (fuel : Nat) (hf : 1026 < fuel) :
    walk nodes fuel 1026 = List.range' 1026 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1026).rule = .bound .leftEnd 1 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1027 (fuel : Nat) (hf : 1027 < fuel) :
    walk nodes fuel 1027 = List.range' 907 121 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1027).rule = .split 1 (1175/512) 1025 1026 := by rfl
      simp only [walk, hr]
      rw [traversal_1025 f (by omega), traversal_1026 f (by omega)]
      change (List.range' 907 119 ++ List.range' (907+119) 1) ++
        [907+(119+1)] = List.range' 907 ((119+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 907) (n := 119+1)).symm

private theorem traversal_1028 (fuel : Nat) (hf : 1028 < fuel) :
    walk nodes fuel 1028 = List.range' 1028 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1028).rule = .bound .leftEnd 1 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1029 (fuel : Nat) (hf : 1029 < fuel) :
    walk nodes fuel 1029 = List.range' 907 123 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1029).rule = .split 0 (1/640) 1027 1028 := by rfl
      simp only [walk, hr]
      rw [traversal_1027 f (by omega), traversal_1028 f (by omega)]
      change (List.range' 907 121 ++ List.range' (907+121) 1) ++
        [907+(121+1)] = List.range' 907 ((121+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 907) (n := 121+1)).symm

private theorem traversal_1030 (fuel : Nat) (hf : 1030 < fuel) :
    walk nodes fuel 1030 = List.range' 1030 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1030).rule = .bound .leftEnd 1 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1031 (fuel : Nat) (hf : 1031 < fuel) :
    walk nodes fuel 1031 = List.range' 907 125 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1031).rule = .split 3 (231/256) 1029 1030 := by rfl
      simp only [walk, hr]
      rw [traversal_1029 f (by omega), traversal_1030 f (by omega)]
      change (List.range' 907 123 ++ List.range' (907+123) 1) ++
        [907+(123+1)] = List.range' 907 ((123+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 907) (n := 123+1)).symm

private theorem traversal_1032 (fuel : Nat) (hf : 1032 < fuel) :
    walk nodes fuel 1032 = List.range' 1032 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1032).rule = .bound .leftEnd 2 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1033 (fuel : Nat) (hf : 1033 < fuel) :
    walk nodes fuel 1033 = List.range' 1033 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1033).rule = .bound .leftEnd 8 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1034 (fuel : Nat) (hf : 1034 < fuel) :
    walk nodes fuel 1034 = List.range' 1034 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1034).rule = .bound .leftEnd 8 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1035 (fuel : Nat) (hf : 1035 < fuel) :
    walk nodes fuel 1035 = List.range' 1035 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1035).rule = .bound .leftEnd 2 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1036 (fuel : Nat) (hf : 1036 < fuel) :
    walk nodes fuel 1036 = List.range' 1034 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1036).rule = .split 2 (73267/32768) 1034 1035 := by rfl
      simp only [walk, hr]
      rw [traversal_1034 f (by omega), traversal_1035 f (by omega)]
      change (List.range' 1034 1 ++ List.range' (1034+1) 1) ++
        [1034+(1+1)] = List.range' 1034 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1034) (n := 1+1)).symm

private theorem traversal_1037 (fuel : Nat) (hf : 1037 < fuel) :
    walk nodes fuel 1037 = List.range' 1037 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1037).rule = .bound .leftEnd 2 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1038 (fuel : Nat) (hf : 1038 < fuel) :
    walk nodes fuel 1038 = List.range' 1034 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1038).rule = .split 1 (18735/8192) 1036 1037 := by rfl
      simp only [walk, hr]
      rw [traversal_1036 f (by omega), traversal_1037 f (by omega)]
      change (List.range' 1034 3 ++ List.range' (1034+3) 1) ++
        [1034+(3+1)] = List.range' 1034 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1034) (n := 3+1)).symm

private theorem traversal_1039 (fuel : Nat) (hf : 1039 < fuel) :
    walk nodes fuel 1039 = List.range' 1039 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1039).rule = .bound .leftEnd 2 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1040 (fuel : Nat) (hf : 1040 < fuel) :
    walk nodes fuel 1040 = List.range' 1034 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1040).rule = .split 0 (1/10240) 1038 1039 := by rfl
      simp only [walk, hr]
      rw [traversal_1038 f (by omega), traversal_1039 f (by omega)]
      change (List.range' 1034 5 ++ List.range' (1034+5) 1) ++
        [1034+(5+1)] = List.range' 1034 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1034) (n := 5+1)).symm

private theorem traversal_1041 (fuel : Nat) (hf : 1041 < fuel) :
    walk nodes fuel 1041 = List.range' 1041 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1041).rule = .bound .leftEnd 8 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1042 (fuel : Nat) (hf : 1042 < fuel) :
    walk nodes fuel 1042 = List.range' 1042 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1042).rule = .bound .leftEnd 3 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1043 (fuel : Nat) (hf : 1043 < fuel) :
    walk nodes fuel 1043 = List.range' 1041 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1043).rule = .split 1 (18735/8192) 1041 1042 := by rfl
      simp only [walk, hr]
      rw [traversal_1041 f (by omega), traversal_1042 f (by omega)]
      change (List.range' 1041 1 ++ List.range' (1041+1) 1) ++
        [1041+(1+1)] = List.range' 1041 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1041) (n := 1+1)).symm

private theorem traversal_1044 (fuel : Nat) (hf : 1044 < fuel) :
    walk nodes fuel 1044 = List.range' 1044 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1044).rule = .bound .leftEnd 1 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1045 (fuel : Nat) (hf : 1045 < fuel) :
    walk nodes fuel 1045 = List.range' 1041 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1045).rule = .split 0 (1/10240) 1043 1044 := by rfl
      simp only [walk, hr]
      rw [traversal_1043 f (by omega), traversal_1044 f (by omega)]
      change (List.range' 1041 3 ++ List.range' (1041+3) 1) ++
        [1041+(3+1)] = List.range' 1041 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1041) (n := 3+1)).symm

private theorem traversal_1046 (fuel : Nat) (hf : 1046 < fuel) :
    walk nodes fuel 1046 = List.range' 1034 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1046).rule = .split 3 (3663/4096) 1040 1045 := by rfl
      simp only [walk, hr]
      rw [traversal_1040 f (by omega), traversal_1045 f (by omega)]
      change (List.range' 1034 7 ++ List.range' (1034+7) 5) ++
        [1034+(7+5)] = List.range' 1034 ((7+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1034) (n := 7+5)).symm

private theorem traversal_1047 (fuel : Nat) (hf : 1047 < fuel) :
    walk nodes fuel 1047 = List.range' 1047 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1047).rule = .bound .leftEnd 3 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1048 (fuel : Nat) (hf : 1048 < fuel) :
    walk nodes fuel 1048 = List.range' 1034 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1048).rule = .split 2 (36643/16384) 1046 1047 := by rfl
      simp only [walk, hr]
      rw [traversal_1046 f (by omega), traversal_1047 f (by omega)]
      change (List.range' 1034 13 ++ List.range' (1034+13) 1) ++
        [1034+(13+1)] = List.range' 1034 ((13+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1034) (n := 13+1)).symm

private theorem traversal_1049 (fuel : Nat) (hf : 1049 < fuel) :
    walk nodes fuel 1049 = List.range' 1033 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1049).rule = .split 1 (9365/4096) 1033 1048 := by rfl
      simp only [walk, hr]
      rw [traversal_1033 f (by omega), traversal_1048 f (by omega)]
      change (List.range' 1033 1 ++ List.range' (1033+1) 15) ++
        [1033+(1+15)] = List.range' 1033 ((1+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1033) (n := 1+15)).symm

private theorem traversal_1050 (fuel : Nat) (hf : 1050 < fuel) :
    walk nodes fuel 1050 = List.range' 1050 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1050).rule = .bound .leftEnd 3 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1051 (fuel : Nat) (hf : 1051 < fuel) :
    walk nodes fuel 1051 = List.range' 1033 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1051).rule = .split 0 (1/5120) 1049 1050 := by rfl
      simp only [walk, hr]
      rw [traversal_1049 f (by omega), traversal_1050 f (by omega)]
      change (List.range' 1033 17 ++ List.range' (1033+17) 1) ++
        [1033+(17+1)] = List.range' 1033 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1033) (n := 17+1)).symm

private theorem traversal_1052 (fuel : Nat) (hf : 1052 < fuel) :
    walk nodes fuel 1052 = List.range' 1052 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1052).rule = .bound .leftEnd 8 (811/1536) (496489/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1053 (fuel : Nat) (hf : 1053 < fuel) :
    walk nodes fuel 1053 = List.range' 1053 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1053).rule = .bound .leftEnd 1 (811/1536) (496489/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1054 (fuel : Nat) (hf : 1054 < fuel) :
    walk nodes fuel 1054 = List.range' 1054 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1054).rule = .bound .leftEnd 3 (811/1536) (496489/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1055 (fuel : Nat) (hf : 1055 < fuel) :
    walk nodes fuel 1055 = List.range' 1053 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1055).rule = .split 2 (36643/16384) 1053 1054 := by rfl
      simp only [walk, hr]
      rw [traversal_1053 f (by omega), traversal_1054 f (by omega)]
      change (List.range' 1053 1 ++ List.range' (1053+1) 1) ++
        [1053+(1+1)] = List.range' 1053 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1053) (n := 1+1)).symm

private theorem traversal_1056 (fuel : Nat) (hf : 1056 < fuel) :
    walk nodes fuel 1056 = List.range' 1052 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1056).rule = .split 1 (9365/4096) 1052 1055 := by rfl
      simp only [walk, hr]
      rw [traversal_1052 f (by omega), traversal_1055 f (by omega)]
      change (List.range' 1052 1 ++ List.range' (1052+1) 3) ++
        [1052+(1+3)] = List.range' 1052 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1052) (n := 1+3)).symm

private theorem traversal_1057 (fuel : Nat) (hf : 1057 < fuel) :
    walk nodes fuel 1057 = List.range' 1057 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1057).rule = .bound .leftEnd 1 (811/1536) (496489/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1058 (fuel : Nat) (hf : 1058 < fuel) :
    walk nodes fuel 1058 = List.range' 1052 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1058).rule = .split 0 (1/5120) 1056 1057 := by rfl
      simp only [walk, hr]
      rw [traversal_1056 f (by omega), traversal_1057 f (by omega)]
      change (List.range' 1052 5 ++ List.range' (1052+5) 1) ++
        [1052+(5+1)] = List.range' 1052 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1052) (n := 5+1)).symm

private theorem traversal_1059 (fuel : Nat) (hf : 1059 < fuel) :
    walk nodes fuel 1059 = List.range' 1033 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1059).rule = .split 3 (1833/2048) 1051 1058 := by rfl
      simp only [walk, hr]
      rw [traversal_1051 f (by omega), traversal_1058 f (by omega)]
      change (List.range' 1033 19 ++ List.range' (1033+19) 7) ++
        [1033+(19+7)] = List.range' 1033 ((19+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1033) (n := 19+7)).symm

private theorem traversal_1060 (fuel : Nat) (hf : 1060 < fuel) :
    walk nodes fuel 1060 = List.range' 1060 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1060).rule = .bound .leftEnd 3 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1061 (fuel : Nat) (hf : 1061 < fuel) :
    walk nodes fuel 1061 = List.range' 1033 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1061).rule = .split 2 (18331/8192) 1059 1060 := by rfl
      simp only [walk, hr]
      rw [traversal_1059 f (by omega), traversal_1060 f (by omega)]
      change (List.range' 1033 27 ++ List.range' (1033+27) 1) ++
        [1033+(27+1)] = List.range' 1033 ((27+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1033) (n := 27+1)).symm

private theorem traversal_1062 (fuel : Nat) (hf : 1062 < fuel) :
    walk nodes fuel 1062 = List.range' 1062 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1062).rule = .bound .leftEnd 3 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1063 (fuel : Nat) (hf : 1063 < fuel) :
    walk nodes fuel 1063 = List.range' 1033 31 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1063).rule = .split 1 (4685/2048) 1061 1062 := by rfl
      simp only [walk, hr]
      rw [traversal_1061 f (by omega), traversal_1062 f (by omega)]
      change (List.range' 1033 29 ++ List.range' (1033+29) 1) ++
        [1033+(29+1)] = List.range' 1033 ((29+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1033) (n := 29+1)).symm

private theorem traversal_1064 (fuel : Nat) (hf : 1064 < fuel) :
    walk nodes fuel 1064 = List.range' 1064 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1064).rule = .bound .leftEnd 3 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1065 (fuel : Nat) (hf : 1065 < fuel) :
    walk nodes fuel 1065 = List.range' 1033 33 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1065).rule = .split 0 (1/2560) 1063 1064 := by rfl
      simp only [walk, hr]
      rw [traversal_1063 f (by omega), traversal_1064 f (by omega)]
      change (List.range' 1033 31 ++ List.range' (1033+31) 1) ++
        [1033+(31+1)] = List.range' 1033 ((31+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1033) (n := 31+1)).symm

private theorem traversal_1066 (fuel : Nat) (hf : 1066 < fuel) :
    walk nodes fuel 1066 = List.range' 1032 35 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1066).rule = .split 3 (915/1024) 1032 1065 := by rfl
      simp only [walk, hr]
      rw [traversal_1032 f (by omega), traversal_1065 f (by omega)]
      change (List.range' 1032 1 ++ List.range' (1032+1) 33) ++
        [1032+(1+33)] = List.range' 1032 ((1+33)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1032) (n := 1+33)).symm

private theorem traversal_1067 (fuel : Nat) (hf : 1067 < fuel) :
    walk nodes fuel 1067 = List.range' 1067 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1067).rule = .bound .leftEnd 3 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1068 (fuel : Nat) (hf : 1068 < fuel) :
    walk nodes fuel 1068 = List.range' 1032 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1068).rule = .split 2 (9175/4096) 1066 1067 := by rfl
      simp only [walk, hr]
      rw [traversal_1066 f (by omega), traversal_1067 f (by omega)]
      change (List.range' 1032 35 ++ List.range' (1032+35) 1) ++
        [1032+(35+1)] = List.range' 1032 ((35+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1032) (n := 35+1)).symm

private theorem traversal_1069 (fuel : Nat) (hf : 1069 < fuel) :
    walk nodes fuel 1069 = List.range' 1069 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1069).rule = .bound .leftEnd 3 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1070 (fuel : Nat) (hf : 1070 < fuel) :
    walk nodes fuel 1070 = List.range' 1032 39 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1070).rule = .split 1 (2345/1024) 1068 1069 := by rfl
      simp only [walk, hr]
      rw [traversal_1068 f (by omega), traversal_1069 f (by omega)]
      change (List.range' 1032 37 ++ List.range' (1032+37) 1) ++
        [1032+(37+1)] = List.range' 1032 ((37+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 1032) (n := 37+1)).symm

theorem traversal_1071 (fuel : Nat) (hf : 1071 < fuel) :
    walk nodes fuel 1071 = List.range' 1071 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1071).rule = .bound .leftEnd 3 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
