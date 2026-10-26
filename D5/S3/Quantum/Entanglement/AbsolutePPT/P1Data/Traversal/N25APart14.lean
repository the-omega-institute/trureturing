/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart14
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart14
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart14.traversal_1002,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart14.traversal_1003,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart14.traversal_1004,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart14.traversal_1005
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart13
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_940 (fuel : Nat) (hf : 940 < fuel) :
    walk nodes fuel 940 = List.range' 932 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 940).rule = .split 3 (3657/4096) 932 939 := by rfl
      simp only [walk, hr]
      rw [traversal_932 f (by omega), traversal_939 f (by omega)]
      change (List.range' 932 1 ++ List.range' (932+1) 7) ++
        [932+(1+7)] = List.range' 932 ((1+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 932) (n := 1+7)).symm

private theorem traversal_941 (fuel : Nat) (hf : 941 < fuel) :
    walk nodes fuel 941 = List.range' 941 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 941).rule = .bound .leftEnd 2 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_942 (fuel : Nat) (hf : 942 < fuel) :
    walk nodes fuel 942 = List.range' 932 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 942).rule = .split 2 (36605/16384) 940 941 := by rfl
      simp only [walk, hr]
      rw [traversal_940 f (by omega), traversal_941 f (by omega)]
      change (List.range' 932 9 ++ List.range' (932+9) 1) ++
        [932+(9+1)] = List.range' 932 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 932) (n := 9+1)).symm

private theorem traversal_943 (fuel : Nat) (hf : 943 < fuel) :
    walk nodes fuel 943 = List.range' 931 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 943).rule = .split 1 (9365/4096) 931 942 := by rfl
      simp only [walk, hr]
      rw [traversal_931 f (by omega), traversal_942 f (by omega)]
      change (List.range' 931 1 ++ List.range' (931+1) 11) ++
        [931+(1+11)] = List.range' 931 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 931) (n := 1+11)).symm

private theorem traversal_944 (fuel : Nat) (hf : 944 < fuel) :
    walk nodes fuel 944 = List.range' 944 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 944).rule = .bound .leftEnd 8 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_945 (fuel : Nat) (hf : 945 < fuel) :
    walk nodes fuel 945 = List.range' 945 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 945).rule = .bound .leftEnd 2 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_946 (fuel : Nat) (hf : 946 < fuel) :
    walk nodes fuel 946 = List.range' 944 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 946).rule = .split 1 (9365/4096) 944 945 := by rfl
      simp only [walk, hr]
      rw [traversal_944 f (by omega), traversal_945 f (by omega)]
      change (List.range' 944 1 ++ List.range' (944+1) 1) ++
        [944+(1+1)] = List.range' 944 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 944) (n := 1+1)).symm

private theorem traversal_947 (fuel : Nat) (hf : 947 < fuel) :
    walk nodes fuel 947 = List.range' 931 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 947).rule = .split 0 (1/5120) 943 946 := by rfl
      simp only [walk, hr]
      rw [traversal_943 f (by omega), traversal_946 f (by omega)]
      change (List.range' 931 13 ++ List.range' (931+13) 3) ++
        [931+(13+3)] = List.range' 931 ((13+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 931) (n := 13+3)).symm

private theorem traversal_948 (fuel : Nat) (hf : 948 < fuel) :
    walk nodes fuel 948 = List.range' 930 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 948).rule = .split 3 (1827/2048) 930 947 := by rfl
      simp only [walk, hr]
      rw [traversal_930 f (by omega), traversal_947 f (by omega)]
      change (List.range' 930 1 ++ List.range' (930+1) 17) ++
        [930+(1+17)] = List.range' 930 ((1+17)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 930) (n := 1+17)).symm

private theorem traversal_949 (fuel : Nat) (hf : 949 < fuel) :
    walk nodes fuel 949 = List.range' 927 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 949).rule = .split 2 (18293/8192) 929 948 := by rfl
      simp only [walk, hr]
      rw [traversal_929 f (by omega), traversal_948 f (by omega)]
      change (List.range' 927 3 ++ List.range' (927+3) 19) ++
        [927+(3+19)] = List.range' 927 ((3+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 927) (n := 3+19)).symm

private theorem traversal_950 (fuel : Nat) (hf : 950 < fuel) :
    walk nodes fuel 950 = List.range' 950 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 950).rule = .bound .leftEnd 2 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_951 (fuel : Nat) (hf : 951 < fuel) :
    walk nodes fuel 951 = List.range' 951 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 951).rule = .bound .leftEnd 1 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_952 (fuel : Nat) (hf : 952 < fuel) :
    walk nodes fuel 952 = List.range' 952 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 952).rule = .bound .leftEnd 2 (203/384) (495877/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_953 (fuel : Nat) (hf : 953 < fuel) :
    walk nodes fuel 953 = List.range' 953 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 953).rule = .bound .leftEnd 1 (407/768) (247329/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_954 (fuel : Nat) (hf : 954 < fuel) :
    walk nodes fuel 954 = List.range' 952 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 954).rule = .split 3 (3657/4096) 952 953 := by rfl
      simp only [walk, hr]
      rw [traversal_952 f (by omega), traversal_953 f (by omega)]
      change (List.range' 952 1 ++ List.range' (952+1) 1) ++
        [952+(1+1)] = List.range' 952 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 952) (n := 1+1)).symm

private theorem traversal_955 (fuel : Nat) (hf : 955 < fuel) :
    walk nodes fuel 955 = List.range' 951 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 955).rule = .split 2 (36567/16384) 951 954 := by rfl
      simp only [walk, hr]
      rw [traversal_951 f (by omega), traversal_954 f (by omega)]
      change (List.range' 951 1 ++ List.range' (951+1) 3) ++
        [951+(1+3)] = List.range' 951 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 951) (n := 1+3)).symm

private theorem traversal_956 (fuel : Nat) (hf : 956 < fuel) :
    walk nodes fuel 956 = List.range' 956 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 956).rule = .bound .leftEnd 1 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_957 (fuel : Nat) (hf : 957 < fuel) :
    walk nodes fuel 957 = List.range' 951 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 957).rule = .split 1 (9375/4096) 955 956 := by rfl
      simp only [walk, hr]
      rw [traversal_955 f (by omega), traversal_956 f (by omega)]
      change (List.range' 951 5 ++ List.range' (951+5) 1) ++
        [951+(5+1)] = List.range' 951 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 951) (n := 5+1)).symm

private theorem traversal_958 (fuel : Nat) (hf : 958 < fuel) :
    walk nodes fuel 958 = List.range' 958 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 958).rule = .bound .leftEnd 1 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_959 (fuel : Nat) (hf : 959 < fuel) :
    walk nodes fuel 959 = List.range' 951 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 959).rule = .split 0 (1/5120) 957 958 := by rfl
      simp only [walk, hr]
      rw [traversal_957 f (by omega), traversal_958 f (by omega)]
      change (List.range' 951 7 ++ List.range' (951+7) 1) ++
        [951+(7+1)] = List.range' 951 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 951) (n := 7+1)).symm

private theorem traversal_960 (fuel : Nat) (hf : 960 < fuel) :
    walk nodes fuel 960 = List.range' 950 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 960).rule = .split 3 (1827/2048) 950 959 := by rfl
      simp only [walk, hr]
      rw [traversal_950 f (by omega), traversal_959 f (by omega)]
      change (List.range' 950 1 ++ List.range' (950+1) 9) ++
        [950+(1+9)] = List.range' 950 ((1+9)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 950) (n := 1+9)).symm

private theorem traversal_961 (fuel : Nat) (hf : 961 < fuel) :
    walk nodes fuel 961 = List.range' 961 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 961).rule = .bound .leftEnd 2 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_962 (fuel : Nat) (hf : 962 < fuel) :
    walk nodes fuel 962 = List.range' 950 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 962).rule = .split 2 (18293/8192) 960 961 := by rfl
      simp only [walk, hr]
      rw [traversal_960 f (by omega), traversal_961 f (by omega)]
      change (List.range' 950 11 ++ List.range' (950+11) 1) ++
        [950+(11+1)] = List.range' 950 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 950) (n := 11+1)).symm

private theorem traversal_963 (fuel : Nat) (hf : 963 < fuel) :
    walk nodes fuel 963 = List.range' 927 37 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 963).rule = .split 1 (4685/2048) 949 962 := by rfl
      simp only [walk, hr]
      rw [traversal_949 f (by omega), traversal_962 f (by omega)]
      change (List.range' 927 23 ++ List.range' (927+23) 13) ++
        [927+(23+13)] = List.range' 927 ((23+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 927) (n := 23+13)).symm

private theorem traversal_964 (fuel : Nat) (hf : 964 < fuel) :
    walk nodes fuel 964 = List.range' 964 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 964).rule = .bound .leftEnd 2 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_965 (fuel : Nat) (hf : 965 < fuel) :
    walk nodes fuel 965 = List.range' 965 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 965).rule = .bound .leftEnd 1 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_966 (fuel : Nat) (hf : 966 < fuel) :
    walk nodes fuel 966 = List.range' 964 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 966).rule = .split 3 (1827/2048) 964 965 := by rfl
      simp only [walk, hr]
      rw [traversal_964 f (by omega), traversal_965 f (by omega)]
      change (List.range' 964 1 ++ List.range' (964+1) 1) ++
        [964+(1+1)] = List.range' 964 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 964) (n := 1+1)).symm

private theorem traversal_967 (fuel : Nat) (hf : 967 < fuel) :
    walk nodes fuel 967 = List.range' 967 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 967).rule = .bound .leftEnd 2 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_968 (fuel : Nat) (hf : 968 < fuel) :
    walk nodes fuel 968 = List.range' 964 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 968).rule = .split 2 (18293/8192) 966 967 := by rfl
      simp only [walk, hr]
      rw [traversal_966 f (by omega), traversal_967 f (by omega)]
      change (List.range' 964 3 ++ List.range' (964+3) 1) ++
        [964+(3+1)] = List.range' 964 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 964) (n := 3+1)).symm

private theorem traversal_969 (fuel : Nat) (hf : 969 < fuel) :
    walk nodes fuel 969 = List.range' 969 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 969).rule = .bound .leftEnd 2 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_970 (fuel : Nat) (hf : 970 < fuel) :
    walk nodes fuel 970 = List.range' 964 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 970).rule = .split 1 (4685/2048) 968 969 := by rfl
      simp only [walk, hr]
      rw [traversal_968 f (by omega), traversal_969 f (by omega)]
      change (List.range' 964 5 ++ List.range' (964+5) 1) ++
        [964+(5+1)] = List.range' 964 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 964) (n := 5+1)).symm

private theorem traversal_971 (fuel : Nat) (hf : 971 < fuel) :
    walk nodes fuel 971 = List.range' 927 45 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 971).rule = .split 0 (1/2560) 963 970 := by rfl
      simp only [walk, hr]
      rw [traversal_963 f (by omega), traversal_970 f (by omega)]
      change (List.range' 927 37 ++ List.range' (927+37) 7) ++
        [927+(37+7)] = List.range' 927 ((37+7)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 927) (n := 37+7)).symm

private theorem traversal_972 (fuel : Nat) (hf : 972 < fuel) :
    walk nodes fuel 972 = List.range' 972 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 972).rule = .bound .leftEnd 8 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_973 (fuel : Nat) (hf : 973 < fuel) :
    walk nodes fuel 973 = List.range' 973 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 973).rule = .bound .leftEnd 8 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_974 (fuel : Nat) (hf : 974 < fuel) :
    walk nodes fuel 974 = List.range' 974 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 974).rule = .bound .leftEnd 8 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_975 (fuel : Nat) (hf : 975 < fuel) :
    walk nodes fuel 975 = List.range' 975 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 975).rule = .bound .leftEnd 8 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_976 (fuel : Nat) (hf : 976 < fuel) :
    walk nodes fuel 976 = List.range' 976 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 976).rule = .bound .leftEnd 1 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_977 (fuel : Nat) (hf : 977 < fuel) :
    walk nodes fuel 977 = List.range' 977 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 977).rule = .bound .leftEnd 2 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_978 (fuel : Nat) (hf : 978 < fuel) :
    walk nodes fuel 978 = List.range' 978 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 978).rule = .bound .leftEnd 1 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_979 (fuel : Nat) (hf : 979 < fuel) :
    walk nodes fuel 979 = List.range' 977 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 979).rule = .split 3 (7323/8192) 977 978 := by rfl
      simp only [walk, hr]
      rw [traversal_977 f (by omega), traversal_978 f (by omega)]
      change (List.range' 977 1 ++ List.range' (977+1) 1) ++
        [977+(1+1)] = List.range' 977 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 977) (n := 1+1)).symm

private theorem traversal_980 (fuel : Nat) (hf : 980 < fuel) :
    walk nodes fuel 980 = List.range' 976 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 980).rule = .split 2 (73229/32768) 976 979 := by rfl
      simp only [walk, hr]
      rw [traversal_976 f (by omega), traversal_979 f (by omega)]
      change (List.range' 976 1 ++ List.range' (976+1) 3) ++
        [976+(1+3)] = List.range' 976 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 976) (n := 1+3)).symm

private theorem traversal_981 (fuel : Nat) (hf : 981 < fuel) :
    walk nodes fuel 981 = List.range' 975 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 981).rule = .split 1 (18735/8192) 975 980 := by rfl
      simp only [walk, hr]
      rw [traversal_975 f (by omega), traversal_980 f (by omega)]
      change (List.range' 975 1 ++ List.range' (975+1) 5) ++
        [975+(1+5)] = List.range' 975 ((1+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 975) (n := 1+5)).symm

private theorem traversal_982 (fuel : Nat) (hf : 982 < fuel) :
    walk nodes fuel 982 = List.range' 982 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 982).rule = .bound .leftEnd 8 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_983 (fuel : Nat) (hf : 983 < fuel) :
    walk nodes fuel 983 = List.range' 983 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 983).rule = .bound .leftEnd 1 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_984 (fuel : Nat) (hf : 984 < fuel) :
    walk nodes fuel 984 = List.range' 982 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 984).rule = .split 1 (18735/8192) 982 983 := by rfl
      simp only [walk, hr]
      rw [traversal_982 f (by omega), traversal_983 f (by omega)]
      change (List.range' 982 1 ++ List.range' (982+1) 1) ++
        [982+(1+1)] = List.range' 982 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 982) (n := 1+1)).symm

private theorem traversal_985 (fuel : Nat) (hf : 985 < fuel) :
    walk nodes fuel 985 = List.range' 975 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 985).rule = .split 0 (1/10240) 981 984 := by rfl
      simp only [walk, hr]
      rw [traversal_981 f (by omega), traversal_984 f (by omega)]
      change (List.range' 975 7 ++ List.range' (975+7) 3) ++
        [975+(7+3)] = List.range' 975 ((7+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 975) (n := 7+3)).symm

private theorem traversal_986 (fuel : Nat) (hf : 986 < fuel) :
    walk nodes fuel 986 = List.range' 986 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 986).rule = .bound .leftEnd 1 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_987 (fuel : Nat) (hf : 987 < fuel) :
    walk nodes fuel 987 = List.range' 975 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 987).rule = .split 3 (3663/4096) 985 986 := by rfl
      simp only [walk, hr]
      rw [traversal_985 f (by omega), traversal_986 f (by omega)]
      change (List.range' 975 11 ++ List.range' (975+11) 1) ++
        [975+(11+1)] = List.range' 975 ((11+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 975) (n := 11+1)).symm

private theorem traversal_988 (fuel : Nat) (hf : 988 < fuel) :
    walk nodes fuel 988 = List.range' 974 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 988).rule = .split 2 (36605/16384) 974 987 := by rfl
      simp only [walk, hr]
      rw [traversal_974 f (by omega), traversal_987 f (by omega)]
      change (List.range' 974 1 ++ List.range' (974+1) 13) ++
        [974+(1+13)] = List.range' 974 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 974) (n := 1+13)).symm

private theorem traversal_989 (fuel : Nat) (hf : 989 < fuel) :
    walk nodes fuel 989 = List.range' 973 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 989).rule = .split 1 (9365/4096) 973 988 := by rfl
      simp only [walk, hr]
      rw [traversal_973 f (by omega), traversal_988 f (by omega)]
      change (List.range' 973 1 ++ List.range' (973+1) 15) ++
        [973+(1+15)] = List.range' 973 ((1+15)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 973) (n := 1+15)).symm

private theorem traversal_990 (fuel : Nat) (hf : 990 < fuel) :
    walk nodes fuel 990 = List.range' 990 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 990).rule = .bound .leftEnd 8 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_991 (fuel : Nat) (hf : 991 < fuel) :
    walk nodes fuel 991 = List.range' 991 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 991).rule = .bound .leftEnd 1 (203/384) (247939/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_992 (fuel : Nat) (hf : 992 < fuel) :
    walk nodes fuel 992 = List.range' 990 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 992).rule = .split 1 (9365/4096) 990 991 := by rfl
      simp only [walk, hr]
      rw [traversal_990 f (by omega), traversal_991 f (by omega)]
      change (List.range' 990 1 ++ List.range' (990+1) 1) ++
        [990+(1+1)] = List.range' 990 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 990) (n := 1+1)).symm

private theorem traversal_993 (fuel : Nat) (hf : 993 < fuel) :
    walk nodes fuel 993 = List.range' 973 21 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 993).rule = .split 0 (1/5120) 989 992 := by rfl
      simp only [walk, hr]
      rw [traversal_989 f (by omega), traversal_992 f (by omega)]
      change (List.range' 973 17 ++ List.range' (973+17) 3) ++
        [973+(17+3)] = List.range' 973 ((17+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 973) (n := 17+3)).symm

private theorem traversal_994 (fuel : Nat) (hf : 994 < fuel) :
    walk nodes fuel 994 = List.range' 994 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 994).rule = .bound .leftEnd 1 (811/1536) (496489/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_995 (fuel : Nat) (hf : 995 < fuel) :
    walk nodes fuel 995 = List.range' 973 23 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 995).rule = .split 3 (1833/2048) 993 994 := by rfl
      simp only [walk, hr]
      rw [traversal_993 f (by omega), traversal_994 f (by omega)]
      change (List.range' 973 21 ++ List.range' (973+21) 1) ++
        [973+(21+1)] = List.range' 973 ((21+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 973) (n := 21+1)).symm

private theorem traversal_996 (fuel : Nat) (hf : 996 < fuel) :
    walk nodes fuel 996 = List.range' 972 25 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 996).rule = .split 2 (18293/8192) 972 995 := by rfl
      simp only [walk, hr]
      rw [traversal_972 f (by omega), traversal_995 f (by omega)]
      change (List.range' 972 1 ++ List.range' (972+1) 23) ++
        [972+(1+23)] = List.range' 972 ((1+23)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 972) (n := 1+23)).symm

private theorem traversal_997 (fuel : Nat) (hf : 997 < fuel) :
    walk nodes fuel 997 = List.range' 997 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 997).rule = .bound .leftEnd 1 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_998 (fuel : Nat) (hf : 998 < fuel) :
    walk nodes fuel 998 = List.range' 972 27 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 998).rule = .split 1 (4685/2048) 996 997 := by rfl
      simp only [walk, hr]
      rw [traversal_996 f (by omega), traversal_997 f (by omega)]
      change (List.range' 972 25 ++ List.range' (972+25) 1) ++
        [972+(25+1)] = List.range' 972 ((25+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 972) (n := 25+1)).symm

private theorem traversal_999 (fuel : Nat) (hf : 999 < fuel) :
    walk nodes fuel 999 = List.range' 999 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 999).rule = .bound .leftEnd 1 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_1000 (fuel : Nat) (hf : 1000 < fuel) :
    walk nodes fuel 1000 = List.range' 972 29 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1000).rule = .split 0 (1/2560) 998 999 := by rfl
      simp only [walk, hr]
      rw [traversal_998 f (by omega), traversal_999 f (by omega)]
      change (List.range' 972 27 ++ List.range' (972+27) 1) ++
        [972+(27+1)] = List.range' 972 ((27+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 972) (n := 27+1)).symm

private theorem traversal_1001 (fuel : Nat) (hf : 1001 < fuel) :
    walk nodes fuel 1001 = List.range' 927 75 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1001).rule = .split 3 (915/1024) 971 1000 := by rfl
      simp only [walk, hr]
      rw [traversal_971 f (by omega), traversal_1000 f (by omega)]
      change (List.range' 927 45 ++ List.range' (927+45) 29) ++
        [927+(45+29)] = List.range' 927 ((45+29)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 927) (n := 45+29)).symm

theorem traversal_1002 (fuel : Nat) (hf : 1002 < fuel) :
    walk nodes fuel 1002 = List.range' 908 95 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1002).rule = .split 2 (9137/4096) 926 1001 := by rfl
      simp only [walk, hr]
      rw [traversal_926 f (by omega), traversal_1001 f (by omega)]
      change (List.range' 908 19 ++ List.range' (908+19) 75) ++
        [908+(19+75)] = List.range' 908 ((19+75)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 908) (n := 19+75)).symm

theorem traversal_1003 (fuel : Nat) (hf : 1003 < fuel) :
    walk nodes fuel 1003 = List.range' 1003 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1003).rule = .bound .leftEnd 1 (1625/3072) (495571/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1004 (fuel : Nat) (hf : 1004 < fuel) :
    walk nodes fuel 1004 = List.range' 1004 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1004).rule = .bound .leftEnd 2 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_1005 (fuel : Nat) (hf : 1005 < fuel) :
    walk nodes fuel 1005 = List.range' 1005 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 1005).rule = .bound .leftEnd 1 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
