/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; premises=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13.traversal_906,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13.traversal_907,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13.traversal_926,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13.traversal_929,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13.traversal_930,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13.traversal_931,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13.traversal_932,D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Traversal/N25APart13.traversal_939
   digest: Exact structural traversal and local numerical premises of the same full scalar reduction. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Traversal.N25APart12
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
private theorem traversal_873 (fuel : Nat) (hf : 873 < fuel) :
    walk nodes fuel 873 = List.range' 867 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 873).rule = .split 0 (1/1280) 871 872 := by rfl
      simp only [walk, hr]
      rw [traversal_871 f (by omega), traversal_872 f (by omega)]
      change (List.range' 867 5 ++ List.range' (867+5) 1) ++
        [867+(5+1)] = List.range' 867 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 867) (n := 5+1)).symm

private theorem traversal_874 (fuel : Nat) (hf : 874 < fuel) :
    walk nodes fuel 874 = List.range' 874 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 874).rule = .bound .leftEnd 8 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_875 (fuel : Nat) (hf : 875 < fuel) :
    walk nodes fuel 875 = List.range' 875 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 875).rule = .bound .leftEnd 3 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_876 (fuel : Nat) (hf : 876 < fuel) :
    walk nodes fuel 876 = List.range' 874 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 876).rule = .split 1 (2335/1024) 874 875 := by rfl
      simp only [walk, hr]
      rw [traversal_874 f (by omega), traversal_875 f (by omega)]
      change (List.range' 874 1 ++ List.range' (874+1) 1) ++
        [874+(1+1)] = List.range' 874 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 874) (n := 1+1)).symm

private theorem traversal_877 (fuel : Nat) (hf : 877 < fuel) :
    walk nodes fuel 877 = List.range' 877 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 877).rule = .bound .leftEnd 3 (3239/6144) (248627/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_878 (fuel : Nat) (hf : 878 < fuel) :
    walk nodes fuel 878 = List.range' 874 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 878).rule = .split 0 (1/1280) 876 877 := by rfl
      simp only [walk, hr]
      rw [traversal_876 f (by omega), traversal_877 f (by omega)]
      change (List.range' 874 3 ++ List.range' (874+3) 1) ++
        [874+(3+1)] = List.range' 874 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 874) (n := 3+1)).symm

private theorem traversal_879 (fuel : Nat) (hf : 879 < fuel) :
    walk nodes fuel 879 = List.range' 867 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 879).rule = .split 3 (459/512) 873 878 := by rfl
      simp only [walk, hr]
      rw [traversal_873 f (by omega), traversal_878 f (by omega)]
      change (List.range' 867 7 ++ List.range' (867+7) 5) ++
        [867+(7+5)] = List.range' 867 ((7+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 867) (n := 7+5)).symm

private theorem traversal_880 (fuel : Nat) (hf : 880 < fuel) :
    walk nodes fuel 880 = List.range' 830 51 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 880).rule = .split 2 (4597/2048) 866 879 := by rfl
      simp only [walk, hr]
      rw [traversal_866 f (by omega), traversal_879 f (by omega)]
      change (List.range' 830 37 ++ List.range' (830+37) 13) ++
        [830+(37+13)] = List.range' 830 ((37+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 830) (n := 37+13)).symm

private theorem traversal_881 (fuel : Nat) (hf : 881 < fuel) :
    walk nodes fuel 881 = List.range' 829 53 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 881).rule = .split 1 (1165/512) 829 880 := by rfl
      simp only [walk, hr]
      rw [traversal_829 f (by omega), traversal_880 f (by omega)]
      change (List.range' 829 1 ++ List.range' (829+1) 51) ++
        [829+(1+51)] = List.range' 829 ((1+51)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 829) (n := 1+51)).symm

private theorem traversal_882 (fuel : Nat) (hf : 882 < fuel) :
    walk nodes fuel 882 = List.range' 882 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 882).rule = .bound .leftEnd 8 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_883 (fuel : Nat) (hf : 883 < fuel) :
    walk nodes fuel 883 = List.range' 883 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 883).rule = .bound .leftEnd 3 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_884 (fuel : Nat) (hf : 884 < fuel) :
    walk nodes fuel 884 = List.range' 882 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 884).rule = .split 1 (1165/512) 882 883 := by rfl
      simp only [walk, hr]
      rw [traversal_882 f (by omega), traversal_883 f (by omega)]
      change (List.range' 882 1 ++ List.range' (882+1) 1) ++
        [882+(1+1)] = List.range' 882 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 882) (n := 1+1)).symm

private theorem traversal_885 (fuel : Nat) (hf : 885 < fuel) :
    walk nodes fuel 885 = List.range' 829 57 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 885).rule = .split 0 (1/640) 881 884 := by rfl
      simp only [walk, hr]
      rw [traversal_881 f (by omega), traversal_884 f (by omega)]
      change (List.range' 829 53 ++ List.range' (829+53) 3) ++
        [829+(53+3)] = List.range' 829 ((53+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 829) (n := 53+3)).symm

private theorem traversal_886 (fuel : Nat) (hf : 886 < fuel) :
    walk nodes fuel 886 = List.range' 886 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 886).rule = .bound .leftEnd 8 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_887 (fuel : Nat) (hf : 887 < fuel) :
    walk nodes fuel 887 = List.range' 887 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 887).rule = .bound .leftEnd 8 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_888 (fuel : Nat) (hf : 888 < fuel) :
    walk nodes fuel 888 = List.range' 888 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 888).rule = .bound .leftEnd 8 (3229/6144) (249397/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_889 (fuel : Nat) (hf : 889 < fuel) :
    walk nodes fuel 889 = List.range' 889 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 889).rule = .bound .leftEnd 3 (3229/6144) (249397/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_890 (fuel : Nat) (hf : 890 < fuel) :
    walk nodes fuel 890 = List.range' 888 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 890).rule = .split 1 (2335/1024) 888 889 := by rfl
      simp only [walk, hr]
      rw [traversal_888 f (by omega), traversal_889 f (by omega)]
      change (List.range' 888 1 ++ List.range' (888+1) 1) ++
        [888+(1+1)] = List.range' 888 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 888) (n := 1+1)).symm

private theorem traversal_891 (fuel : Nat) (hf : 891 < fuel) :
    walk nodes fuel 891 = List.range' 891 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 891).rule = .bound .leftEnd 3 (3229/6144) (249397/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_892 (fuel : Nat) (hf : 892 < fuel) :
    walk nodes fuel 892 = List.range' 888 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 892).rule = .split 0 (1/1280) 890 891 := by rfl
      simp only [walk, hr]
      rw [traversal_890 f (by omega), traversal_891 f (by omega)]
      change (List.range' 888 3 ++ List.range' (888+3) 1) ++
        [888+(3+1)] = List.range' 888 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 888) (n := 3+1)).symm

private theorem traversal_893 (fuel : Nat) (hf : 893 < fuel) :
    walk nodes fuel 893 = List.range' 893 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 893).rule = .bound .leftEnd 8 (1073/2048) (62543/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_894 (fuel : Nat) (hf : 894 < fuel) :
    walk nodes fuel 894 = List.range' 894 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 894).rule = .bound .leftEnd 1 (1073/2048) (62543/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_895 (fuel : Nat) (hf : 895 < fuel) :
    walk nodes fuel 895 = List.range' 893 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 895).rule = .split 1 (2335/1024) 893 894 := by rfl
      simp only [walk, hr]
      rw [traversal_893 f (by omega), traversal_894 f (by omega)]
      change (List.range' 893 1 ++ List.range' (893+1) 1) ++
        [893+(1+1)] = List.range' 893 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 893) (n := 1+1)).symm

private theorem traversal_896 (fuel : Nat) (hf : 896 < fuel) :
    walk nodes fuel 896 = List.range' 896 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 896).rule = .bound .leftEnd 1 (1073/2048) (62543/131072) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_897 (fuel : Nat) (hf : 897 < fuel) :
    walk nodes fuel 897 = List.range' 893 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 897).rule = .split 0 (1/1280) 895 896 := by rfl
      simp only [walk, hr]
      rw [traversal_895 f (by omega), traversal_896 f (by omega)]
      change (List.range' 893 3 ++ List.range' (893+3) 1) ++
        [893+(3+1)] = List.range' 893 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 893) (n := 3+1)).symm

private theorem traversal_898 (fuel : Nat) (hf : 898 < fuel) :
    walk nodes fuel 898 = List.range' 888 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 898).rule = .split 3 (465/512) 892 897 := by rfl
      simp only [walk, hr]
      rw [traversal_892 f (by omega), traversal_897 f (by omega)]
      change (List.range' 888 5 ++ List.range' (888+5) 5) ++
        [888+(5+5)] = List.range' 888 ((5+5)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 888) (n := 5+5)).symm

private theorem traversal_899 (fuel : Nat) (hf : 899 < fuel) :
    walk nodes fuel 899 = List.range' 887 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 899).rule = .split 2 (4597/2048) 887 898 := by rfl
      simp only [walk, hr]
      rw [traversal_887 f (by omega), traversal_898 f (by omega)]
      change (List.range' 887 1 ++ List.range' (887+1) 11) ++
        [887+(1+11)] = List.range' 887 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 887) (n := 1+11)).symm

private theorem traversal_900 (fuel : Nat) (hf : 900 < fuel) :
    walk nodes fuel 900 = List.range' 886 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 900).rule = .split 1 (1165/512) 886 899 := by rfl
      simp only [walk, hr]
      rw [traversal_886 f (by omega), traversal_899 f (by omega)]
      change (List.range' 886 1 ++ List.range' (886+1) 13) ++
        [886+(1+13)] = List.range' 886 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 886) (n := 1+13)).symm

private theorem traversal_901 (fuel : Nat) (hf : 901 < fuel) :
    walk nodes fuel 901 = List.range' 901 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 901).rule = .bound .leftEnd 8 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_902 (fuel : Nat) (hf : 902 < fuel) :
    walk nodes fuel 902 = List.range' 902 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 902).rule = .bound .leftEnd 1 (403/768) (124891/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_903 (fuel : Nat) (hf : 903 < fuel) :
    walk nodes fuel 903 = List.range' 901 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 903).rule = .split 1 (1165/512) 901 902 := by rfl
      simp only [walk, hr]
      rw [traversal_901 f (by omega), traversal_902 f (by omega)]
      change (List.range' 901 1 ++ List.range' (901+1) 1) ++
        [901+(1+1)] = List.range' 901 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 901) (n := 1+1)).symm

private theorem traversal_904 (fuel : Nat) (hf : 904 < fuel) :
    walk nodes fuel 904 = List.range' 886 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 904).rule = .split 0 (1/640) 900 903 := by rfl
      simp only [walk, hr]
      rw [traversal_900 f (by omega), traversal_903 f (by omega)]
      change (List.range' 886 15 ++ List.range' (886+15) 3) ++
        [886+(15+3)] = List.range' 886 ((15+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 886) (n := 15+3)).symm

private theorem traversal_905 (fuel : Nat) (hf : 905 < fuel) :
    walk nodes fuel 905 = List.range' 829 77 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 905).rule = .split 3 (231/256) 885 904 := by rfl
      simp only [walk, hr]
      rw [traversal_885 f (by omega), traversal_904 f (by omega)]
      change (List.range' 829 57 ++ List.range' (829+57) 19) ++
        [829+(57+19)] = List.range' 829 ((57+19)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 829) (n := 57+19)).symm

theorem traversal_906 (fuel : Nat) (hf : 906 < fuel) :
    walk nodes fuel 906 = List.range' 828 79 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 906).rule = .split 2 (2289/1024) 828 905 := by rfl
      simp only [walk, hr]
      rw [traversal_828 f (by omega), traversal_905 f (by omega)]
      change (List.range' 828 1 ++ List.range' (828+1) 77) ++
        [828+(1+77)] = List.range' 828 ((1+77)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 828) (n := 1+77)).symm

theorem traversal_907 (fuel : Nat) (hf : 907 < fuel) :
    walk nodes fuel 907 = List.range' 907 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 907).rule = .bound .leftEnd 1 (2163/4096) (496407/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_908 (fuel : Nat) (hf : 908 < fuel) :
    walk nodes fuel 908 = List.range' 908 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 908).rule = .bound .leftEnd 8 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_909 (fuel : Nat) (hf : 909 < fuel) :
    walk nodes fuel 909 = List.range' 909 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 909).rule = .bound .leftEnd 1 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_910 (fuel : Nat) (hf : 910 < fuel) :
    walk nodes fuel 910 = List.range' 910 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 910).rule = .bound .leftEnd 2 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_911 (fuel : Nat) (hf : 911 < fuel) :
    walk nodes fuel 911 = List.range' 911 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 911).rule = .bound .leftEnd 1 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_912 (fuel : Nat) (hf : 912 < fuel) :
    walk nodes fuel 912 = List.range' 910 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 912).rule = .split 3 (3651/4096) 910 911 := by rfl
      simp only [walk, hr]
      rw [traversal_910 f (by omega), traversal_911 f (by omega)]
      change (List.range' 910 1 ++ List.range' (910+1) 1) ++
        [910+(1+1)] = List.range' 910 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 910) (n := 1+1)).symm

private theorem traversal_913 (fuel : Nat) (hf : 913 < fuel) :
    walk nodes fuel 913 = List.range' 913 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 913).rule = .bound .leftEnd 2 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_914 (fuel : Nat) (hf : 914 < fuel) :
    walk nodes fuel 914 = List.range' 910 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 914).rule = .split 2 (36529/16384) 912 913 := by rfl
      simp only [walk, hr]
      rw [traversal_912 f (by omega), traversal_913 f (by omega)]
      change (List.range' 910 3 ++ List.range' (910+3) 1) ++
        [910+(3+1)] = List.range' 910 ((3+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 910) (n := 3+1)).symm

private theorem traversal_915 (fuel : Nat) (hf : 915 < fuel) :
    walk nodes fuel 915 = List.range' 915 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 915).rule = .bound .leftEnd 2 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_916 (fuel : Nat) (hf : 916 < fuel) :
    walk nodes fuel 916 = List.range' 910 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 916).rule = .split 1 (9375/4096) 914 915 := by rfl
      simp only [walk, hr]
      rw [traversal_914 f (by omega), traversal_915 f (by omega)]
      change (List.range' 910 5 ++ List.range' (910+5) 1) ++
        [910+(5+1)] = List.range' 910 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 910) (n := 5+1)).symm

private theorem traversal_917 (fuel : Nat) (hf : 917 < fuel) :
    walk nodes fuel 917 = List.range' 917 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 917).rule = .bound .leftEnd 1 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_918 (fuel : Nat) (hf : 918 < fuel) :
    walk nodes fuel 918 = List.range' 910 9 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 918).rule = .split 0 (1/5120) 916 917 := by rfl
      simp only [walk, hr]
      rw [traversal_916 f (by omega), traversal_917 f (by omega)]
      change (List.range' 910 7 ++ List.range' (910+7) 1) ++
        [910+(7+1)] = List.range' 910 ((7+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 910) (n := 7+1)).symm

private theorem traversal_919 (fuel : Nat) (hf : 919 < fuel) :
    walk nodes fuel 919 = List.range' 919 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 919).rule = .bound .leftEnd 1 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_920 (fuel : Nat) (hf : 920 < fuel) :
    walk nodes fuel 920 = List.range' 910 11 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 920).rule = .split 3 (1827/2048) 918 919 := by rfl
      simp only [walk, hr]
      rw [traversal_918 f (by omega), traversal_919 f (by omega)]
      change (List.range' 910 9 ++ List.range' (910+9) 1) ++
        [910+(9+1)] = List.range' 910 ((9+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 910) (n := 9+1)).symm

private theorem traversal_921 (fuel : Nat) (hf : 921 < fuel) :
    walk nodes fuel 921 = List.range' 909 13 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 921).rule = .split 2 (18255/8192) 909 920 := by rfl
      simp only [walk, hr]
      rw [traversal_909 f (by omega), traversal_920 f (by omega)]
      change (List.range' 909 1 ++ List.range' (909+1) 11) ++
        [909+(1+11)] = List.range' 909 ((1+11)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 909) (n := 1+11)).symm

private theorem traversal_922 (fuel : Nat) (hf : 922 < fuel) :
    walk nodes fuel 922 = List.range' 908 15 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 922).rule = .split 1 (4685/2048) 908 921 := by rfl
      simp only [walk, hr]
      rw [traversal_908 f (by omega), traversal_921 f (by omega)]
      change (List.range' 908 1 ++ List.range' (908+1) 13) ++
        [908+(1+13)] = List.range' 908 ((1+13)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 908) (n := 1+13)).symm

private theorem traversal_923 (fuel : Nat) (hf : 923 < fuel) :
    walk nodes fuel 923 = List.range' 923 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 923).rule = .bound .leftEnd 1 (1627/3072) (494963/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_924 (fuel : Nat) (hf : 924 < fuel) :
    walk nodes fuel 924 = List.range' 908 17 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 924).rule = .split 0 (1/2560) 922 923 := by rfl
      simp only [walk, hr]
      rw [traversal_922 f (by omega), traversal_923 f (by omega)]
      change (List.range' 908 15 ++ List.range' (908+15) 1) ++
        [908+(15+1)] = List.range' 908 ((15+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 908) (n := 15+1)).symm

private theorem traversal_925 (fuel : Nat) (hf : 925 < fuel) :
    walk nodes fuel 925 = List.range' 925 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 925).rule = .bound .leftEnd 1 (541/1024) (496183/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_926 (fuel : Nat) (hf : 926 < fuel) :
    walk nodes fuel 926 = List.range' 908 19 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 926).rule = .split 3 (915/1024) 924 925 := by rfl
      simp only [walk, hr]
      rw [traversal_924 f (by omega), traversal_925 f (by omega)]
      change (List.range' 908 17 ++ List.range' (908+17) 1) ++
        [908+(17+1)] = List.range' 908 ((17+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 908) (n := 17+1)).symm

private theorem traversal_927 (fuel : Nat) (hf : 927 < fuel) :
    walk nodes fuel 927 = List.range' 927 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 927).rule = .bound .leftEnd 2 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_928 (fuel : Nat) (hf : 928 < fuel) :
    walk nodes fuel 928 = List.range' 928 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 928).rule = .bound .leftEnd 8 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_929 (fuel : Nat) (hf : 929 < fuel) :
    walk nodes fuel 929 = List.range' 927 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 929).rule = .split 3 (1827/2048) 927 928 := by rfl
      simp only [walk, hr]
      rw [traversal_927 f (by omega), traversal_928 f (by omega)]
      change (List.range' 927 1 ++ List.range' (927+1) 1) ++
        [927+(1+1)] = List.range' 927 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 927) (n := 1+1)).symm

theorem traversal_930 (fuel : Nat) (hf : 930 < fuel) :
    walk nodes fuel 930 = List.range' 930 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 930).rule = .bound .leftEnd 2 (407/768) (494659/1048576) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_931 (fuel : Nat) (hf : 931 < fuel) :
    walk nodes fuel 931 = List.range' 931 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 931).rule = .bound .leftEnd 8 (271/512) (123817/262144) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_932 (fuel : Nat) (hf : 932 < fuel) :
    walk nodes fuel 932 = List.range' 932 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 932).rule = .bound .leftEnd 2 (203/384) (495877/1048576) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_933 (fuel : Nat) (hf : 933 < fuel) :
    walk nodes fuel 933 = List.range' 933 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 933).rule = .bound .leftEnd 8 (407/768) (247329/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_934 (fuel : Nat) (hf : 934 < fuel) :
    walk nodes fuel 934 = List.range' 934 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 934).rule = .bound .leftEnd 8 (407/768) (247329/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_935 (fuel : Nat) (hf : 935 < fuel) :
    walk nodes fuel 935 = List.range' 935 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 935).rule = .bound .leftEnd 2 (407/768) (247329/524288) := by rfl
      simp only [walk, hr]
      rfl

private theorem traversal_936 (fuel : Nat) (hf : 936 < fuel) :
    walk nodes fuel 936 = List.range' 934 3 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 936).rule = .split 2 (73191/32768) 934 935 := by rfl
      simp only [walk, hr]
      rw [traversal_934 f (by omega), traversal_935 f (by omega)]
      change (List.range' 934 1 ++ List.range' (934+1) 1) ++
        [934+(1+1)] = List.range' 934 ((1+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 934) (n := 1+1)).symm

private theorem traversal_937 (fuel : Nat) (hf : 937 < fuel) :
    walk nodes fuel 937 = List.range' 933 5 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 937).rule = .split 1 (18735/8192) 933 936 := by rfl
      simp only [walk, hr]
      rw [traversal_933 f (by omega), traversal_936 f (by omega)]
      change (List.range' 933 1 ++ List.range' (933+1) 3) ++
        [933+(1+3)] = List.range' 933 ((1+3)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 933) (n := 1+3)).symm

private theorem traversal_938 (fuel : Nat) (hf : 938 < fuel) :
    walk nodes fuel 938 = List.range' 938 1 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 938).rule = .bound .leftEnd 2 (407/768) (247329/524288) := by rfl
      simp only [walk, hr]
      rfl

theorem traversal_939 (fuel : Nat) (hf : 939 < fuel) :
    walk nodes fuel 939 = List.range' 933 7 := by
  cases fuel with
  | zero => omega
  | succ f =>
      have hr : (node nodes 939).rule = .split 0 (1/10240) 937 938 := by rfl
      simp only [walk, hr]
      rw [traversal_937 f (by omega), traversal_938 f (by omega)]
      change (List.range' 933 5 ++ List.range' (933+5) 1) ++
        [933+(5+1)] = List.range' 933 ((5+1)+1)
      rw [List.range'_append_1]
      exact (List.range'_1_concat (s := 933) (n := 5+1)).symm
end D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
