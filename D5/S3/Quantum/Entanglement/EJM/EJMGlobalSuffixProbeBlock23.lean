/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock23
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock23
   mirror-E: none(waiver:actual-global-cover-kernel-probe)
   anchors: []
   utility: none
   digest: Exact full subtree leaf receipts and every four-child split are assembled without changing their actual contexts. -/

/- Same complete existing-cover suffix. This is computational staging of the
original actual cache/partial expressions and all four branches. Native input
is untrusted. Only canonical kernel compilation earns each receipt. These
receipts close this exact suffix, not the complete global refutation. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock23
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1004 : Cache :=
  step cache1003 ⟨17, by decide⟩ 0
private def partial1004 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1003 ⟨17, by decide⟩ (some 0)

private def cache1005 : Cache :=
  step cache1003 ⟨17, by decide⟩ 1
private def partial1005 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1003 ⟨17, by decide⟩ (some 1)

private def cache1006 : Cache :=
  step cache1005 ⟨18, by decide⟩ 0
private def partial1006 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1005 ⟨18, by decide⟩ (some 0)

private def cache1007 : Cache :=
  step cache1005 ⟨18, by decide⟩ 1
private def partial1007 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1005 ⟨18, by decide⟩ (some 1)

private def cache1008 : Cache :=
  step cache1007 ⟨19, by decide⟩ 0
private def partial1008 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1007 ⟨19, by decide⟩ (some 0)

private def cache1009 : Cache :=
  step cache1007 ⟨19, by decide⟩ 1
private def partial1009 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1007 ⟨19, by decide⟩ (some 1)

private def cache1010 : Cache :=
  step cache1007 ⟨19, by decide⟩ 2
private def partial1010 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1007 ⟨19, by decide⟩ (some 2)

private def cache1011 : Cache :=
  step cache1007 ⟨19, by decide⟩ 3
private def partial1011 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1007 ⟨19, by decide⟩ (some 3)

private def cache1012 : Cache :=
  step cache1005 ⟨18, by decide⟩ 2
private def partial1012 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1005 ⟨18, by decide⟩ (some 2)

private def cache1013 : Cache :=
  step cache1012 ⟨19, by decide⟩ 0
private def partial1013 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1012 ⟨19, by decide⟩ (some 0)

private def cache1014 : Cache :=
  step cache1012 ⟨19, by decide⟩ 1
private def partial1014 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1012 ⟨19, by decide⟩ (some 1)

private def cache1015 : Cache :=
  step cache1012 ⟨19, by decide⟩ 2
private def partial1015 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1012 ⟨19, by decide⟩ (some 2)

private def cache1016 : Cache :=
  step cache1012 ⟨19, by decide⟩ 3
private def partial1016 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1012 ⟨19, by decide⟩ (some 3)

private def cache1017 : Cache :=
  step cache1005 ⟨18, by decide⟩ 3
private def partial1017 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1005 ⟨18, by decide⟩ (some 3)

private def cache1018 : Cache :=
  step cache1017 ⟨19, by decide⟩ 0
private def partial1018 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1017 ⟨19, by decide⟩ (some 0)

private def cache1019 : Cache :=
  step cache1017 ⟨19, by decide⟩ 1
private def partial1019 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1017 ⟨19, by decide⟩ (some 1)

private def cache1020 : Cache :=
  step cache1017 ⟨19, by decide⟩ 2
private def partial1020 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1017 ⟨19, by decide⟩ (some 2)

private def cache1021 : Cache :=
  step cache1017 ⟨19, by decide⟩ 3
private def partial1021 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1017 ⟨19, by decide⟩ (some 3)

private def cache1022 : Cache :=
  step cache1003 ⟨17, by decide⟩ 2
private def partial1022 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1003 ⟨17, by decide⟩ (some 2)

private def cache1023 : Cache :=
  step cache1022 ⟨18, by decide⟩ 0
private def partial1023 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1022 ⟨18, by decide⟩ (some 0)

private def cache1024 : Cache :=
  step cache1023 ⟨19, by decide⟩ 0
private def partial1024 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1023 ⟨19, by decide⟩ (some 0)

private def cache1025 : Cache :=
  step cache1023 ⟨19, by decide⟩ 1
private def partial1025 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1023 ⟨19, by decide⟩ (some 1)

private def cache1026 : Cache :=
  step cache1023 ⟨19, by decide⟩ 2
private def partial1026 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1023 ⟨19, by decide⟩ (some 2)

private def cache1027 : Cache :=
  step cache1023 ⟨19, by decide⟩ 3
private def partial1027 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1023 ⟨19, by decide⟩ (some 3)

private def cache1028 : Cache :=
  step cache1022 ⟨18, by decide⟩ 1
private def partial1028 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1022 ⟨18, by decide⟩ (some 1)

private def cache1029 : Cache :=
  step cache1028 ⟨19, by decide⟩ 0
private def partial1029 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1028 ⟨19, by decide⟩ (some 0)

private def cache1030 : Cache :=
  step cache1028 ⟨19, by decide⟩ 1
private def partial1030 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1028 ⟨19, by decide⟩ (some 1)

private def cache1031 : Cache :=
  step cache1028 ⟨19, by decide⟩ 2
private def partial1031 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1028 ⟨19, by decide⟩ (some 2)

private def cache1032 : Cache :=
  step cache1028 ⟨19, by decide⟩ 3
private def partial1032 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1028 ⟨19, by decide⟩ (some 3)

private def cache1033 : Cache :=
  step cache1022 ⟨18, by decide⟩ 2
private def partial1033 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1022 ⟨18, by decide⟩ (some 2)

private def cache1034 : Cache :=
  step cache1033 ⟨19, by decide⟩ 0
private def partial1034 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1033 ⟨19, by decide⟩ (some 0)

private def cache1035 : Cache :=
  step cache1033 ⟨19, by decide⟩ 1
private def partial1035 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1033 ⟨19, by decide⟩ (some 1)

private def cache1036 : Cache :=
  step cache1033 ⟨19, by decide⟩ 2
private def partial1036 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1033 ⟨19, by decide⟩ (some 2)

private def cache1037 : Cache :=
  step cache1033 ⟨19, by decide⟩ 3
private def partial1037 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1033 ⟨19, by decide⟩ (some 3)

private def cache1038 : Cache :=
  step cache1022 ⟨18, by decide⟩ 3
private def partial1038 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1022 ⟨18, by decide⟩ (some 3)

private def cache1039 : Cache :=
  step cache1038 ⟨19, by decide⟩ 0
private def partial1039 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1038 ⟨19, by decide⟩ (some 0)

private def cache1040 : Cache :=
  step cache1038 ⟨19, by decide⟩ 1
private def partial1040 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1038 ⟨19, by decide⟩ (some 1)

private def cache1041 : Cache :=
  step cache1038 ⟨19, by decide⟩ 2
private def partial1041 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1038 ⟨19, by decide⟩ (some 2)

private def cache1042 : Cache :=
  step cache1038 ⟨19, by decide⟩ 3
private def partial1042 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1038 ⟨19, by decide⟩ (some 3)

private def cache1043 : Cache :=
  step cache1003 ⟨17, by decide⟩ 3
private def partial1043 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1003 ⟨17, by decide⟩ (some 3)

private def cache1044 : Cache :=
  step cache1043 ⟨18, by decide⟩ 0
private def partial1044 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1043 ⟨18, by decide⟩ (some 0)

private def cache1045 : Cache :=
  step cache1044 ⟨19, by decide⟩ 0
private def partial1045 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1044 ⟨19, by decide⟩ (some 0)

private def cache1046 : Cache :=
  step cache1044 ⟨19, by decide⟩ 1
private def partial1046 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1044 ⟨19, by decide⟩ (some 1)

private def cache1047 : Cache :=
  step cache1044 ⟨19, by decide⟩ 2
private def partial1047 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1044 ⟨19, by decide⟩ (some 2)

private def cache1048 : Cache :=
  step cache1044 ⟨19, by decide⟩ 3
private def partial1048 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1044 ⟨19, by decide⟩ (some 3)

private def cache1049 : Cache :=
  step cache1043 ⟨18, by decide⟩ 1
private def partial1049 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1043 ⟨18, by decide⟩ (some 1)

private def cache1050 : Cache :=
  step cache1049 ⟨19, by decide⟩ 0
private def partial1050 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1049 ⟨19, by decide⟩ (some 0)

private def cache1051 : Cache :=
  step cache1049 ⟨19, by decide⟩ 1
private def partial1051 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1049 ⟨19, by decide⟩ (some 1)

private def cache1052 : Cache :=
  step cache1049 ⟨19, by decide⟩ 2
private def partial1052 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1049 ⟨19, by decide⟩ (some 2)

private def cache1053 : Cache :=
  step cache1049 ⟨19, by decide⟩ 3
private def partial1053 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1049 ⟨19, by decide⟩ (some 3)

private def cache1054 : Cache :=
  step cache1043 ⟨18, by decide⟩ 2
private def partial1054 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1043 ⟨18, by decide⟩ (some 2)

private def cache1055 : Cache :=
  step cache1054 ⟨19, by decide⟩ 0
private def partial1055 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1054 ⟨19, by decide⟩ (some 0)

private def cache1056 : Cache :=
  step cache1054 ⟨19, by decide⟩ 1
private def partial1056 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1054 ⟨19, by decide⟩ (some 1)

private def cache1057 : Cache :=
  step cache1054 ⟨19, by decide⟩ 2
private def partial1057 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1054 ⟨19, by decide⟩ (some 2)

private def cache1058 : Cache :=
  step cache1054 ⟨19, by decide⟩ 3
private def partial1058 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1054 ⟨19, by decide⟩ (some 3)

private def cache1059 : Cache :=
  step cache1043 ⟨18, by decide⟩ 3
private def partial1059 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1043 ⟨18, by decide⟩ (some 3)

private def cache1060 : Cache :=
  step cache1059 ⟨19, by decide⟩ 0
private def partial1060 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1059 ⟨19, by decide⟩ (some 0)

private def cache1061 : Cache :=
  step cache1059 ⟨19, by decide⟩ 1
private def partial1061 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1059 ⟨19, by decide⟩ (some 1)

private def cache1062 : Cache :=
  step cache1059 ⟨19, by decide⟩ 2
private def partial1062 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1059 ⟨19, by decide⟩ (some 2)

private def cache1063 : Cache :=
  step cache1059 ⟨19, by decide⟩ 3
private def partial1063 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1059 ⟨19, by decide⟩ (some 3)

private theorem receipt1063 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1063, by decide⟩ cache1063 partial1063 = true := by
  decide +kernel

private theorem receipt1062 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1062, by decide⟩ cache1062 partial1062 = true := by
  decide +kernel

private theorem receipt1061 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1061, by decide⟩ cache1061 partial1061 = true := by
  decide +kernel

private theorem receipt1060 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1060, by decide⟩ cache1060 partial1060 = true := by
  decide +kernel

private theorem receipt1059 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1059, by decide⟩ cache1059 partial1059 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1060,1061,1062,1063])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2338132016661651 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1060
  · exact receipt1061
  · exact receipt1062
  · exact receipt1063

private theorem receipt1058 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1058, by decide⟩ cache1058 partial1058 = true := by
  decide +kernel

private theorem receipt1057 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1057, by decide⟩ cache1057 partial1057 = true := by
  decide +kernel

private theorem receipt1056 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1056, by decide⟩ cache1056 partial1056 = true := by
  decide +kernel

private theorem receipt1055 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1055, by decide⟩ cache1055 partial1055 = true := by
  decide +kernel

private theorem receipt1054 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1054, by decide⟩ cache1054 partial1054 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1055,1056,1057,1058])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2327134215373811 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1055
  · exact receipt1056
  · exact receipt1057
  · exact receipt1058

private theorem receipt1053 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1053, by decide⟩ cache1053 partial1053 = true := by
  decide +kernel

private theorem receipt1052 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1052, by decide⟩ cache1052 partial1052 = true := by
  decide +kernel

private theorem receipt1051 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1051, by decide⟩ cache1051 partial1051 = true := by
  decide +kernel

private theorem receipt1050 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1050, by decide⟩ cache1050 partial1050 = true := by
  decide +kernel

private theorem receipt1049 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1049, by decide⟩ cache1049 partial1049 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1050,1051,1052,1053])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2316136414085971 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1050
  · exact receipt1051
  · exact receipt1052
  · exact receipt1053

private theorem receipt1048 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1048, by decide⟩ cache1048 partial1048 = true := by
  decide +kernel

private theorem receipt1047 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1047, by decide⟩ cache1047 partial1047 = true := by
  decide +kernel

private theorem receipt1046 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1046, by decide⟩ cache1046 partial1046 = true := by
  decide +kernel

private theorem receipt1045 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1045, by decide⟩ cache1045 partial1045 = true := by
  decide +kernel

private theorem receipt1044 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1044, by decide⟩ cache1044 partial1044 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1045,1046,1047,1048])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2305138612798131 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1045
  · exact receipt1046
  · exact receipt1047
  · exact receipt1048

private theorem receipt1043 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1043, by decide⟩ cache1043 partial1043 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1044,1049,1054,1059])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2329331627098770 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1044
  · exact receipt1049
  · exact receipt1054
  · exact receipt1059

private theorem receipt1042 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1042, by decide⟩ cache1042 partial1042 = true := by
  decide +kernel

private theorem receipt1041 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1041, by decide⟩ cache1041 partial1041 = true := by
  decide +kernel

private theorem receipt1040 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1040, by decide⟩ cache1040 partial1040 = true := by
  decide +kernel

private theorem receipt1039 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1039, by decide⟩ cache1039 partial1039 = true := by
  decide +kernel

private theorem receipt1038 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1038, by decide⟩ cache1038 partial1038 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1039,1040,1041,1042])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2291941251252723 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1039
  · exact receipt1040
  · exact receipt1041
  · exact receipt1042

private theorem receipt1037 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1037, by decide⟩ cache1037 partial1037 = true := by
  decide +kernel

private theorem receipt1036 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1036, by decide⟩ cache1036 partial1036 = true := by
  decide +kernel

private theorem receipt1035 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1035, by decide⟩ cache1035 partial1035 = true := by
  decide +kernel

private theorem receipt1034 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1034, by decide⟩ cache1034 partial1034 = true := by
  decide +kernel

private theorem receipt1033 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1033, by decide⟩ cache1033 partial1033 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1034,1035,1036,1037])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2280943449964883 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1034
  · exact receipt1035
  · exact receipt1036
  · exact receipt1037

private theorem receipt1032 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1032, by decide⟩ cache1032 partial1032 = true := by
  decide +kernel

private theorem receipt1031 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1031, by decide⟩ cache1031 partial1031 = true := by
  decide +kernel

private theorem receipt1030 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1030, by decide⟩ cache1030 partial1030 = true := by
  decide +kernel

private theorem receipt1029 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1029, by decide⟩ cache1029 partial1029 = true := by
  decide +kernel

private theorem receipt1028 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1028, by decide⟩ cache1028 partial1028 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1029,1030,1031,1032])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2269945648677043 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1029
  · exact receipt1030
  · exact receipt1031
  · exact receipt1032

private theorem receipt1027 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1027, by decide⟩ cache1027 partial1027 = true := by
  decide +kernel

private theorem receipt1026 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1026, by decide⟩ cache1026 partial1026 = true := by
  decide +kernel

private theorem receipt1025 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1025, by decide⟩ cache1025 partial1025 = true := by
  decide +kernel

private theorem receipt1024 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1024, by decide⟩ cache1024 partial1024 = true := by
  decide +kernel

#print axioms receipt1024

private theorem receipt1023 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1023, by decide⟩ cache1023 partial1023 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1024,1025,1026,1027])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2258947847389203 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1024
  · exact receipt1025
  · exact receipt1026
  · exact receipt1027

private theorem receipt1022 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1022, by decide⟩ cache1022 partial1022 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1023,1028,1033,1038])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2283140861689842 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1023
  · exact receipt1028
  · exact receipt1033
  · exact receipt1038

private theorem receipt1021 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1021, by decide⟩ cache1021 partial1021 = true := by
  decide +kernel

private theorem receipt1020 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1020, by decide⟩ cache1020 partial1020 = true := by
  decide +kernel

private theorem receipt1019 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1019, by decide⟩ cache1019 partial1019 = true := by
  decide +kernel

private theorem receipt1018 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1018, by decide⟩ cache1018 partial1018 = true := by
  decide +kernel

private theorem receipt1017 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1017, by decide⟩ cache1017 partial1017 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1018,1019,1020,1021])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2245750485843795 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1018
  · exact receipt1019
  · exact receipt1020
  · exact receipt1021

private theorem receipt1016 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1016, by decide⟩ cache1016 partial1016 = true := by
  decide +kernel

private theorem receipt1015 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1015, by decide⟩ cache1015 partial1015 = true := by
  decide +kernel

private theorem receipt1014 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1014, by decide⟩ cache1014 partial1014 = true := by
  decide +kernel

private theorem receipt1013 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1013, by decide⟩ cache1013 partial1013 = true := by
  decide +kernel

private theorem receipt1012 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1012, by decide⟩ cache1012 partial1012 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1013,1014,1015,1016])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2234752684555955 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1013
  · exact receipt1014
  · exact receipt1015
  · exact receipt1016

private theorem receipt1011 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1011, by decide⟩ cache1011 partial1011 = true := by
  decide +kernel

private theorem receipt1010 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1010, by decide⟩ cache1010 partial1010 = true := by
  decide +kernel

private theorem receipt1009 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1009, by decide⟩ cache1009 partial1009 = true := by
  decide +kernel

private theorem receipt1008 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1008, by decide⟩ cache1008 partial1008 = true := by
  decide +kernel

private theorem receipt1007 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1007, by decide⟩ cache1007 partial1007 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1008,1009,1010,1011])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2223754883268115 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1008
  · exact receipt1009
  · exact receipt1010
  · exact receipt1011

private theorem receipt1006 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1006, by decide⟩ cache1006 partial1006 = true := by
  decide +kernel

private theorem receipt1005 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1005, by decide⟩ cache1005 partial1005 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1006,1007,1012,1017])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2236950096281042 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1006
  · exact receipt1007
  · exact receipt1012
  · exact receipt1017

private theorem receipt1004 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1004, by decide⟩ cache1004 partial1004 = true := by
  decide +kernel

theorem receipt1003 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1003, by decide⟩ cache1003 partial1003 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1004,1005,1022,1043])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2294130069372305 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1004
  · exact receipt1005
  · exact receipt1022
  · exact receipt1043


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock23
