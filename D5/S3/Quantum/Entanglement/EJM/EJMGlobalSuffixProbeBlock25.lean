/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock25
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock25
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock25
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache907 : Cache :=
  step cache906 ⟨17, by decide⟩ 0
private def partial907 : Partial (Fin 20) (Fin 4) :=
  Function.update partial906 ⟨17, by decide⟩ (some 0)

private def cache908 : Cache :=
  step cache906 ⟨17, by decide⟩ 1
private def partial908 : Partial (Fin 20) (Fin 4) :=
  Function.update partial906 ⟨17, by decide⟩ (some 1)

private def cache909 : Cache :=
  step cache908 ⟨18, by decide⟩ 0
private def partial909 : Partial (Fin 20) (Fin 4) :=
  Function.update partial908 ⟨18, by decide⟩ (some 0)

private def cache910 : Cache :=
  step cache908 ⟨18, by decide⟩ 1
private def partial910 : Partial (Fin 20) (Fin 4) :=
  Function.update partial908 ⟨18, by decide⟩ (some 1)

private def cache911 : Cache :=
  step cache910 ⟨19, by decide⟩ 0
private def partial911 : Partial (Fin 20) (Fin 4) :=
  Function.update partial910 ⟨19, by decide⟩ (some 0)

private def cache912 : Cache :=
  step cache910 ⟨19, by decide⟩ 1
private def partial912 : Partial (Fin 20) (Fin 4) :=
  Function.update partial910 ⟨19, by decide⟩ (some 1)

private def cache913 : Cache :=
  step cache910 ⟨19, by decide⟩ 2
private def partial913 : Partial (Fin 20) (Fin 4) :=
  Function.update partial910 ⟨19, by decide⟩ (some 2)

private def cache914 : Cache :=
  step cache910 ⟨19, by decide⟩ 3
private def partial914 : Partial (Fin 20) (Fin 4) :=
  Function.update partial910 ⟨19, by decide⟩ (some 3)

private def cache915 : Cache :=
  step cache908 ⟨18, by decide⟩ 2
private def partial915 : Partial (Fin 20) (Fin 4) :=
  Function.update partial908 ⟨18, by decide⟩ (some 2)

private def cache916 : Cache :=
  step cache908 ⟨18, by decide⟩ 3
private def partial916 : Partial (Fin 20) (Fin 4) :=
  Function.update partial908 ⟨18, by decide⟩ (some 3)

private def cache917 : Cache :=
  step cache916 ⟨19, by decide⟩ 0
private def partial917 : Partial (Fin 20) (Fin 4) :=
  Function.update partial916 ⟨19, by decide⟩ (some 0)

private def cache918 : Cache :=
  step cache916 ⟨19, by decide⟩ 1
private def partial918 : Partial (Fin 20) (Fin 4) :=
  Function.update partial916 ⟨19, by decide⟩ (some 1)

private def cache919 : Cache :=
  step cache916 ⟨19, by decide⟩ 2
private def partial919 : Partial (Fin 20) (Fin 4) :=
  Function.update partial916 ⟨19, by decide⟩ (some 2)

private def cache920 : Cache :=
  step cache916 ⟨19, by decide⟩ 3
private def partial920 : Partial (Fin 20) (Fin 4) :=
  Function.update partial916 ⟨19, by decide⟩ (some 3)

private def cache921 : Cache :=
  step cache906 ⟨17, by decide⟩ 2
private def partial921 : Partial (Fin 20) (Fin 4) :=
  Function.update partial906 ⟨17, by decide⟩ (some 2)

private def cache922 : Cache :=
  step cache921 ⟨18, by decide⟩ 0
private def partial922 : Partial (Fin 20) (Fin 4) :=
  Function.update partial921 ⟨18, by decide⟩ (some 0)

private def cache923 : Cache :=
  step cache922 ⟨19, by decide⟩ 0
private def partial923 : Partial (Fin 20) (Fin 4) :=
  Function.update partial922 ⟨19, by decide⟩ (some 0)

private def cache924 : Cache :=
  step cache922 ⟨19, by decide⟩ 1
private def partial924 : Partial (Fin 20) (Fin 4) :=
  Function.update partial922 ⟨19, by decide⟩ (some 1)

private def cache925 : Cache :=
  step cache922 ⟨19, by decide⟩ 2
private def partial925 : Partial (Fin 20) (Fin 4) :=
  Function.update partial922 ⟨19, by decide⟩ (some 2)

private def cache926 : Cache :=
  step cache922 ⟨19, by decide⟩ 3
private def partial926 : Partial (Fin 20) (Fin 4) :=
  Function.update partial922 ⟨19, by decide⟩ (some 3)

private def cache927 : Cache :=
  step cache921 ⟨18, by decide⟩ 1
private def partial927 : Partial (Fin 20) (Fin 4) :=
  Function.update partial921 ⟨18, by decide⟩ (some 1)

private def cache928 : Cache :=
  step cache927 ⟨19, by decide⟩ 0
private def partial928 : Partial (Fin 20) (Fin 4) :=
  Function.update partial927 ⟨19, by decide⟩ (some 0)

private def cache929 : Cache :=
  step cache927 ⟨19, by decide⟩ 1
private def partial929 : Partial (Fin 20) (Fin 4) :=
  Function.update partial927 ⟨19, by decide⟩ (some 1)

private def cache930 : Cache :=
  step cache927 ⟨19, by decide⟩ 2
private def partial930 : Partial (Fin 20) (Fin 4) :=
  Function.update partial927 ⟨19, by decide⟩ (some 2)

private def cache931 : Cache :=
  step cache927 ⟨19, by decide⟩ 3
private def partial931 : Partial (Fin 20) (Fin 4) :=
  Function.update partial927 ⟨19, by decide⟩ (some 3)

private def cache932 : Cache :=
  step cache921 ⟨18, by decide⟩ 2
private def partial932 : Partial (Fin 20) (Fin 4) :=
  Function.update partial921 ⟨18, by decide⟩ (some 2)

private def cache933 : Cache :=
  step cache932 ⟨19, by decide⟩ 0
private def partial933 : Partial (Fin 20) (Fin 4) :=
  Function.update partial932 ⟨19, by decide⟩ (some 0)

private def cache934 : Cache :=
  step cache932 ⟨19, by decide⟩ 1
private def partial934 : Partial (Fin 20) (Fin 4) :=
  Function.update partial932 ⟨19, by decide⟩ (some 1)

private def cache935 : Cache :=
  step cache932 ⟨19, by decide⟩ 2
private def partial935 : Partial (Fin 20) (Fin 4) :=
  Function.update partial932 ⟨19, by decide⟩ (some 2)

private def cache936 : Cache :=
  step cache932 ⟨19, by decide⟩ 3
private def partial936 : Partial (Fin 20) (Fin 4) :=
  Function.update partial932 ⟨19, by decide⟩ (some 3)

private def cache937 : Cache :=
  step cache921 ⟨18, by decide⟩ 3
private def partial937 : Partial (Fin 20) (Fin 4) :=
  Function.update partial921 ⟨18, by decide⟩ (some 3)

private def cache938 : Cache :=
  step cache937 ⟨19, by decide⟩ 0
private def partial938 : Partial (Fin 20) (Fin 4) :=
  Function.update partial937 ⟨19, by decide⟩ (some 0)

private def cache939 : Cache :=
  step cache937 ⟨19, by decide⟩ 1
private def partial939 : Partial (Fin 20) (Fin 4) :=
  Function.update partial937 ⟨19, by decide⟩ (some 1)

private def cache940 : Cache :=
  step cache937 ⟨19, by decide⟩ 2
private def partial940 : Partial (Fin 20) (Fin 4) :=
  Function.update partial937 ⟨19, by decide⟩ (some 2)

private def cache941 : Cache :=
  step cache937 ⟨19, by decide⟩ 3
private def partial941 : Partial (Fin 20) (Fin 4) :=
  Function.update partial937 ⟨19, by decide⟩ (some 3)

private def cache942 : Cache :=
  step cache906 ⟨17, by decide⟩ 3
private def partial942 : Partial (Fin 20) (Fin 4) :=
  Function.update partial906 ⟨17, by decide⟩ (some 3)

private def cache943 : Cache :=
  step cache942 ⟨18, by decide⟩ 0
private def partial943 : Partial (Fin 20) (Fin 4) :=
  Function.update partial942 ⟨18, by decide⟩ (some 0)

private def cache944 : Cache :=
  step cache943 ⟨19, by decide⟩ 0
private def partial944 : Partial (Fin 20) (Fin 4) :=
  Function.update partial943 ⟨19, by decide⟩ (some 0)

private def cache945 : Cache :=
  step cache943 ⟨19, by decide⟩ 1
private def partial945 : Partial (Fin 20) (Fin 4) :=
  Function.update partial943 ⟨19, by decide⟩ (some 1)

private def cache946 : Cache :=
  step cache943 ⟨19, by decide⟩ 2
private def partial946 : Partial (Fin 20) (Fin 4) :=
  Function.update partial943 ⟨19, by decide⟩ (some 2)

private def cache947 : Cache :=
  step cache943 ⟨19, by decide⟩ 3
private def partial947 : Partial (Fin 20) (Fin 4) :=
  Function.update partial943 ⟨19, by decide⟩ (some 3)

private def cache948 : Cache :=
  step cache942 ⟨18, by decide⟩ 1
private def partial948 : Partial (Fin 20) (Fin 4) :=
  Function.update partial942 ⟨18, by decide⟩ (some 1)

private def cache949 : Cache :=
  step cache948 ⟨19, by decide⟩ 0
private def partial949 : Partial (Fin 20) (Fin 4) :=
  Function.update partial948 ⟨19, by decide⟩ (some 0)

private def cache950 : Cache :=
  step cache948 ⟨19, by decide⟩ 1
private def partial950 : Partial (Fin 20) (Fin 4) :=
  Function.update partial948 ⟨19, by decide⟩ (some 1)

private def cache951 : Cache :=
  step cache948 ⟨19, by decide⟩ 2
private def partial951 : Partial (Fin 20) (Fin 4) :=
  Function.update partial948 ⟨19, by decide⟩ (some 2)

private def cache952 : Cache :=
  step cache948 ⟨19, by decide⟩ 3
private def partial952 : Partial (Fin 20) (Fin 4) :=
  Function.update partial948 ⟨19, by decide⟩ (some 3)

private def cache953 : Cache :=
  step cache942 ⟨18, by decide⟩ 2
private def partial953 : Partial (Fin 20) (Fin 4) :=
  Function.update partial942 ⟨18, by decide⟩ (some 2)

private def cache954 : Cache :=
  step cache942 ⟨18, by decide⟩ 3
private def partial954 : Partial (Fin 20) (Fin 4) :=
  Function.update partial942 ⟨18, by decide⟩ (some 3)

private theorem receipt954 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨954, by decide⟩ cache954 partial954 = true := by
  decide +kernel

private theorem receipt953 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨953, by decide⟩ cache953 partial953 = true := by
  decide +kernel

private theorem receipt952 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨952, by decide⟩ cache952 partial952 = true := by
  decide +kernel

private theorem receipt951 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨951, by decide⟩ cache951 partial951 = true := by
  decide +kernel

private theorem receipt950 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨950, by decide⟩ cache950 partial950 = true := by
  decide +kernel

private theorem receipt949 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨949, by decide⟩ cache949 partial949 = true := by
  decide +kernel

private theorem receipt948 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨948, by decide⟩ cache948 partial948 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![949,950,951,952])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2093980828071603 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt949
  · exact receipt950
  · exact receipt951
  · exact receipt952

private theorem receipt947 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨947, by decide⟩ cache947 partial947 = true := by
  decide +kernel

private theorem receipt946 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨946, by decide⟩ cache946 partial946 = true := by
  decide +kernel

private theorem receipt945 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨945, by decide⟩ cache945 partial945 = true := by
  decide +kernel

private theorem receipt944 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨944, by decide⟩ cache944 partial944 = true := by
  decide +kernel

private theorem receipt943 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨943, by decide⟩ cache943 partial943 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![944,945,946,947])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2082983026783763 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt944
  · exact receipt945
  · exact receipt946
  · exact receipt947

private theorem receipt942 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨942, by decide⟩ cache942 partial942 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![943,948,953,954])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2098379948062194 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt943
  · exact receipt948
  · exact receipt953
  · exact receipt954

private theorem receipt941 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨941, by decide⟩ cache941 partial941 = true := by
  decide +kernel

private theorem receipt940 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨940, by decide⟩ cache940 partial940 = true := by
  decide +kernel

private theorem receipt939 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨939, by decide⟩ cache939 partial939 = true := by
  decide +kernel

private theorem receipt938 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨938, by decide⟩ cache938 partial938 = true := by
  decide +kernel

private theorem receipt937 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨937, by decide⟩ cache937 partial937 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![938,939,940,941])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2069785665238355 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt938
  · exact receipt939
  · exact receipt940
  · exact receipt941

private theorem receipt936 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨936, by decide⟩ cache936 partial936 = true := by
  decide +kernel

private theorem receipt935 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨935, by decide⟩ cache935 partial935 = true := by
  decide +kernel

private theorem receipt934 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨934, by decide⟩ cache934 partial934 = true := by
  decide +kernel

private theorem receipt933 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨933, by decide⟩ cache933 partial933 = true := by
  decide +kernel

private theorem receipt932 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨932, by decide⟩ cache932 partial932 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![933,934,935,936])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2058787863950515 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt933
  · exact receipt934
  · exact receipt935
  · exact receipt936

private theorem receipt931 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨931, by decide⟩ cache931 partial931 = true := by
  decide +kernel

private theorem receipt930 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨930, by decide⟩ cache930 partial930 = true := by
  decide +kernel

private theorem receipt929 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨929, by decide⟩ cache929 partial929 = true := by
  decide +kernel

private theorem receipt928 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨928, by decide⟩ cache928 partial928 = true := by
  decide +kernel

private theorem receipt927 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨927, by decide⟩ cache927 partial927 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![928,929,930,931])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2047790062662675 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt928
  · exact receipt929
  · exact receipt930
  · exact receipt931

private theorem receipt926 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨926, by decide⟩ cache926 partial926 = true := by
  decide +kernel

private theorem receipt925 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨925, by decide⟩ cache925 partial925 = true := by
  decide +kernel

private theorem receipt924 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨924, by decide⟩ cache924 partial924 = true := by
  decide +kernel

private theorem receipt923 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨923, by decide⟩ cache923 partial923 = true := by
  decide +kernel

private theorem receipt922 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨922, by decide⟩ cache922 partial922 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![923,924,925,926])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2036792261374835 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt923
  · exact receipt924
  · exact receipt925
  · exact receipt926

private theorem receipt921 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨921, by decide⟩ cache921 partial921 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![922,927,932,937])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2060985275675474 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt922
  · exact receipt927
  · exact receipt932
  · exact receipt937

private theorem receipt920 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨920, by decide⟩ cache920 partial920 = true := by
  decide +kernel

private theorem receipt919 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨919, by decide⟩ cache919 partial919 = true := by
  decide +kernel

private theorem receipt918 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨918, by decide⟩ cache918 partial918 = true := by
  decide +kernel

private theorem receipt917 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨917, by decide⟩ cache917 partial917 = true := by
  decide +kernel

private theorem receipt916 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨916, by decide⟩ cache916 partial916 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![917,918,919,920])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2023594899829427 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt917
  · exact receipt918
  · exact receipt919
  · exact receipt920

private theorem receipt915 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨915, by decide⟩ cache915 partial915 = true := by
  decide +kernel

private theorem receipt914 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨914, by decide⟩ cache914 partial914 = true := by
  decide +kernel

private theorem receipt913 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨913, by decide⟩ cache913 partial913 = true := by
  decide +kernel

private theorem receipt912 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨912, by decide⟩ cache912 partial912 = true := by
  decide +kernel

private theorem receipt911 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨911, by decide⟩ cache911 partial911 = true := by
  decide +kernel

private theorem receipt910 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨910, by decide⟩ cache910 partial910 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![911,912,913,914])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2010397538284019 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt911
  · exact receipt912
  · exact receipt913
  · exact receipt914

private theorem receipt909 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨909, by decide⟩ cache909 partial909 = true := by
  decide +kernel

private theorem receipt908 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨908, by decide⟩ cache908 partial908 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![909,910,915,916])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2014796658274738 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt909
  · exact receipt910
  · exact receipt915
  · exact receipt916

private theorem receipt907 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨907, by decide⟩ cache907 partial907 = true := by
  decide +kernel

theorem receipt906 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨906, by decide⟩ cache906 partial906 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![907,908,921,942])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2071974483882353 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt907
  · exact receipt908
  · exact receipt921
  · exact receipt942


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock25
