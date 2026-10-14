/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock3
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock3
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock3
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1912 : Cache :=
  step cache1911 ⟨16, by decide⟩ 0
private def partial1912 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1911 ⟨16, by decide⟩ (some 0)

private def cache1913 : Cache :=
  step cache1911 ⟨16, by decide⟩ 1
private def partial1913 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1911 ⟨16, by decide⟩ (some 1)

private def cache1914 : Cache :=
  step cache1911 ⟨16, by decide⟩ 2
private def partial1914 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1911 ⟨16, by decide⟩ (some 2)

private def cache1915 : Cache :=
  step cache1911 ⟨16, by decide⟩ 3
private def partial1915 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1911 ⟨16, by decide⟩ (some 3)

private def cache1916 : Cache :=
  step cache1915 ⟨17, by decide⟩ 0
private def partial1916 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1915 ⟨17, by decide⟩ (some 0)

private def cache1917 : Cache :=
  step cache1915 ⟨17, by decide⟩ 1
private def partial1917 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1915 ⟨17, by decide⟩ (some 1)

private def cache1918 : Cache :=
  step cache1917 ⟨18, by decide⟩ 0
private def partial1918 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1917 ⟨18, by decide⟩ (some 0)

private def cache1919 : Cache :=
  step cache1917 ⟨18, by decide⟩ 1
private def partial1919 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1917 ⟨18, by decide⟩ (some 1)

private def cache1920 : Cache :=
  step cache1917 ⟨18, by decide⟩ 2
private def partial1920 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1917 ⟨18, by decide⟩ (some 2)

private def cache1921 : Cache :=
  step cache1920 ⟨19, by decide⟩ 0
private def partial1921 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1920 ⟨19, by decide⟩ (some 0)

private def cache1922 : Cache :=
  step cache1920 ⟨19, by decide⟩ 1
private def partial1922 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1920 ⟨19, by decide⟩ (some 1)

private def cache1923 : Cache :=
  step cache1920 ⟨19, by decide⟩ 2
private def partial1923 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1920 ⟨19, by decide⟩ (some 2)

private def cache1924 : Cache :=
  step cache1920 ⟨19, by decide⟩ 3
private def partial1924 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1920 ⟨19, by decide⟩ (some 3)

private def cache1925 : Cache :=
  step cache1917 ⟨18, by decide⟩ 3
private def partial1925 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1917 ⟨18, by decide⟩ (some 3)

private def cache1926 : Cache :=
  step cache1925 ⟨19, by decide⟩ 0
private def partial1926 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1925 ⟨19, by decide⟩ (some 0)

private def cache1927 : Cache :=
  step cache1925 ⟨19, by decide⟩ 1
private def partial1927 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1925 ⟨19, by decide⟩ (some 1)

private def cache1928 : Cache :=
  step cache1925 ⟨19, by decide⟩ 2
private def partial1928 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1925 ⟨19, by decide⟩ (some 2)

private def cache1929 : Cache :=
  step cache1925 ⟨19, by decide⟩ 3
private def partial1929 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1925 ⟨19, by decide⟩ (some 3)

private def cache1930 : Cache :=
  step cache1915 ⟨17, by decide⟩ 2
private def partial1930 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1915 ⟨17, by decide⟩ (some 2)

private def cache1931 : Cache :=
  step cache1930 ⟨18, by decide⟩ 0
private def partial1931 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1930 ⟨18, by decide⟩ (some 0)

private def cache1932 : Cache :=
  step cache1930 ⟨18, by decide⟩ 1
private def partial1932 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1930 ⟨18, by decide⟩ (some 1)

private def cache1933 : Cache :=
  step cache1930 ⟨18, by decide⟩ 2
private def partial1933 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1930 ⟨18, by decide⟩ (some 2)

private def cache1934 : Cache :=
  step cache1930 ⟨18, by decide⟩ 3
private def partial1934 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1930 ⟨18, by decide⟩ (some 3)

private def cache1935 : Cache :=
  step cache1934 ⟨19, by decide⟩ 0
private def partial1935 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1934 ⟨19, by decide⟩ (some 0)

private def cache1936 : Cache :=
  step cache1934 ⟨19, by decide⟩ 1
private def partial1936 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1934 ⟨19, by decide⟩ (some 1)

private def cache1937 : Cache :=
  step cache1934 ⟨19, by decide⟩ 2
private def partial1937 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1934 ⟨19, by decide⟩ (some 2)

private def cache1938 : Cache :=
  step cache1934 ⟨19, by decide⟩ 3
private def partial1938 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1934 ⟨19, by decide⟩ (some 3)

private def cache1939 : Cache :=
  step cache1915 ⟨17, by decide⟩ 3
private def partial1939 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1915 ⟨17, by decide⟩ (some 3)

private def cache1940 : Cache :=
  step cache1939 ⟨18, by decide⟩ 0
private def partial1940 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1939 ⟨18, by decide⟩ (some 0)

private def cache1941 : Cache :=
  step cache1939 ⟨18, by decide⟩ 1
private def partial1941 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1939 ⟨18, by decide⟩ (some 1)

private def cache1942 : Cache :=
  step cache1939 ⟨18, by decide⟩ 2
private def partial1942 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1939 ⟨18, by decide⟩ (some 2)

private def cache1943 : Cache :=
  step cache1942 ⟨19, by decide⟩ 0
private def partial1943 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1942 ⟨19, by decide⟩ (some 0)

private def cache1944 : Cache :=
  step cache1942 ⟨19, by decide⟩ 1
private def partial1944 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1942 ⟨19, by decide⟩ (some 1)

private def cache1945 : Cache :=
  step cache1942 ⟨19, by decide⟩ 2
private def partial1945 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1942 ⟨19, by decide⟩ (some 2)

private def cache1946 : Cache :=
  step cache1942 ⟨19, by decide⟩ 3
private def partial1946 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1942 ⟨19, by decide⟩ (some 3)

private def cache1947 : Cache :=
  step cache1939 ⟨18, by decide⟩ 3
private def partial1947 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1939 ⟨18, by decide⟩ (some 3)

private def cache1948 : Cache :=
  step cache1947 ⟨19, by decide⟩ 0
private def partial1948 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1947 ⟨19, by decide⟩ (some 0)

private def cache1949 : Cache :=
  step cache1947 ⟨19, by decide⟩ 1
private def partial1949 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1947 ⟨19, by decide⟩ (some 1)

private def cache1950 : Cache :=
  step cache1947 ⟨19, by decide⟩ 2
private def partial1950 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1947 ⟨19, by decide⟩ (some 2)

private def cache1951 : Cache :=
  step cache1947 ⟨19, by decide⟩ 3
private def partial1951 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1947 ⟨19, by decide⟩ (some 3)

private theorem receipt1951 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1951, by decide⟩ cache1951 partial1951 = true := by
  decide +kernel

private theorem receipt1950 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1950, by decide⟩ cache1950 partial1950 = true := by
  decide +kernel

private theorem receipt1949 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1949, by decide⟩ cache1949 partial1949 = true := by
  decide +kernel

private theorem receipt1948 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1948, by decide⟩ cache1948 partial1948 = true := by
  decide +kernel

private theorem receipt1947 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1947, by decide⟩ cache1947 partial1947 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1948,1949,1950,1951])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4291341525382035 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1948
  · exact receipt1949
  · exact receipt1950
  · exact receipt1951

private theorem receipt1946 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1946, by decide⟩ cache1946 partial1946 = true := by
  decide +kernel

private theorem receipt1945 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1945, by decide⟩ cache1945 partial1945 = true := by
  decide +kernel

private theorem receipt1944 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1944, by decide⟩ cache1944 partial1944 = true := by
  decide +kernel

private theorem receipt1943 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1943, by decide⟩ cache1943 partial1943 = true := by
  decide +kernel

private theorem receipt1942 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1942, by decide⟩ cache1942 partial1942 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1943,1944,1945,1946])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4280343724094195 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1943
  · exact receipt1944
  · exact receipt1945
  · exact receipt1946

private theorem receipt1941 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1941, by decide⟩ cache1941 partial1941 = true := by
  decide +kernel

private theorem receipt1940 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1940, by decide⟩ cache1940 partial1940 = true := by
  decide +kernel

private theorem receipt1939 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1939, by decide⟩ cache1939 partial1939 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1940,1941,1942,1947])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4282541136343698 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1940
  · exact receipt1941
  · exact receipt1942
  · exact receipt1947

private theorem receipt1938 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1938, by decide⟩ cache1938 partial1938 = true := by
  decide +kernel

private theorem receipt1937 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1937, by decide⟩ cache1937 partial1937 = true := by
  decide +kernel

private theorem receipt1936 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1936, by decide⟩ cache1936 partial1936 = true := by
  decide +kernel

private theorem receipt1935 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1935, by decide⟩ cache1935 partial1935 = true := by
  decide +kernel

private theorem receipt1934 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1934, by decide⟩ cache1934 partial1934 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1935,1936,1937,1938])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4262747242033651 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1935
  · exact receipt1936
  · exact receipt1937
  · exact receipt1938

private theorem receipt1933 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1933, by decide⟩ cache1933 partial1933 = true := by
  decide +kernel

private theorem receipt1932 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1932, by decide⟩ cache1932 partial1932 = true := by
  decide +kernel

private theorem receipt1931 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1931, by decide⟩ cache1931 partial1931 = true := by
  decide +kernel

private theorem receipt1930 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1930, by decide⟩ cache1930 partial1930 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1931,1932,1933,1934])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4253949001003378 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1931
  · exact receipt1932
  · exact receipt1933
  · exact receipt1934

private theorem receipt1929 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1929, by decide⟩ cache1929 partial1929 = true := by
  decide +kernel

private theorem receipt1928 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1928, by decide⟩ cache1928 partial1928 = true := by
  decide +kernel

private theorem receipt1927 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1927, by decide⟩ cache1927 partial1927 = true := by
  decide +kernel

private theorem receipt1926 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1926, by decide⟩ cache1926 partial1926 = true := by
  decide +kernel

private theorem receipt1925 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1925, by decide⟩ cache1925 partial1925 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1926,1927,1928,1929])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4242951199715539 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1926
  · exact receipt1927
  · exact receipt1928
  · exact receipt1929

private theorem receipt1924 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1924, by decide⟩ cache1924 partial1924 = true := by
  decide +kernel

private theorem receipt1923 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1923, by decide⟩ cache1923 partial1923 = true := by
  decide +kernel

private theorem receipt1922 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1922, by decide⟩ cache1922 partial1922 = true := by
  decide +kernel

private theorem receipt1921 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1921, by decide⟩ cache1921 partial1921 = true := by
  decide +kernel

private theorem receipt1920 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1920, by decide⟩ cache1920 partial1920 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1921,1922,1923,1924])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4231953398427699 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1921
  · exact receipt1922
  · exact receipt1923
  · exact receipt1924

private theorem receipt1919 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1919, by decide⟩ cache1919 partial1919 = true := by
  decide +kernel

private theorem receipt1918 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1918, by decide⟩ cache1918 partial1918 = true := by
  decide +kernel

private theorem receipt1917 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1917, by decide⟩ cache1917 partial1917 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1918,1919,1920,1925])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4234150810677202 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1918
  · exact receipt1919
  · exact receipt1920
  · exact receipt1925

private theorem receipt1916 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1916, by decide⟩ cache1916 partial1916 = true := by
  decide +kernel

private theorem receipt1915 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1915, by decide⟩ cache1915 partial1915 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1916,1917,1930,1939])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4264942504701841 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1916
  · exact receipt1917
  · exact receipt1930
  · exact receipt1939

private theorem receipt1914 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1914, by decide⟩ cache1914 partial1914 = true := by
  decide +kernel

private theorem receipt1913 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1913, by decide⟩ cache1913 partial1913 = true := by
  decide +kernel

private theorem receipt1912 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1912, by decide⟩ cache1912 partial1912 = true := by
  decide +kernel

theorem receipt1911 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1911, by decide⟩ cache1911 partial1911 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1912,1913,1914,1915])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4212157356109584 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1912
  · exact receipt1913
  · exact receipt1914
  · exact receipt1915

theorem receipt1910 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1910, by decide⟩ cache1910 partial1910 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock3
