/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock2
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock2
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock2
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1953 : Cache :=
  step cache1952 ⟨16, by decide⟩ 0
private def partial1953 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1952 ⟨16, by decide⟩ (some 0)

private def cache1954 : Cache :=
  step cache1952 ⟨16, by decide⟩ 1
private def partial1954 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1952 ⟨16, by decide⟩ (some 1)

private def cache1955 : Cache :=
  step cache1952 ⟨16, by decide⟩ 2
private def partial1955 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1952 ⟨16, by decide⟩ (some 2)

private def cache1956 : Cache :=
  step cache1952 ⟨16, by decide⟩ 3
private def partial1956 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1952 ⟨16, by decide⟩ (some 3)

private def cache1957 : Cache :=
  step cache1956 ⟨17, by decide⟩ 0
private def partial1957 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1956 ⟨17, by decide⟩ (some 0)

private def cache1958 : Cache :=
  step cache1956 ⟨17, by decide⟩ 1
private def partial1958 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1956 ⟨17, by decide⟩ (some 1)

private def cache1959 : Cache :=
  step cache1958 ⟨18, by decide⟩ 0
private def partial1959 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1958 ⟨18, by decide⟩ (some 0)

private def cache1960 : Cache :=
  step cache1958 ⟨18, by decide⟩ 1
private def partial1960 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1958 ⟨18, by decide⟩ (some 1)

private def cache1961 : Cache :=
  step cache1958 ⟨18, by decide⟩ 2
private def partial1961 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1958 ⟨18, by decide⟩ (some 2)

private def cache1962 : Cache :=
  step cache1961 ⟨19, by decide⟩ 0
private def partial1962 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1961 ⟨19, by decide⟩ (some 0)

private def cache1963 : Cache :=
  step cache1961 ⟨19, by decide⟩ 1
private def partial1963 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1961 ⟨19, by decide⟩ (some 1)

private def cache1964 : Cache :=
  step cache1961 ⟨19, by decide⟩ 2
private def partial1964 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1961 ⟨19, by decide⟩ (some 2)

private def cache1965 : Cache :=
  step cache1961 ⟨19, by decide⟩ 3
private def partial1965 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1961 ⟨19, by decide⟩ (some 3)

private def cache1966 : Cache :=
  step cache1958 ⟨18, by decide⟩ 3
private def partial1966 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1958 ⟨18, by decide⟩ (some 3)

private def cache1967 : Cache :=
  step cache1966 ⟨19, by decide⟩ 0
private def partial1967 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1966 ⟨19, by decide⟩ (some 0)

private def cache1968 : Cache :=
  step cache1966 ⟨19, by decide⟩ 1
private def partial1968 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1966 ⟨19, by decide⟩ (some 1)

private def cache1969 : Cache :=
  step cache1966 ⟨19, by decide⟩ 2
private def partial1969 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1966 ⟨19, by decide⟩ (some 2)

private def cache1970 : Cache :=
  step cache1966 ⟨19, by decide⟩ 3
private def partial1970 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1966 ⟨19, by decide⟩ (some 3)

private def cache1971 : Cache :=
  step cache1956 ⟨17, by decide⟩ 2
private def partial1971 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1956 ⟨17, by decide⟩ (some 2)

private def cache1972 : Cache :=
  step cache1971 ⟨18, by decide⟩ 0
private def partial1972 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1971 ⟨18, by decide⟩ (some 0)

private def cache1973 : Cache :=
  step cache1971 ⟨18, by decide⟩ 1
private def partial1973 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1971 ⟨18, by decide⟩ (some 1)

private def cache1974 : Cache :=
  step cache1973 ⟨19, by decide⟩ 0
private def partial1974 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1973 ⟨19, by decide⟩ (some 0)

private def cache1975 : Cache :=
  step cache1973 ⟨19, by decide⟩ 1
private def partial1975 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1973 ⟨19, by decide⟩ (some 1)

private def cache1976 : Cache :=
  step cache1973 ⟨19, by decide⟩ 2
private def partial1976 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1973 ⟨19, by decide⟩ (some 2)

private def cache1977 : Cache :=
  step cache1973 ⟨19, by decide⟩ 3
private def partial1977 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1973 ⟨19, by decide⟩ (some 3)

private def cache1978 : Cache :=
  step cache1971 ⟨18, by decide⟩ 2
private def partial1978 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1971 ⟨18, by decide⟩ (some 2)

private def cache1979 : Cache :=
  step cache1971 ⟨18, by decide⟩ 3
private def partial1979 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1971 ⟨18, by decide⟩ (some 3)

private def cache1980 : Cache :=
  step cache1979 ⟨19, by decide⟩ 0
private def partial1980 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1979 ⟨19, by decide⟩ (some 0)

private def cache1981 : Cache :=
  step cache1979 ⟨19, by decide⟩ 1
private def partial1981 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1979 ⟨19, by decide⟩ (some 1)

private def cache1982 : Cache :=
  step cache1979 ⟨19, by decide⟩ 2
private def partial1982 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1979 ⟨19, by decide⟩ (some 2)

private def cache1983 : Cache :=
  step cache1979 ⟨19, by decide⟩ 3
private def partial1983 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1979 ⟨19, by decide⟩ (some 3)

private def cache1984 : Cache :=
  step cache1956 ⟨17, by decide⟩ 3
private def partial1984 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1956 ⟨17, by decide⟩ (some 3)

private def cache1985 : Cache :=
  step cache1984 ⟨18, by decide⟩ 0
private def partial1985 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1984 ⟨18, by decide⟩ (some 0)

private def cache1986 : Cache :=
  step cache1985 ⟨19, by decide⟩ 0
private def partial1986 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1985 ⟨19, by decide⟩ (some 0)

private def cache1987 : Cache :=
  step cache1985 ⟨19, by decide⟩ 1
private def partial1987 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1985 ⟨19, by decide⟩ (some 1)

private def cache1988 : Cache :=
  step cache1985 ⟨19, by decide⟩ 2
private def partial1988 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1985 ⟨19, by decide⟩ (some 2)

private def cache1989 : Cache :=
  step cache1985 ⟨19, by decide⟩ 3
private def partial1989 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1985 ⟨19, by decide⟩ (some 3)

private def cache1990 : Cache :=
  step cache1984 ⟨18, by decide⟩ 1
private def partial1990 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1984 ⟨18, by decide⟩ (some 1)

private def cache1991 : Cache :=
  step cache1984 ⟨18, by decide⟩ 2
private def partial1991 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1984 ⟨18, by decide⟩ (some 2)

private def cache1992 : Cache :=
  step cache1991 ⟨19, by decide⟩ 0
private def partial1992 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1991 ⟨19, by decide⟩ (some 0)

private def cache1993 : Cache :=
  step cache1991 ⟨19, by decide⟩ 1
private def partial1993 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1991 ⟨19, by decide⟩ (some 1)

private def cache1994 : Cache :=
  step cache1991 ⟨19, by decide⟩ 2
private def partial1994 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1991 ⟨19, by decide⟩ (some 2)

private def cache1995 : Cache :=
  step cache1991 ⟨19, by decide⟩ 3
private def partial1995 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1991 ⟨19, by decide⟩ (some 3)

private def cache1996 : Cache :=
  step cache1984 ⟨18, by decide⟩ 3
private def partial1996 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1984 ⟨18, by decide⟩ (some 3)

private def cache1998 : Cache :=
  step cache1997 ⟨16, by decide⟩ 0
private def partial1998 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1997 ⟨16, by decide⟩ (some 0)

private def cache1999 : Cache :=
  step cache1997 ⟨16, by decide⟩ 1
private def partial1999 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1997 ⟨16, by decide⟩ (some 1)

private def cache2000 : Cache :=
  step cache1997 ⟨16, by decide⟩ 2
private def partial2000 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1997 ⟨16, by decide⟩ (some 2)

private def cache2001 : Cache :=
  step cache1997 ⟨16, by decide⟩ 3
private def partial2001 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1997 ⟨16, by decide⟩ (some 3)

private def cache2002 : Cache :=
  step cache2001 ⟨17, by decide⟩ 0
private def partial2002 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2001 ⟨17, by decide⟩ (some 0)

private def cache2003 : Cache :=
  step cache2001 ⟨17, by decide⟩ 1
private def partial2003 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2001 ⟨17, by decide⟩ (some 1)

private def cache2004 : Cache :=
  step cache2003 ⟨18, by decide⟩ 0
private def partial2004 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2003 ⟨18, by decide⟩ (some 0)

private def cache2005 : Cache :=
  step cache2003 ⟨18, by decide⟩ 1
private def partial2005 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2003 ⟨18, by decide⟩ (some 1)

private def cache2006 : Cache :=
  step cache2003 ⟨18, by decide⟩ 2
private def partial2006 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2003 ⟨18, by decide⟩ (some 2)

private def cache2007 : Cache :=
  step cache2006 ⟨19, by decide⟩ 0
private def partial2007 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2006 ⟨19, by decide⟩ (some 0)

private def cache2008 : Cache :=
  step cache2006 ⟨19, by decide⟩ 1
private def partial2008 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2006 ⟨19, by decide⟩ (some 1)

private def cache2009 : Cache :=
  step cache2006 ⟨19, by decide⟩ 2
private def partial2009 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2006 ⟨19, by decide⟩ (some 2)

private def cache2010 : Cache :=
  step cache2006 ⟨19, by decide⟩ 3
private def partial2010 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2006 ⟨19, by decide⟩ (some 3)

private def cache2011 : Cache :=
  step cache2003 ⟨18, by decide⟩ 3
private def partial2011 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2003 ⟨18, by decide⟩ (some 3)

private def cache2012 : Cache :=
  step cache2001 ⟨17, by decide⟩ 2
private def partial2012 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2001 ⟨17, by decide⟩ (some 2)

private def cache2013 : Cache :=
  step cache2012 ⟨18, by decide⟩ 0
private def partial2013 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2012 ⟨18, by decide⟩ (some 0)

private def cache2014 : Cache :=
  step cache2012 ⟨18, by decide⟩ 1
private def partial2014 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2012 ⟨18, by decide⟩ (some 1)

private def cache2015 : Cache :=
  step cache2014 ⟨19, by decide⟩ 0
private def partial2015 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2014 ⟨19, by decide⟩ (some 0)

private def cache2016 : Cache :=
  step cache2014 ⟨19, by decide⟩ 1
private def partial2016 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2014 ⟨19, by decide⟩ (some 1)

private def cache2017 : Cache :=
  step cache2014 ⟨19, by decide⟩ 2
private def partial2017 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2014 ⟨19, by decide⟩ (some 2)

private def cache2018 : Cache :=
  step cache2014 ⟨19, by decide⟩ 3
private def partial2018 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2014 ⟨19, by decide⟩ (some 3)

private def cache2019 : Cache :=
  step cache2012 ⟨18, by decide⟩ 2
private def partial2019 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2012 ⟨18, by decide⟩ (some 2)

private def cache2020 : Cache :=
  step cache2012 ⟨18, by decide⟩ 3
private def partial2020 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2012 ⟨18, by decide⟩ (some 3)

private def cache2021 : Cache :=
  step cache2001 ⟨17, by decide⟩ 3
private def partial2021 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2001 ⟨17, by decide⟩ (some 3)

private def cache2022 : Cache :=
  step cache2021 ⟨18, by decide⟩ 0
private def partial2022 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2021 ⟨18, by decide⟩ (some 0)

private def cache2023 : Cache :=
  step cache2022 ⟨19, by decide⟩ 0
private def partial2023 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2022 ⟨19, by decide⟩ (some 0)

private def cache2024 : Cache :=
  step cache2022 ⟨19, by decide⟩ 1
private def partial2024 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2022 ⟨19, by decide⟩ (some 1)

private def cache2025 : Cache :=
  step cache2022 ⟨19, by decide⟩ 2
private def partial2025 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2022 ⟨19, by decide⟩ (some 2)

private def cache2026 : Cache :=
  step cache2022 ⟨19, by decide⟩ 3
private def partial2026 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2022 ⟨19, by decide⟩ (some 3)

private def cache2027 : Cache :=
  step cache2021 ⟨18, by decide⟩ 1
private def partial2027 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2021 ⟨18, by decide⟩ (some 1)

private def cache2028 : Cache :=
  step cache2027 ⟨19, by decide⟩ 0
private def partial2028 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2027 ⟨19, by decide⟩ (some 0)

private def cache2029 : Cache :=
  step cache2027 ⟨19, by decide⟩ 1
private def partial2029 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2027 ⟨19, by decide⟩ (some 1)

private def cache2030 : Cache :=
  step cache2027 ⟨19, by decide⟩ 2
private def partial2030 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2027 ⟨19, by decide⟩ (some 2)

private def cache2031 : Cache :=
  step cache2027 ⟨19, by decide⟩ 3
private def partial2031 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2027 ⟨19, by decide⟩ (some 3)

private def cache2032 : Cache :=
  step cache2021 ⟨18, by decide⟩ 2
private def partial2032 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2021 ⟨18, by decide⟩ (some 2)

private def cache2033 : Cache :=
  step cache2032 ⟨19, by decide⟩ 0
private def partial2033 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2032 ⟨19, by decide⟩ (some 0)

private def cache2034 : Cache :=
  step cache2032 ⟨19, by decide⟩ 1
private def partial2034 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2032 ⟨19, by decide⟩ (some 1)

private def cache2035 : Cache :=
  step cache2032 ⟨19, by decide⟩ 2
private def partial2035 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2032 ⟨19, by decide⟩ (some 2)

private def cache2036 : Cache :=
  step cache2032 ⟨19, by decide⟩ 3
private def partial2036 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2032 ⟨19, by decide⟩ (some 3)

private def cache2037 : Cache :=
  step cache2021 ⟨18, by decide⟩ 3
private def partial2037 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2021 ⟨18, by decide⟩ (some 3)

private def cache2041 : Cache :=
  step cache2040 ⟨16, by decide⟩ 0
private def partial2041 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2040 ⟨16, by decide⟩ (some 0)

private def cache2042 : Cache :=
  step cache2040 ⟨16, by decide⟩ 1
private def partial2042 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2040 ⟨16, by decide⟩ (some 1)

private def cache2043 : Cache :=
  step cache2040 ⟨16, by decide⟩ 2
private def partial2043 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2040 ⟨16, by decide⟩ (some 2)

private def cache2044 : Cache :=
  step cache2040 ⟨16, by decide⟩ 3
private def partial2044 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2040 ⟨16, by decide⟩ (some 3)

private def cache2045 : Cache :=
  step cache2044 ⟨17, by decide⟩ 0
private def partial2045 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2044 ⟨17, by decide⟩ (some 0)

private def cache2046 : Cache :=
  step cache2044 ⟨17, by decide⟩ 1
private def partial2046 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2044 ⟨17, by decide⟩ (some 1)

private def cache2047 : Cache :=
  step cache2046 ⟨18, by decide⟩ 0
private def partial2047 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2046 ⟨18, by decide⟩ (some 0)

private def cache2048 : Cache :=
  step cache2046 ⟨18, by decide⟩ 1
private def partial2048 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2046 ⟨18, by decide⟩ (some 1)

private def cache2049 : Cache :=
  step cache2046 ⟨18, by decide⟩ 2
private def partial2049 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2046 ⟨18, by decide⟩ (some 2)

private def cache2050 : Cache :=
  step cache2046 ⟨18, by decide⟩ 3
private def partial2050 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2046 ⟨18, by decide⟩ (some 3)

private def cache2051 : Cache :=
  step cache2050 ⟨19, by decide⟩ 0
private def partial2051 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2050 ⟨19, by decide⟩ (some 0)

private def cache2052 : Cache :=
  step cache2050 ⟨19, by decide⟩ 1
private def partial2052 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2050 ⟨19, by decide⟩ (some 1)

private def cache2053 : Cache :=
  step cache2050 ⟨19, by decide⟩ 2
private def partial2053 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2050 ⟨19, by decide⟩ (some 2)

private def cache2054 : Cache :=
  step cache2050 ⟨19, by decide⟩ 3
private def partial2054 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2050 ⟨19, by decide⟩ (some 3)

private def cache2055 : Cache :=
  step cache2044 ⟨17, by decide⟩ 2
private def partial2055 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2044 ⟨17, by decide⟩ (some 2)

private def cache2056 : Cache :=
  step cache2055 ⟨18, by decide⟩ 0
private def partial2056 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2055 ⟨18, by decide⟩ (some 0)

private def cache2057 : Cache :=
  step cache2055 ⟨18, by decide⟩ 1
private def partial2057 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2055 ⟨18, by decide⟩ (some 1)

private def cache2058 : Cache :=
  step cache2055 ⟨18, by decide⟩ 2
private def partial2058 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2055 ⟨18, by decide⟩ (some 2)

private def cache2059 : Cache :=
  step cache2058 ⟨19, by decide⟩ 0
private def partial2059 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2058 ⟨19, by decide⟩ (some 0)

private def cache2060 : Cache :=
  step cache2058 ⟨19, by decide⟩ 1
private def partial2060 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2058 ⟨19, by decide⟩ (some 1)

private def cache2061 : Cache :=
  step cache2058 ⟨19, by decide⟩ 2
private def partial2061 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2058 ⟨19, by decide⟩ (some 2)

private def cache2062 : Cache :=
  step cache2058 ⟨19, by decide⟩ 3
private def partial2062 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2058 ⟨19, by decide⟩ (some 3)

private def cache2063 : Cache :=
  step cache2055 ⟨18, by decide⟩ 3
private def partial2063 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2055 ⟨18, by decide⟩ (some 3)

private def cache2064 : Cache :=
  step cache2063 ⟨19, by decide⟩ 0
private def partial2064 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2063 ⟨19, by decide⟩ (some 0)

private def cache2065 : Cache :=
  step cache2063 ⟨19, by decide⟩ 1
private def partial2065 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2063 ⟨19, by decide⟩ (some 1)

private def cache2066 : Cache :=
  step cache2063 ⟨19, by decide⟩ 2
private def partial2066 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2063 ⟨19, by decide⟩ (some 2)

private def cache2067 : Cache :=
  step cache2063 ⟨19, by decide⟩ 3
private def partial2067 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2063 ⟨19, by decide⟩ (some 3)

private def cache2068 : Cache :=
  step cache2044 ⟨17, by decide⟩ 3
private def partial2068 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2044 ⟨17, by decide⟩ (some 3)

private def cache2069 : Cache :=
  step cache2068 ⟨18, by decide⟩ 0
private def partial2069 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2068 ⟨18, by decide⟩ (some 0)

private def cache2070 : Cache :=
  step cache2068 ⟨18, by decide⟩ 1
private def partial2070 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2068 ⟨18, by decide⟩ (some 1)

private def cache2071 : Cache :=
  step cache2068 ⟨18, by decide⟩ 2
private def partial2071 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2068 ⟨18, by decide⟩ (some 2)

private def cache2072 : Cache :=
  step cache2071 ⟨19, by decide⟩ 0
private def partial2072 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2071 ⟨19, by decide⟩ (some 0)

private def cache2073 : Cache :=
  step cache2071 ⟨19, by decide⟩ 1
private def partial2073 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2071 ⟨19, by decide⟩ (some 1)

private def cache2074 : Cache :=
  step cache2071 ⟨19, by decide⟩ 2
private def partial2074 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2071 ⟨19, by decide⟩ (some 2)

private def cache2075 : Cache :=
  step cache2071 ⟨19, by decide⟩ 3
private def partial2075 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2071 ⟨19, by decide⟩ (some 3)

private def cache2076 : Cache :=
  step cache2068 ⟨18, by decide⟩ 3
private def partial2076 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2068 ⟨18, by decide⟩ (some 3)

private def cache2077 : Cache :=
  step cache2076 ⟨19, by decide⟩ 0
private def partial2077 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2076 ⟨19, by decide⟩ (some 0)

private def cache2078 : Cache :=
  step cache2076 ⟨19, by decide⟩ 1
private def partial2078 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2076 ⟨19, by decide⟩ (some 1)

private def cache2079 : Cache :=
  step cache2076 ⟨19, by decide⟩ 2
private def partial2079 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2076 ⟨19, by decide⟩ (some 2)

private def cache2080 : Cache :=
  step cache2076 ⟨19, by decide⟩ 3
private def partial2080 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2076 ⟨19, by decide⟩ (some 3)

private def cache2082 : Cache :=
  step cache2081 ⟨16, by decide⟩ 0
private def partial2082 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2081 ⟨16, by decide⟩ (some 0)

private def cache2083 : Cache :=
  step cache2081 ⟨16, by decide⟩ 1
private def partial2083 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2081 ⟨16, by decide⟩ (some 1)

private def cache2084 : Cache :=
  step cache2081 ⟨16, by decide⟩ 2
private def partial2084 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2081 ⟨16, by decide⟩ (some 2)

private def cache2085 : Cache :=
  step cache2081 ⟨16, by decide⟩ 3
private def partial2085 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2081 ⟨16, by decide⟩ (some 3)

private def cache2086 : Cache :=
  step cache2085 ⟨17, by decide⟩ 0
private def partial2086 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2085 ⟨17, by decide⟩ (some 0)

private def cache2087 : Cache :=
  step cache2085 ⟨17, by decide⟩ 1
private def partial2087 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2085 ⟨17, by decide⟩ (some 1)

private def cache2088 : Cache :=
  step cache2087 ⟨18, by decide⟩ 0
private def partial2088 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2087 ⟨18, by decide⟩ (some 0)

private def cache2089 : Cache :=
  step cache2087 ⟨18, by decide⟩ 1
private def partial2089 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2087 ⟨18, by decide⟩ (some 1)

private def cache2090 : Cache :=
  step cache2087 ⟨18, by decide⟩ 2
private def partial2090 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2087 ⟨18, by decide⟩ (some 2)

private def cache2091 : Cache :=
  step cache2087 ⟨18, by decide⟩ 3
private def partial2091 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2087 ⟨18, by decide⟩ (some 3)

private def cache2092 : Cache :=
  step cache2091 ⟨19, by decide⟩ 0
private def partial2092 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2091 ⟨19, by decide⟩ (some 0)

private def cache2093 : Cache :=
  step cache2091 ⟨19, by decide⟩ 1
private def partial2093 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2091 ⟨19, by decide⟩ (some 1)

private def cache2094 : Cache :=
  step cache2091 ⟨19, by decide⟩ 2
private def partial2094 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2091 ⟨19, by decide⟩ (some 2)

private def cache2095 : Cache :=
  step cache2091 ⟨19, by decide⟩ 3
private def partial2095 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2091 ⟨19, by decide⟩ (some 3)

private def cache2096 : Cache :=
  step cache2085 ⟨17, by decide⟩ 2
private def partial2096 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2085 ⟨17, by decide⟩ (some 2)

private def cache2097 : Cache :=
  step cache2096 ⟨18, by decide⟩ 0
private def partial2097 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2096 ⟨18, by decide⟩ (some 0)

private def cache2098 : Cache :=
  step cache2097 ⟨19, by decide⟩ 0
private def partial2098 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2097 ⟨19, by decide⟩ (some 0)

private def cache2099 : Cache :=
  step cache2097 ⟨19, by decide⟩ 1
private def partial2099 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2097 ⟨19, by decide⟩ (some 1)

private def cache2100 : Cache :=
  step cache2097 ⟨19, by decide⟩ 2
private def partial2100 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2097 ⟨19, by decide⟩ (some 2)

private def cache2101 : Cache :=
  step cache2097 ⟨19, by decide⟩ 3
private def partial2101 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2097 ⟨19, by decide⟩ (some 3)

private def cache2102 : Cache :=
  step cache2096 ⟨18, by decide⟩ 1
private def partial2102 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2096 ⟨18, by decide⟩ (some 1)

private def cache2103 : Cache :=
  step cache2102 ⟨19, by decide⟩ 0
private def partial2103 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2102 ⟨19, by decide⟩ (some 0)

private def cache2104 : Cache :=
  step cache2102 ⟨19, by decide⟩ 1
private def partial2104 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2102 ⟨19, by decide⟩ (some 1)

private def cache2105 : Cache :=
  step cache2102 ⟨19, by decide⟩ 2
private def partial2105 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2102 ⟨19, by decide⟩ (some 2)

private def cache2106 : Cache :=
  step cache2102 ⟨19, by decide⟩ 3
private def partial2106 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2102 ⟨19, by decide⟩ (some 3)

private def cache2107 : Cache :=
  step cache2096 ⟨18, by decide⟩ 2
private def partial2107 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2096 ⟨18, by decide⟩ (some 2)

private def cache2108 : Cache :=
  step cache2107 ⟨19, by decide⟩ 0
private def partial2108 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2107 ⟨19, by decide⟩ (some 0)

private def cache2109 : Cache :=
  step cache2107 ⟨19, by decide⟩ 1
private def partial2109 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2107 ⟨19, by decide⟩ (some 1)

private def cache2110 : Cache :=
  step cache2107 ⟨19, by decide⟩ 2
private def partial2110 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2107 ⟨19, by decide⟩ (some 2)

private def cache2111 : Cache :=
  step cache2107 ⟨19, by decide⟩ 3
private def partial2111 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2107 ⟨19, by decide⟩ (some 3)

private def cache2112 : Cache :=
  step cache2096 ⟨18, by decide⟩ 3
private def partial2112 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2096 ⟨18, by decide⟩ (some 3)

private def cache2113 : Cache :=
  step cache2112 ⟨19, by decide⟩ 0
private def partial2113 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2112 ⟨19, by decide⟩ (some 0)

private def cache2114 : Cache :=
  step cache2112 ⟨19, by decide⟩ 1
private def partial2114 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2112 ⟨19, by decide⟩ (some 1)

private def cache2115 : Cache :=
  step cache2112 ⟨19, by decide⟩ 2
private def partial2115 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2112 ⟨19, by decide⟩ (some 2)

private def cache2116 : Cache :=
  step cache2112 ⟨19, by decide⟩ 3
private def partial2116 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2112 ⟨19, by decide⟩ (some 3)

private def cache2117 : Cache :=
  step cache2085 ⟨17, by decide⟩ 3
private def partial2117 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2085 ⟨17, by decide⟩ (some 3)

private def cache2118 : Cache :=
  step cache2117 ⟨18, by decide⟩ 0
private def partial2118 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2117 ⟨18, by decide⟩ (some 0)

private def cache2119 : Cache :=
  step cache2117 ⟨18, by decide⟩ 1
private def partial2119 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2117 ⟨18, by decide⟩ (some 1)

private def cache2120 : Cache :=
  step cache2117 ⟨18, by decide⟩ 2
private def partial2120 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2117 ⟨18, by decide⟩ (some 2)

private def cache2121 : Cache :=
  step cache2120 ⟨19, by decide⟩ 0
private def partial2121 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2120 ⟨19, by decide⟩ (some 0)

private def cache2122 : Cache :=
  step cache2120 ⟨19, by decide⟩ 1
private def partial2122 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2120 ⟨19, by decide⟩ (some 1)

private def cache2123 : Cache :=
  step cache2120 ⟨19, by decide⟩ 2
private def partial2123 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2120 ⟨19, by decide⟩ (some 2)

private def cache2124 : Cache :=
  step cache2120 ⟨19, by decide⟩ 3
private def partial2124 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2120 ⟨19, by decide⟩ (some 3)

private def cache2125 : Cache :=
  step cache2117 ⟨18, by decide⟩ 3
private def partial2125 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2117 ⟨18, by decide⟩ (some 3)

private def cache2126 : Cache :=
  step cache2125 ⟨19, by decide⟩ 0
private def partial2126 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2125 ⟨19, by decide⟩ (some 0)

private def cache2127 : Cache :=
  step cache2125 ⟨19, by decide⟩ 1
private def partial2127 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2125 ⟨19, by decide⟩ (some 1)

private def cache2128 : Cache :=
  step cache2125 ⟨19, by decide⟩ 2
private def partial2128 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2125 ⟨19, by decide⟩ (some 2)

private def cache2129 : Cache :=
  step cache2125 ⟨19, by decide⟩ 3
private def partial2129 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2125 ⟨19, by decide⟩ (some 3)

private theorem receipt2129 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2129, by decide⟩ cache2129 partial2129 = true := by
  decide +kernel

private theorem receipt2128 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2128, by decide⟩ cache2128 partial2128 = true := by
  decide +kernel

private theorem receipt2127 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2127, by decide⟩ cache2127 partial2127 = true := by
  decide +kernel

private theorem receipt2126 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2126, by decide⟩ cache2126 partial2126 = true := by
  decide +kernel

private theorem receipt2125 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2125, by decide⟩ cache2125 partial2125 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2126,2127,2128,2129])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4682863251229139 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2126
  · exact receipt2127
  · exact receipt2128
  · exact receipt2129

private theorem receipt2124 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2124, by decide⟩ cache2124 partial2124 = true := by
  decide +kernel

private theorem receipt2123 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2123, by decide⟩ cache2123 partial2123 = true := by
  decide +kernel

private theorem receipt2122 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2122, by decide⟩ cache2122 partial2122 = true := by
  decide +kernel

private theorem receipt2121 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2121, by decide⟩ cache2121 partial2121 = true := by
  decide +kernel

private theorem receipt2120 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2120, by decide⟩ cache2120 partial2120 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2121,2122,2123,2124])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4671865449941299 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2121
  · exact receipt2122
  · exact receipt2123
  · exact receipt2124

private theorem receipt2119 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2119, by decide⟩ cache2119 partial2119 = true := by
  decide +kernel

private theorem receipt2118 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2118, by decide⟩ cache2118 partial2118 = true := by
  decide +kernel

private theorem receipt2117 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2117, by decide⟩ cache2117 partial2117 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2118,2119,2120,2125])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4674062862190802 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2118
  · exact receipt2119
  · exact receipt2120
  · exact receipt2125

private theorem receipt2116 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2116, by decide⟩ cache2116 partial2116 = true := by
  decide +kernel

private theorem receipt2115 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2115, by decide⟩ cache2115 partial2115 = true := by
  decide +kernel

private theorem receipt2114 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2114, by decide⟩ cache2114 partial2114 = true := by
  decide +kernel

private theorem receipt2113 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2113, by decide⟩ cache2113 partial2113 = true := by
  decide +kernel

private theorem receipt2112 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2112, by decide⟩ cache2112 partial2112 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2113,2114,2115,2116])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4654268967880755 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2113
  · exact receipt2114
  · exact receipt2115
  · exact receipt2116

private theorem receipt2111 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2111, by decide⟩ cache2111 partial2111 = true := by
  decide +kernel

private theorem receipt2110 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2110, by decide⟩ cache2110 partial2110 = true := by
  decide +kernel

private theorem receipt2109 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2109, by decide⟩ cache2109 partial2109 = true := by
  decide +kernel

private theorem receipt2108 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2108, by decide⟩ cache2108 partial2108 = true := by
  decide +kernel

private theorem receipt2107 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2107, by decide⟩ cache2107 partial2107 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2108,2109,2110,2111])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4643271166592915 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2108
  · exact receipt2109
  · exact receipt2110
  · exact receipt2111

private theorem receipt2106 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2106, by decide⟩ cache2106 partial2106 = true := by
  decide +kernel

private theorem receipt2105 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2105, by decide⟩ cache2105 partial2105 = true := by
  decide +kernel

private theorem receipt2104 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2104, by decide⟩ cache2104 partial2104 = true := by
  decide +kernel

private theorem receipt2103 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2103, by decide⟩ cache2103 partial2103 = true := by
  decide +kernel

private theorem receipt2102 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2102, by decide⟩ cache2102 partial2102 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2103,2104,2105,2106])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4632273365305075 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2103
  · exact receipt2104
  · exact receipt2105
  · exact receipt2106

private theorem receipt2101 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2101, by decide⟩ cache2101 partial2101 = true := by
  decide +kernel

private theorem receipt2100 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2100, by decide⟩ cache2100 partial2100 = true := by
  decide +kernel

private theorem receipt2099 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2099, by decide⟩ cache2099 partial2099 = true := by
  decide +kernel

private theorem receipt2098 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2098, by decide⟩ cache2098 partial2098 = true := by
  decide +kernel

private theorem receipt2097 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2097, by decide⟩ cache2097 partial2097 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2098,2099,2100,2101])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4621275564017235 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2098
  · exact receipt2099
  · exact receipt2100
  · exact receipt2101

private theorem receipt2096 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2096, by decide⟩ cache2096 partial2096 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2097,2102,2107,2112])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4645468578317874 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2097
  · exact receipt2102
  · exact receipt2107
  · exact receipt2112

private theorem receipt2095 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2095, by decide⟩ cache2095 partial2095 = true := by
  decide +kernel

private theorem receipt2094 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2094, by decide⟩ cache2094 partial2094 = true := by
  decide +kernel

private theorem receipt2093 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2093, by decide⟩ cache2093 partial2093 = true := by
  decide +kernel

private theorem receipt2092 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2092, by decide⟩ cache2092 partial2092 = true := by
  decide +kernel

private theorem receipt2091 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2091, by decide⟩ cache2091 partial2091 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2092,2093,2094,2095])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4608078202471827 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2092
  · exact receipt2093
  · exact receipt2094
  · exact receipt2095

private theorem receipt2090 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2090, by decide⟩ cache2090 partial2090 = true := by
  decide +kernel

private theorem receipt2089 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2089, by decide⟩ cache2089 partial2089 = true := by
  decide +kernel

private theorem receipt2088 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2088, by decide⟩ cache2088 partial2088 = true := by
  decide +kernel

private theorem receipt2087 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2087, by decide⟩ cache2087 partial2087 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2088,2089,2090,2091])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4599279961441554 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2088
  · exact receipt2089
  · exact receipt2090
  · exact receipt2091

private theorem receipt2086 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2086, by decide⟩ cache2086 partial2086 = true := by
  decide +kernel

private theorem receipt2085 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2085, by decide⟩ cache2085 partial2085 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![2086,2087,2096,2117])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4656457787049169 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2086
  · exact receipt2087
  · exact receipt2096
  · exact receipt2117

private theorem receipt2084 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2084, by decide⟩ cache2084 partial2084 = true := by
  decide +kernel

private theorem receipt2083 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2083, by decide⟩ cache2083 partial2083 = true := by
  decide +kernel

private theorem receipt2082 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2082, by decide⟩ cache2082 partial2082 = true := by
  decide +kernel

theorem receipt2081 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2081, by decide⟩ cache2081 partial2081 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![2082,2083,2084,2085])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4586082599896144 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2082
  · exact receipt2083
  · exact receipt2084
  · exact receipt2085

private theorem receipt2080 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2080, by decide⟩ cache2080 partial2080 = true := by
  decide +kernel

private theorem receipt2079 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2079, by decide⟩ cache2079 partial2079 = true := by
  decide +kernel

private theorem receipt2078 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2078, by decide⟩ cache2078 partial2078 = true := by
  decide +kernel

private theorem receipt2077 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2077, by decide⟩ cache2077 partial2077 = true := by
  decide +kernel

private theorem receipt2076 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2076, by decide⟩ cache2076 partial2076 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2077,2078,2079,2080])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4575084798608307 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2077
  · exact receipt2078
  · exact receipt2079
  · exact receipt2080

private theorem receipt2075 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2075, by decide⟩ cache2075 partial2075 = true := by
  decide +kernel

private theorem receipt2074 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2074, by decide⟩ cache2074 partial2074 = true := by
  decide +kernel

private theorem receipt2073 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2073, by decide⟩ cache2073 partial2073 = true := by
  decide +kernel

private theorem receipt2072 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2072, by decide⟩ cache2072 partial2072 = true := by
  decide +kernel

private theorem receipt2071 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2071, by decide⟩ cache2071 partial2071 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2072,2073,2074,2075])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4564086997320467 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2072
  · exact receipt2073
  · exact receipt2074
  · exact receipt2075

private theorem receipt2070 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2070, by decide⟩ cache2070 partial2070 = true := by
  decide +kernel

private theorem receipt2069 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2069, by decide⟩ cache2069 partial2069 = true := by
  decide +kernel

private theorem receipt2068 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2068, by decide⟩ cache2068 partial2068 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2069,2070,2071,2076])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4566284409569970 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2069
  · exact receipt2070
  · exact receipt2071
  · exact receipt2076

private theorem receipt2067 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2067, by decide⟩ cache2067 partial2067 = true := by
  decide +kernel

private theorem receipt2066 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2066, by decide⟩ cache2066 partial2066 = true := by
  decide +kernel

private theorem receipt2065 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2065, by decide⟩ cache2065 partial2065 = true := by
  decide +kernel

private theorem receipt2064 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2064, by decide⟩ cache2064 partial2064 = true := by
  decide +kernel

private theorem receipt2063 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2063, by decide⟩ cache2063 partial2063 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2064,2065,2066,2067])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4546490515259923 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2064
  · exact receipt2065
  · exact receipt2066
  · exact receipt2067

private theorem receipt2062 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2062, by decide⟩ cache2062 partial2062 = true := by
  decide +kernel

private theorem receipt2061 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2061, by decide⟩ cache2061 partial2061 = true := by
  decide +kernel

private theorem receipt2060 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2060, by decide⟩ cache2060 partial2060 = true := by
  decide +kernel

private theorem receipt2059 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2059, by decide⟩ cache2059 partial2059 = true := by
  decide +kernel

private theorem receipt2058 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2058, by decide⟩ cache2058 partial2058 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2059,2060,2061,2062])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4535492713972083 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2059
  · exact receipt2060
  · exact receipt2061
  · exact receipt2062

private theorem receipt2057 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2057, by decide⟩ cache2057 partial2057 = true := by
  decide +kernel

private theorem receipt2056 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2056, by decide⟩ cache2056 partial2056 = true := by
  decide +kernel

private theorem receipt2055 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2055, by decide⟩ cache2055 partial2055 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2056,2057,2058,2063])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4537690126221586 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2056
  · exact receipt2057
  · exact receipt2058
  · exact receipt2063

private theorem receipt2054 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2054, by decide⟩ cache2054 partial2054 = true := by
  decide +kernel

private theorem receipt2053 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2053, by decide⟩ cache2053 partial2053 = true := by
  decide +kernel

private theorem receipt2052 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2052, by decide⟩ cache2052 partial2052 = true := by
  decide +kernel

private theorem receipt2051 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2051, by decide⟩ cache2051 partial2051 = true := by
  decide +kernel

private theorem receipt2050 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2050, by decide⟩ cache2050 partial2050 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2051,2052,2053,2054])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4517896231911539 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2051
  · exact receipt2052
  · exact receipt2053
  · exact receipt2054

private theorem receipt2049 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2049, by decide⟩ cache2049 partial2049 = true := by
  decide +kernel

private theorem receipt2048 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2048, by decide⟩ cache2048 partial2048 = true := by
  decide +kernel

#print axioms receipt2048

private theorem receipt2047 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2047, by decide⟩ cache2047 partial2047 = true := by
  decide +kernel

private theorem receipt2046 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2046, by decide⟩ cache2046 partial2046 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2047,2048,2049,2050])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4509097990881266 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2047
  · exact receipt2048
  · exact receipt2049
  · exact receipt2050

private theorem receipt2045 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2045, by decide⟩ cache2045 partial2045 = true := by
  decide +kernel

private theorem receipt2044 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2044, by decide⟩ cache2044 partial2044 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![2045,2046,2055,2068])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4548683630444465 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2045
  · exact receipt2046
  · exact receipt2055
  · exact receipt2068

private theorem receipt2043 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2043, by decide⟩ cache2043 partial2043 = true := by
  decide +kernel

private theorem receipt2042 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2042, by decide⟩ cache2042 partial2042 = true := by
  decide +kernel

private theorem receipt2041 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2041, by decide⟩ cache2041 partial2041 = true := by
  decide +kernel

theorem receipt2040 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2040, by decide⟩ cache2040 partial2040 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![2041,2042,2043,2044])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4495900629335856 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2041
  · exact receipt2042
  · exact receipt2043
  · exact receipt2044

theorem receipt2039 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2039, by decide⟩ cache2039 partial2039 = true := by
  decide +kernel

private theorem receipt2037 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2037, by decide⟩ cache2037 partial2037 = true := by
  decide +kernel

private theorem receipt2036 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2036, by decide⟩ cache2036 partial2036 = true := by
  decide +kernel

private theorem receipt2035 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2035, by decide⟩ cache2035 partial2035 = true := by
  decide +kernel

private theorem receipt2034 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2034, by decide⟩ cache2034 partial2034 = true := by
  decide +kernel

private theorem receipt2033 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2033, by decide⟩ cache2033 partial2033 = true := by
  decide +kernel

private theorem receipt2032 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2032, by decide⟩ cache2032 partial2032 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2033,2034,2035,2036])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4478304147275315 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2033
  · exact receipt2034
  · exact receipt2035
  · exact receipt2036

private theorem receipt2031 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2031, by decide⟩ cache2031 partial2031 = true := by
  decide +kernel

private theorem receipt2030 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2030, by decide⟩ cache2030 partial2030 = true := by
  decide +kernel

private theorem receipt2029 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2029, by decide⟩ cache2029 partial2029 = true := by
  decide +kernel

private theorem receipt2028 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2028, by decide⟩ cache2028 partial2028 = true := by
  decide +kernel

private theorem receipt2027 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2027, by decide⟩ cache2027 partial2027 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2028,2029,2030,2031])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4467306345987475 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2028
  · exact receipt2029
  · exact receipt2030
  · exact receipt2031

private theorem receipt2026 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2026, by decide⟩ cache2026 partial2026 = true := by
  decide +kernel

private theorem receipt2025 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2025, by decide⟩ cache2025 partial2025 = true := by
  decide +kernel

private theorem receipt2024 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2024, by decide⟩ cache2024 partial2024 = true := by
  decide +kernel

private theorem receipt2023 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2023, by decide⟩ cache2023 partial2023 = true := by
  decide +kernel

private theorem receipt2022 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2022, by decide⟩ cache2022 partial2022 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2023,2024,2025,2026])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4456308544699635 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2023
  · exact receipt2024
  · exact receipt2025
  · exact receipt2026

private theorem receipt2021 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2021, by decide⟩ cache2021 partial2021 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2022,2027,2032,2037])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4480501559000274 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2022
  · exact receipt2027
  · exact receipt2032
  · exact receipt2037

private theorem receipt2020 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2020, by decide⟩ cache2020 partial2020 = true := by
  decide +kernel

private theorem receipt2019 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2019, by decide⟩ cache2019 partial2019 = true := by
  decide +kernel

private theorem receipt2018 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2018, by decide⟩ cache2018 partial2018 = true := by
  decide +kernel

private theorem receipt2017 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2017, by decide⟩ cache2017 partial2017 = true := by
  decide +kernel

private theorem receipt2016 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2016, by decide⟩ cache2016 partial2016 = true := by
  decide +kernel

private theorem receipt2015 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2015, by decide⟩ cache2015 partial2015 = true := by
  decide +kernel

private theorem receipt2014 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2014, by decide⟩ cache2014 partial2014 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2015,2016,2017,2018])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4438712062639091 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2015
  · exact receipt2016
  · exact receipt2017
  · exact receipt2018

private theorem receipt2013 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2013, by decide⟩ cache2013 partial2013 = true := by
  decide +kernel

private theorem receipt2012 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2012, by decide⟩ cache2012 partial2012 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2013,2014,2019,2020])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4443111182629810 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2013
  · exact receipt2014
  · exact receipt2019
  · exact receipt2020

private theorem receipt2011 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2011, by decide⟩ cache2011 partial2011 = true := by
  decide +kernel

private theorem receipt2010 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2010, by decide⟩ cache2010 partial2010 = true := by
  decide +kernel

private theorem receipt2009 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2009, by decide⟩ cache2009 partial2009 = true := by
  decide +kernel

private theorem receipt2008 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2008, by decide⟩ cache2008 partial2008 = true := by
  decide +kernel

private theorem receipt2007 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2007, by decide⟩ cache2007 partial2007 = true := by
  decide +kernel

private theorem receipt2006 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2006, by decide⟩ cache2006 partial2006 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2007,2008,2009,2010])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4421115580578547 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2007
  · exact receipt2008
  · exact receipt2009
  · exact receipt2010

private theorem receipt2005 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2005, by decide⟩ cache2005 partial2005 = true := by
  decide +kernel

private theorem receipt2004 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2004, by decide⟩ cache2004 partial2004 = true := by
  decide +kernel

private theorem receipt2003 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2003, by decide⟩ cache2003 partial2003 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2004,2005,2006,2011])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4423312992828050 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2004
  · exact receipt2005
  · exact receipt2006
  · exact receipt2011

private theorem receipt2002 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2002, by decide⟩ cache2002 partial2002 = true := by
  decide +kernel

private theorem receipt2001 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2001, by decide⟩ cache2001 partial2001 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![2002,2003,2012,2021])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4445306446346833 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2002
  · exact receipt2003
  · exact receipt2012
  · exact receipt2021

private theorem receipt2000 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2000, by decide⟩ cache2000 partial2000 = true := by
  decide +kernel

private theorem receipt1999 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1999, by decide⟩ cache1999 partial1999 = true := by
  decide +kernel

private theorem receipt1998 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1998, by decide⟩ cache1998 partial1998 = true := by
  decide +kernel

theorem receipt1997 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1997, by decide⟩ cache1997 partial1997 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1998,1999,2000,2001])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4401319538260432 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1998
  · exact receipt1999
  · exact receipt2000
  · exact receipt2001

private theorem receipt1996 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1996, by decide⟩ cache1996 partial1996 = true := by
  decide +kernel

private theorem receipt1995 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1995, by decide⟩ cache1995 partial1995 = true := by
  decide +kernel

private theorem receipt1994 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1994, by decide⟩ cache1994 partial1994 = true := by
  decide +kernel

private theorem receipt1993 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1993, by decide⟩ cache1993 partial1993 = true := by
  decide +kernel

private theorem receipt1992 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1992, by decide⟩ cache1992 partial1992 = true := by
  decide +kernel

private theorem receipt1991 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1991, by decide⟩ cache1991 partial1991 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1992,1993,1994,1995])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4388122176715027 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1992
  · exact receipt1993
  · exact receipt1994
  · exact receipt1995

private theorem receipt1990 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1990, by decide⟩ cache1990 partial1990 = true := by
  decide +kernel

private theorem receipt1989 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1989, by decide⟩ cache1989 partial1989 = true := by
  decide +kernel

private theorem receipt1988 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1988, by decide⟩ cache1988 partial1988 = true := by
  decide +kernel

private theorem receipt1987 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1987, by decide⟩ cache1987 partial1987 = true := by
  decide +kernel

private theorem receipt1986 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1986, by decide⟩ cache1986 partial1986 = true := by
  decide +kernel

private theorem receipt1985 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1985, by decide⟩ cache1985 partial1985 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1986,1987,1988,1989])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4374924815169619 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1986
  · exact receipt1987
  · exact receipt1988
  · exact receipt1989

private theorem receipt1984 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1984, by decide⟩ cache1984 partial1984 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1985,1990,1991,1996])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4390319588964402 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1985
  · exact receipt1990
  · exact receipt1991
  · exact receipt1996

private theorem receipt1983 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1983, by decide⟩ cache1983 partial1983 = true := by
  decide +kernel

private theorem receipt1982 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1982, by decide⟩ cache1982 partial1982 = true := by
  decide +kernel

private theorem receipt1981 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1981, by decide⟩ cache1981 partial1981 = true := by
  decide +kernel

private theorem receipt1980 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1980, by decide⟩ cache1980 partial1980 = true := by
  decide +kernel

private theorem receipt1979 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1979, by decide⟩ cache1979 partial1979 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1980,1981,1982,1983])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4361727453624211 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1980
  · exact receipt1981
  · exact receipt1982
  · exact receipt1983

private theorem receipt1978 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1978, by decide⟩ cache1978 partial1978 = true := by
  decide +kernel

private theorem receipt1977 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1977, by decide⟩ cache1977 partial1977 = true := by
  decide +kernel

private theorem receipt1976 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1976, by decide⟩ cache1976 partial1976 = true := by
  decide +kernel

private theorem receipt1975 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1975, by decide⟩ cache1975 partial1975 = true := by
  decide +kernel

private theorem receipt1974 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1974, by decide⟩ cache1974 partial1974 = true := by
  decide +kernel

private theorem receipt1973 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1973, by decide⟩ cache1973 partial1973 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1974,1975,1976,1977])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4348530092078803 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1974
  · exact receipt1975
  · exact receipt1976
  · exact receipt1977

private theorem receipt1972 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1972, by decide⟩ cache1972 partial1972 = true := by
  decide +kernel

private theorem receipt1971 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1971, by decide⟩ cache1971 partial1971 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1972,1973,1978,1979])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4352929212069522 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1972
  · exact receipt1973
  · exact receipt1978
  · exact receipt1979

private theorem receipt1970 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1970, by decide⟩ cache1970 partial1970 = true := by
  decide +kernel

private theorem receipt1969 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1969, by decide⟩ cache1969 partial1969 = true := by
  decide +kernel

private theorem receipt1968 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1968, by decide⟩ cache1968 partial1968 = true := by
  decide +kernel

private theorem receipt1967 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1967, by decide⟩ cache1967 partial1967 = true := by
  decide +kernel

private theorem receipt1966 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1966, by decide⟩ cache1966 partial1966 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1967,1968,1969,1970])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4333133170275827 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1967
  · exact receipt1968
  · exact receipt1969
  · exact receipt1970

private theorem receipt1965 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1965, by decide⟩ cache1965 partial1965 = true := by
  decide +kernel

private theorem receipt1964 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1964, by decide⟩ cache1964 partial1964 = true := by
  decide +kernel

private theorem receipt1963 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1963, by decide⟩ cache1963 partial1963 = true := by
  decide +kernel

private theorem receipt1962 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1962, by decide⟩ cache1962 partial1962 = true := by
  decide +kernel

private theorem receipt1961 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1961, by decide⟩ cache1961 partial1961 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1962,1963,1964,1965])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4322135368987987 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1962
  · exact receipt1963
  · exact receipt1964
  · exact receipt1965

private theorem receipt1960 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1960, by decide⟩ cache1960 partial1960 = true := by
  decide +kernel

private theorem receipt1959 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1959, by decide⟩ cache1959 partial1959 = true := by
  decide +kernel

private theorem receipt1958 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1958, by decide⟩ cache1958 partial1958 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1959,1960,1961,1966])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4324332781237490 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1959
  · exact receipt1960
  · exact receipt1961
  · exact receipt1966

private theorem receipt1957 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1957, by decide⟩ cache1957 partial1957 = true := by
  decide +kernel

private theorem receipt1956 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1956, by decide⟩ cache1956 partial1956 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1957,1958,1971,1984])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4363920568284337 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1957
  · exact receipt1958
  · exact receipt1971
  · exact receipt1984

private theorem receipt1955 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1955, by decide⟩ cache1955 partial1955 = true := by
  decide +kernel

private theorem receipt1954 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1954, by decide⟩ cache1954 partial1954 = true := by
  decide +kernel

private theorem receipt1953 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1953, by decide⟩ cache1953 partial1953 = true := by
  decide +kernel

theorem receipt1952 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1952, by decide⟩ cache1952 partial1952 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![1953,1954,1955,1956])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4302339326669872 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1953
  · exact receipt1954
  · exact receipt1955
  · exact receipt1956


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock2
