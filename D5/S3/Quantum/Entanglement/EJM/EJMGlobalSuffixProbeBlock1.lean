/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock1
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock1
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock1
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache2131 : Cache :=
  step cache2130 ⟨16, by decide⟩ 0
private def partial2131 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2130 ⟨16, by decide⟩ (some 0)

private def cache2132 : Cache :=
  step cache2130 ⟨16, by decide⟩ 1
private def partial2132 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2130 ⟨16, by decide⟩ (some 1)

private def cache2133 : Cache :=
  step cache2130 ⟨16, by decide⟩ 2
private def partial2133 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2130 ⟨16, by decide⟩ (some 2)

private def cache2134 : Cache :=
  step cache2130 ⟨16, by decide⟩ 3
private def partial2134 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2130 ⟨16, by decide⟩ (some 3)

private def cache2135 : Cache :=
  step cache2134 ⟨17, by decide⟩ 0
private def partial2135 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2134 ⟨17, by decide⟩ (some 0)

private def cache2136 : Cache :=
  step cache2134 ⟨17, by decide⟩ 1
private def partial2136 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2134 ⟨17, by decide⟩ (some 1)

private def cache2137 : Cache :=
  step cache2136 ⟨18, by decide⟩ 0
private def partial2137 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2136 ⟨18, by decide⟩ (some 0)

private def cache2138 : Cache :=
  step cache2136 ⟨18, by decide⟩ 1
private def partial2138 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2136 ⟨18, by decide⟩ (some 1)

private def cache2139 : Cache :=
  step cache2136 ⟨18, by decide⟩ 2
private def partial2139 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2136 ⟨18, by decide⟩ (some 2)

private def cache2140 : Cache :=
  step cache2136 ⟨18, by decide⟩ 3
private def partial2140 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2136 ⟨18, by decide⟩ (some 3)

private def cache2141 : Cache :=
  step cache2140 ⟨19, by decide⟩ 0
private def partial2141 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2140 ⟨19, by decide⟩ (some 0)

private def cache2142 : Cache :=
  step cache2140 ⟨19, by decide⟩ 1
private def partial2142 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2140 ⟨19, by decide⟩ (some 1)

private def cache2143 : Cache :=
  step cache2140 ⟨19, by decide⟩ 2
private def partial2143 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2140 ⟨19, by decide⟩ (some 2)

private def cache2144 : Cache :=
  step cache2140 ⟨19, by decide⟩ 3
private def partial2144 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2140 ⟨19, by decide⟩ (some 3)

private def cache2145 : Cache :=
  step cache2134 ⟨17, by decide⟩ 2
private def partial2145 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2134 ⟨17, by decide⟩ (some 2)

private def cache2146 : Cache :=
  step cache2145 ⟨18, by decide⟩ 0
private def partial2146 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2145 ⟨18, by decide⟩ (some 0)

private def cache2147 : Cache :=
  step cache2145 ⟨18, by decide⟩ 1
private def partial2147 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2145 ⟨18, by decide⟩ (some 1)

private def cache2148 : Cache :=
  step cache2147 ⟨19, by decide⟩ 0
private def partial2148 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2147 ⟨19, by decide⟩ (some 0)

private def cache2149 : Cache :=
  step cache2147 ⟨19, by decide⟩ 1
private def partial2149 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2147 ⟨19, by decide⟩ (some 1)

private def cache2150 : Cache :=
  step cache2147 ⟨19, by decide⟩ 2
private def partial2150 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2147 ⟨19, by decide⟩ (some 2)

private def cache2151 : Cache :=
  step cache2147 ⟨19, by decide⟩ 3
private def partial2151 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2147 ⟨19, by decide⟩ (some 3)

private def cache2152 : Cache :=
  step cache2145 ⟨18, by decide⟩ 2
private def partial2152 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2145 ⟨18, by decide⟩ (some 2)

private def cache2153 : Cache :=
  step cache2145 ⟨18, by decide⟩ 3
private def partial2153 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2145 ⟨18, by decide⟩ (some 3)

private def cache2154 : Cache :=
  step cache2134 ⟨17, by decide⟩ 3
private def partial2154 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2134 ⟨17, by decide⟩ (some 3)

private def cache2155 : Cache :=
  step cache2154 ⟨18, by decide⟩ 0
private def partial2155 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2154 ⟨18, by decide⟩ (some 0)

private def cache2156 : Cache :=
  step cache2154 ⟨18, by decide⟩ 1
private def partial2156 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2154 ⟨18, by decide⟩ (some 1)

private def cache2157 : Cache :=
  step cache2154 ⟨18, by decide⟩ 2
private def partial2157 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2154 ⟨18, by decide⟩ (some 2)

private def cache2158 : Cache :=
  step cache2154 ⟨18, by decide⟩ 3
private def partial2158 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2154 ⟨18, by decide⟩ (some 3)

private def cache2164 : Cache :=
  step cache2163 ⟨16, by decide⟩ 0
private def partial2164 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2163 ⟨16, by decide⟩ (some 0)

private def cache2165 : Cache :=
  step cache2163 ⟨16, by decide⟩ 1
private def partial2165 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2163 ⟨16, by decide⟩ (some 1)

private def cache2166 : Cache :=
  step cache2163 ⟨16, by decide⟩ 2
private def partial2166 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2163 ⟨16, by decide⟩ (some 2)

private def cache2167 : Cache :=
  step cache2163 ⟨16, by decide⟩ 3
private def partial2167 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2163 ⟨16, by decide⟩ (some 3)

private def cache2168 : Cache :=
  step cache2167 ⟨17, by decide⟩ 0
private def partial2168 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2167 ⟨17, by decide⟩ (some 0)

private def cache2169 : Cache :=
  step cache2167 ⟨17, by decide⟩ 1
private def partial2169 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2167 ⟨17, by decide⟩ (some 1)

private def cache2170 : Cache :=
  step cache2167 ⟨17, by decide⟩ 2
private def partial2170 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2167 ⟨17, by decide⟩ (some 2)

private def cache2171 : Cache :=
  step cache2170 ⟨18, by decide⟩ 0
private def partial2171 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2170 ⟨18, by decide⟩ (some 0)

private def cache2172 : Cache :=
  step cache2171 ⟨19, by decide⟩ 0
private def partial2172 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2171 ⟨19, by decide⟩ (some 0)

private def cache2173 : Cache :=
  step cache2171 ⟨19, by decide⟩ 1
private def partial2173 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2171 ⟨19, by decide⟩ (some 1)

private def cache2174 : Cache :=
  step cache2171 ⟨19, by decide⟩ 2
private def partial2174 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2171 ⟨19, by decide⟩ (some 2)

private def cache2175 : Cache :=
  step cache2171 ⟨19, by decide⟩ 3
private def partial2175 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2171 ⟨19, by decide⟩ (some 3)

private def cache2176 : Cache :=
  step cache2170 ⟨18, by decide⟩ 1
private def partial2176 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2170 ⟨18, by decide⟩ (some 1)

private def cache2177 : Cache :=
  step cache2176 ⟨19, by decide⟩ 0
private def partial2177 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2176 ⟨19, by decide⟩ (some 0)

private def cache2178 : Cache :=
  step cache2176 ⟨19, by decide⟩ 1
private def partial2178 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2176 ⟨19, by decide⟩ (some 1)

private def cache2179 : Cache :=
  step cache2176 ⟨19, by decide⟩ 2
private def partial2179 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2176 ⟨19, by decide⟩ (some 2)

private def cache2180 : Cache :=
  step cache2176 ⟨19, by decide⟩ 3
private def partial2180 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2176 ⟨19, by decide⟩ (some 3)

private def cache2181 : Cache :=
  step cache2170 ⟨18, by decide⟩ 2
private def partial2181 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2170 ⟨18, by decide⟩ (some 2)

private def cache2182 : Cache :=
  step cache2181 ⟨19, by decide⟩ 0
private def partial2182 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2181 ⟨19, by decide⟩ (some 0)

private def cache2183 : Cache :=
  step cache2181 ⟨19, by decide⟩ 1
private def partial2183 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2181 ⟨19, by decide⟩ (some 1)

private def cache2184 : Cache :=
  step cache2181 ⟨19, by decide⟩ 2
private def partial2184 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2181 ⟨19, by decide⟩ (some 2)

private def cache2185 : Cache :=
  step cache2181 ⟨19, by decide⟩ 3
private def partial2185 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2181 ⟨19, by decide⟩ (some 3)

private def cache2186 : Cache :=
  step cache2170 ⟨18, by decide⟩ 3
private def partial2186 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2170 ⟨18, by decide⟩ (some 3)

private def cache2187 : Cache :=
  step cache2186 ⟨19, by decide⟩ 0
private def partial2187 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2186 ⟨19, by decide⟩ (some 0)

private def cache2188 : Cache :=
  step cache2186 ⟨19, by decide⟩ 1
private def partial2188 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2186 ⟨19, by decide⟩ (some 1)

private def cache2189 : Cache :=
  step cache2186 ⟨19, by decide⟩ 2
private def partial2189 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2186 ⟨19, by decide⟩ (some 2)

private def cache2190 : Cache :=
  step cache2186 ⟨19, by decide⟩ 3
private def partial2190 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2186 ⟨19, by decide⟩ (some 3)

private def cache2191 : Cache :=
  step cache2167 ⟨17, by decide⟩ 3
private def partial2191 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2167 ⟨17, by decide⟩ (some 3)

private def cache2192 : Cache :=
  step cache2191 ⟨18, by decide⟩ 0
private def partial2192 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2191 ⟨18, by decide⟩ (some 0)

private def cache2193 : Cache :=
  step cache2192 ⟨19, by decide⟩ 0
private def partial2193 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2192 ⟨19, by decide⟩ (some 0)

private def cache2194 : Cache :=
  step cache2192 ⟨19, by decide⟩ 1
private def partial2194 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2192 ⟨19, by decide⟩ (some 1)

private def cache2195 : Cache :=
  step cache2192 ⟨19, by decide⟩ 2
private def partial2195 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2192 ⟨19, by decide⟩ (some 2)

private def cache2196 : Cache :=
  step cache2192 ⟨19, by decide⟩ 3
private def partial2196 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2192 ⟨19, by decide⟩ (some 3)

private def cache2197 : Cache :=
  step cache2191 ⟨18, by decide⟩ 1
private def partial2197 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2191 ⟨18, by decide⟩ (some 1)

private def cache2198 : Cache :=
  step cache2197 ⟨19, by decide⟩ 0
private def partial2198 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2197 ⟨19, by decide⟩ (some 0)

private def cache2199 : Cache :=
  step cache2197 ⟨19, by decide⟩ 1
private def partial2199 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2197 ⟨19, by decide⟩ (some 1)

private def cache2200 : Cache :=
  step cache2197 ⟨19, by decide⟩ 2
private def partial2200 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2197 ⟨19, by decide⟩ (some 2)

private def cache2201 : Cache :=
  step cache2197 ⟨19, by decide⟩ 3
private def partial2201 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2197 ⟨19, by decide⟩ (some 3)

private def cache2202 : Cache :=
  step cache2191 ⟨18, by decide⟩ 2
private def partial2202 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2191 ⟨18, by decide⟩ (some 2)

private def cache2203 : Cache :=
  step cache2191 ⟨18, by decide⟩ 3
private def partial2203 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2191 ⟨18, by decide⟩ (some 3)

private def cache2205 : Cache :=
  step cache2204 ⟨16, by decide⟩ 0
private def partial2205 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2204 ⟨16, by decide⟩ (some 0)

private def cache2206 : Cache :=
  step cache2204 ⟨16, by decide⟩ 1
private def partial2206 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2204 ⟨16, by decide⟩ (some 1)

private def cache2207 : Cache :=
  step cache2204 ⟨16, by decide⟩ 2
private def partial2207 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2204 ⟨16, by decide⟩ (some 2)

private def cache2208 : Cache :=
  step cache2204 ⟨16, by decide⟩ 3
private def partial2208 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2204 ⟨16, by decide⟩ (some 3)

private def cache2209 : Cache :=
  step cache2208 ⟨17, by decide⟩ 0
private def partial2209 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2208 ⟨17, by decide⟩ (some 0)

private def cache2210 : Cache :=
  step cache2208 ⟨17, by decide⟩ 1
private def partial2210 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2208 ⟨17, by decide⟩ (some 1)

private def cache2211 : Cache :=
  step cache2208 ⟨17, by decide⟩ 2
private def partial2211 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2208 ⟨17, by decide⟩ (some 2)

private def cache2212 : Cache :=
  step cache2211 ⟨18, by decide⟩ 0
private def partial2212 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2211 ⟨18, by decide⟩ (some 0)

private def cache2213 : Cache :=
  step cache2212 ⟨19, by decide⟩ 0
private def partial2213 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2212 ⟨19, by decide⟩ (some 0)

private def cache2214 : Cache :=
  step cache2212 ⟨19, by decide⟩ 1
private def partial2214 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2212 ⟨19, by decide⟩ (some 1)

private def cache2215 : Cache :=
  step cache2212 ⟨19, by decide⟩ 2
private def partial2215 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2212 ⟨19, by decide⟩ (some 2)

private def cache2216 : Cache :=
  step cache2212 ⟨19, by decide⟩ 3
private def partial2216 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2212 ⟨19, by decide⟩ (some 3)

private def cache2217 : Cache :=
  step cache2211 ⟨18, by decide⟩ 1
private def partial2217 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2211 ⟨18, by decide⟩ (some 1)

private def cache2218 : Cache :=
  step cache2217 ⟨19, by decide⟩ 0
private def partial2218 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2217 ⟨19, by decide⟩ (some 0)

private def cache2219 : Cache :=
  step cache2217 ⟨19, by decide⟩ 1
private def partial2219 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2217 ⟨19, by decide⟩ (some 1)

private def cache2220 : Cache :=
  step cache2217 ⟨19, by decide⟩ 2
private def partial2220 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2217 ⟨19, by decide⟩ (some 2)

private def cache2221 : Cache :=
  step cache2217 ⟨19, by decide⟩ 3
private def partial2221 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2217 ⟨19, by decide⟩ (some 3)

private def cache2222 : Cache :=
  step cache2211 ⟨18, by decide⟩ 2
private def partial2222 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2211 ⟨18, by decide⟩ (some 2)

private def cache2223 : Cache :=
  step cache2222 ⟨19, by decide⟩ 0
private def partial2223 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2222 ⟨19, by decide⟩ (some 0)

private def cache2224 : Cache :=
  step cache2222 ⟨19, by decide⟩ 1
private def partial2224 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2222 ⟨19, by decide⟩ (some 1)

private def cache2225 : Cache :=
  step cache2222 ⟨19, by decide⟩ 2
private def partial2225 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2222 ⟨19, by decide⟩ (some 2)

private def cache2226 : Cache :=
  step cache2222 ⟨19, by decide⟩ 3
private def partial2226 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2222 ⟨19, by decide⟩ (some 3)

private def cache2227 : Cache :=
  step cache2211 ⟨18, by decide⟩ 3
private def partial2227 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2211 ⟨18, by decide⟩ (some 3)

private def cache2228 : Cache :=
  step cache2227 ⟨19, by decide⟩ 0
private def partial2228 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2227 ⟨19, by decide⟩ (some 0)

private def cache2229 : Cache :=
  step cache2227 ⟨19, by decide⟩ 1
private def partial2229 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2227 ⟨19, by decide⟩ (some 1)

private def cache2230 : Cache :=
  step cache2227 ⟨19, by decide⟩ 2
private def partial2230 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2227 ⟨19, by decide⟩ (some 2)

private def cache2231 : Cache :=
  step cache2227 ⟨19, by decide⟩ 3
private def partial2231 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2227 ⟨19, by decide⟩ (some 3)

private def cache2232 : Cache :=
  step cache2208 ⟨17, by decide⟩ 3
private def partial2232 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2208 ⟨17, by decide⟩ (some 3)

private def cache2233 : Cache :=
  step cache2232 ⟨18, by decide⟩ 0
private def partial2233 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2232 ⟨18, by decide⟩ (some 0)

private def cache2234 : Cache :=
  step cache2233 ⟨19, by decide⟩ 0
private def partial2234 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2233 ⟨19, by decide⟩ (some 0)

private def cache2235 : Cache :=
  step cache2233 ⟨19, by decide⟩ 1
private def partial2235 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2233 ⟨19, by decide⟩ (some 1)

private def cache2236 : Cache :=
  step cache2233 ⟨19, by decide⟩ 2
private def partial2236 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2233 ⟨19, by decide⟩ (some 2)

private def cache2237 : Cache :=
  step cache2233 ⟨19, by decide⟩ 3
private def partial2237 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2233 ⟨19, by decide⟩ (some 3)

private def cache2238 : Cache :=
  step cache2232 ⟨18, by decide⟩ 1
private def partial2238 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2232 ⟨18, by decide⟩ (some 1)

private def cache2239 : Cache :=
  step cache2238 ⟨19, by decide⟩ 0
private def partial2239 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2238 ⟨19, by decide⟩ (some 0)

private def cache2240 : Cache :=
  step cache2238 ⟨19, by decide⟩ 1
private def partial2240 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2238 ⟨19, by decide⟩ (some 1)

private def cache2241 : Cache :=
  step cache2238 ⟨19, by decide⟩ 2
private def partial2241 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2238 ⟨19, by decide⟩ (some 2)

private def cache2242 : Cache :=
  step cache2238 ⟨19, by decide⟩ 3
private def partial2242 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2238 ⟨19, by decide⟩ (some 3)

private def cache2243 : Cache :=
  step cache2232 ⟨18, by decide⟩ 2
private def partial2243 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2232 ⟨18, by decide⟩ (some 2)

private def cache2244 : Cache :=
  step cache2243 ⟨19, by decide⟩ 0
private def partial2244 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2243 ⟨19, by decide⟩ (some 0)

private def cache2245 : Cache :=
  step cache2243 ⟨19, by decide⟩ 1
private def partial2245 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2243 ⟨19, by decide⟩ (some 1)

private def cache2246 : Cache :=
  step cache2243 ⟨19, by decide⟩ 2
private def partial2246 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2243 ⟨19, by decide⟩ (some 2)

private def cache2247 : Cache :=
  step cache2243 ⟨19, by decide⟩ 3
private def partial2247 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2243 ⟨19, by decide⟩ (some 3)

private def cache2248 : Cache :=
  step cache2232 ⟨18, by decide⟩ 3
private def partial2248 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2232 ⟨18, by decide⟩ (some 3)

private def cache2250 : Cache :=
  step cache2249 ⟨15, by decide⟩ 0
private def partial2250 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2249 ⟨15, by decide⟩ (some 0)

private def cache2251 : Cache :=
  step cache2249 ⟨15, by decide⟩ 1
private def partial2251 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2249 ⟨15, by decide⟩ (some 1)

private def cache2252 : Cache :=
  step cache2249 ⟨15, by decide⟩ 2
private def partial2252 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2249 ⟨15, by decide⟩ (some 2)

private def cache2253 : Cache :=
  step cache2252 ⟨16, by decide⟩ 0
private def partial2253 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2252 ⟨16, by decide⟩ (some 0)

private def cache2254 : Cache :=
  step cache2252 ⟨16, by decide⟩ 1
private def partial2254 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2252 ⟨16, by decide⟩ (some 1)

private def cache2255 : Cache :=
  step cache2252 ⟨16, by decide⟩ 2
private def partial2255 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2252 ⟨16, by decide⟩ (some 2)

private def cache2256 : Cache :=
  step cache2252 ⟨16, by decide⟩ 3
private def partial2256 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2252 ⟨16, by decide⟩ (some 3)

private def cache2257 : Cache :=
  step cache2256 ⟨17, by decide⟩ 0
private def partial2257 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2256 ⟨17, by decide⟩ (some 0)

private def cache2258 : Cache :=
  step cache2256 ⟨17, by decide⟩ 1
private def partial2258 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2256 ⟨17, by decide⟩ (some 1)

private def cache2259 : Cache :=
  step cache2256 ⟨17, by decide⟩ 2
private def partial2259 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2256 ⟨17, by decide⟩ (some 2)

private def cache2260 : Cache :=
  step cache2259 ⟨18, by decide⟩ 0
private def partial2260 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2259 ⟨18, by decide⟩ (some 0)

private def cache2261 : Cache :=
  step cache2259 ⟨18, by decide⟩ 1
private def partial2261 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2259 ⟨18, by decide⟩ (some 1)

private def cache2262 : Cache :=
  step cache2261 ⟨19, by decide⟩ 0
private def partial2262 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2261 ⟨19, by decide⟩ (some 0)

private def cache2263 : Cache :=
  step cache2261 ⟨19, by decide⟩ 1
private def partial2263 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2261 ⟨19, by decide⟩ (some 1)

private def cache2264 : Cache :=
  step cache2261 ⟨19, by decide⟩ 2
private def partial2264 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2261 ⟨19, by decide⟩ (some 2)

private def cache2265 : Cache :=
  step cache2261 ⟨19, by decide⟩ 3
private def partial2265 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2261 ⟨19, by decide⟩ (some 3)

private def cache2266 : Cache :=
  step cache2259 ⟨18, by decide⟩ 2
private def partial2266 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2259 ⟨18, by decide⟩ (some 2)

private def cache2267 : Cache :=
  step cache2266 ⟨19, by decide⟩ 0
private def partial2267 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2266 ⟨19, by decide⟩ (some 0)

private def cache2268 : Cache :=
  step cache2266 ⟨19, by decide⟩ 1
private def partial2268 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2266 ⟨19, by decide⟩ (some 1)

private def cache2269 : Cache :=
  step cache2266 ⟨19, by decide⟩ 2
private def partial2269 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2266 ⟨19, by decide⟩ (some 2)

private def cache2270 : Cache :=
  step cache2266 ⟨19, by decide⟩ 3
private def partial2270 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2266 ⟨19, by decide⟩ (some 3)

private def cache2271 : Cache :=
  step cache2259 ⟨18, by decide⟩ 3
private def partial2271 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2259 ⟨18, by decide⟩ (some 3)

private def cache2272 : Cache :=
  step cache2271 ⟨19, by decide⟩ 0
private def partial2272 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2271 ⟨19, by decide⟩ (some 0)

private def cache2273 : Cache :=
  step cache2271 ⟨19, by decide⟩ 1
private def partial2273 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2271 ⟨19, by decide⟩ (some 1)

private def cache2274 : Cache :=
  step cache2271 ⟨19, by decide⟩ 2
private def partial2274 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2271 ⟨19, by decide⟩ (some 2)

private def cache2275 : Cache :=
  step cache2271 ⟨19, by decide⟩ 3
private def partial2275 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2271 ⟨19, by decide⟩ (some 3)

private def cache2276 : Cache :=
  step cache2256 ⟨17, by decide⟩ 3
private def partial2276 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2256 ⟨17, by decide⟩ (some 3)

private def cache2277 : Cache :=
  step cache2276 ⟨18, by decide⟩ 0
private def partial2277 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2276 ⟨18, by decide⟩ (some 0)

private def cache2278 : Cache :=
  step cache2277 ⟨19, by decide⟩ 0
private def partial2278 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2277 ⟨19, by decide⟩ (some 0)

private def cache2279 : Cache :=
  step cache2277 ⟨19, by decide⟩ 1
private def partial2279 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2277 ⟨19, by decide⟩ (some 1)

private def cache2280 : Cache :=
  step cache2277 ⟨19, by decide⟩ 2
private def partial2280 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2277 ⟨19, by decide⟩ (some 2)

private def cache2281 : Cache :=
  step cache2277 ⟨19, by decide⟩ 3
private def partial2281 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2277 ⟨19, by decide⟩ (some 3)

private def cache2282 : Cache :=
  step cache2276 ⟨18, by decide⟩ 1
private def partial2282 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2276 ⟨18, by decide⟩ (some 1)

private def cache2283 : Cache :=
  step cache2276 ⟨18, by decide⟩ 2
private def partial2283 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2276 ⟨18, by decide⟩ (some 2)

private def cache2284 : Cache :=
  step cache2276 ⟨18, by decide⟩ 3
private def partial2284 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2276 ⟨18, by decide⟩ (some 3)

private def cache2285 : Cache :=
  step cache2249 ⟨15, by decide⟩ 3
private def partial2285 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2249 ⟨15, by decide⟩ (some 3)

private def cache2286 : Cache :=
  step cache2285 ⟨16, by decide⟩ 0
private def partial2286 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2285 ⟨16, by decide⟩ (some 0)

private def cache2287 : Cache :=
  step cache2285 ⟨16, by decide⟩ 1
private def partial2287 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2285 ⟨16, by decide⟩ (some 1)

private def cache2288 : Cache :=
  step cache2285 ⟨16, by decide⟩ 2
private def partial2288 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2285 ⟨16, by decide⟩ (some 2)

private def cache2289 : Cache :=
  step cache2285 ⟨16, by decide⟩ 3
private def partial2289 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2285 ⟨16, by decide⟩ (some 3)

private def cache2290 : Cache :=
  step cache2289 ⟨17, by decide⟩ 0
private def partial2290 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2289 ⟨17, by decide⟩ (some 0)

private def cache2291 : Cache :=
  step cache2289 ⟨17, by decide⟩ 1
private def partial2291 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2289 ⟨17, by decide⟩ (some 1)

private def cache2292 : Cache :=
  step cache2289 ⟨17, by decide⟩ 2
private def partial2292 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2289 ⟨17, by decide⟩ (some 2)

private def cache2293 : Cache :=
  step cache2292 ⟨18, by decide⟩ 0
private def partial2293 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2292 ⟨18, by decide⟩ (some 0)

private def cache2294 : Cache :=
  step cache2292 ⟨18, by decide⟩ 1
private def partial2294 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2292 ⟨18, by decide⟩ (some 1)

private def cache2295 : Cache :=
  step cache2292 ⟨18, by decide⟩ 2
private def partial2295 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2292 ⟨18, by decide⟩ (some 2)

private def cache2296 : Cache :=
  step cache2292 ⟨18, by decide⟩ 3
private def partial2296 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2292 ⟨18, by decide⟩ (some 3)

private def cache2297 : Cache :=
  step cache2289 ⟨17, by decide⟩ 3
private def partial2297 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2289 ⟨17, by decide⟩ (some 3)

private def cache2298 : Cache :=
  step cache2297 ⟨18, by decide⟩ 0
private def partial2298 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2297 ⟨18, by decide⟩ (some 0)

private def cache2299 : Cache :=
  step cache2298 ⟨19, by decide⟩ 0
private def partial2299 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2298 ⟨19, by decide⟩ (some 0)

private def cache2300 : Cache :=
  step cache2298 ⟨19, by decide⟩ 1
private def partial2300 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2298 ⟨19, by decide⟩ (some 1)

private def cache2301 : Cache :=
  step cache2298 ⟨19, by decide⟩ 2
private def partial2301 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2298 ⟨19, by decide⟩ (some 2)

private def cache2302 : Cache :=
  step cache2298 ⟨19, by decide⟩ 3
private def partial2302 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2298 ⟨19, by decide⟩ (some 3)

private def cache2303 : Cache :=
  step cache2297 ⟨18, by decide⟩ 1
private def partial2303 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2297 ⟨18, by decide⟩ (some 1)

private def cache2304 : Cache :=
  step cache2297 ⟨18, by decide⟩ 2
private def partial2304 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2297 ⟨18, by decide⟩ (some 2)

private def cache2305 : Cache :=
  step cache2297 ⟨18, by decide⟩ 3
private def partial2305 : Partial (Fin 20) (Fin 4) :=
  Function.update partial2297 ⟨18, by decide⟩ (some 3)

private theorem receipt2305 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2305, by decide⟩ cache2305 partial2305 = true := by
  decide +kernel

private theorem receipt2304 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2304, by decide⟩ cache2304 partial2304 = true := by
  decide +kernel

#print axioms receipt2304

private theorem receipt2303 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2303, by decide⟩ cache2303 partial2303 = true := by
  decide +kernel

private theorem receipt2302 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2302, by decide⟩ cache2302 partial2302 = true := by
  decide +kernel

private theorem receipt2301 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2301, by decide⟩ cache2301 partial2301 = true := by
  decide +kernel

private theorem receipt2300 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2300, by decide⟩ cache2300 partial2300 = true := by
  decide +kernel

private theorem receipt2299 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2299, by decide⟩ cache2299 partial2299 = true := by
  decide +kernel

private theorem receipt2298 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2298, by decide⟩ cache2298 partial2298 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2299,2300,2301,2302])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(5063387175788403 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2299
  · exact receipt2300
  · exact receipt2301
  · exact receipt2302

private theorem receipt2297 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2297, by decide⟩ cache2297 partial2297 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2298,2303,2304,2305])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(5069985856560978 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2298
  · exact receipt2303
  · exact receipt2304
  · exact receipt2305

private theorem receipt2296 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2296, by decide⟩ cache2296 partial2296 = true := by
  decide +kernel

private theorem receipt2295 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2295, by decide⟩ cache2295 partial2295 = true := by
  decide +kernel

private theorem receipt2294 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2294, by decide⟩ cache2294 partial2294 = true := by
  decide +kernel

private theorem receipt2293 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2293, by decide⟩ cache2293 partial2293 = true := by
  decide +kernel

private theorem receipt2292 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2292, by decide⟩ cache2292 partial2292 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2293,2294,2295,2296])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(5050189814242994 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2293
  · exact receipt2294
  · exact receipt2295
  · exact receipt2296

private theorem receipt2291 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2291, by decide⟩ cache2291 partial2291 = true := by
  decide +kernel

private theorem receipt2290 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2290, by decide⟩ cache2290 partial2290 = true := by
  decide +kernel

private theorem receipt2289 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2289, by decide⟩ cache2289 partial2289 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![2290,2291,2292,2297])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(5052387226492497 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2290
  · exact receipt2291
  · exact receipt2292
  · exact receipt2297

private theorem receipt2288 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2288, by decide⟩ cache2288 partial2288 = true := by
  decide +kernel

private theorem receipt2287 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2287, by decide⟩ cache2287 partial2287 = true := by
  decide +kernel

private theorem receipt2286 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2286, by decide⟩ cache2286 partial2286 = true := by
  decide +kernel

private theorem receipt2285 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2285, by decide⟩ cache2285 partial2285 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![2286,2287,2288,2289])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(5034792892440016 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2286
  · exact receipt2287
  · exact receipt2288
  · exact receipt2289

private theorem receipt2284 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2284, by decide⟩ cache2284 partial2284 = true := by
  decide +kernel

private theorem receipt2283 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2283, by decide⟩ cache2283 partial2283 = true := by
  decide +kernel

private theorem receipt2282 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2282, by decide⟩ cache2282 partial2282 = true := by
  decide +kernel

private theorem receipt2281 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2281, by decide⟩ cache2281 partial2281 = true := by
  decide +kernel

private theorem receipt2280 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2280, by decide⟩ cache2280 partial2280 = true := by
  decide +kernel

private theorem receipt2279 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2279, by decide⟩ cache2279 partial2279 = true := by
  decide +kernel

private theorem receipt2278 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2278, by decide⟩ cache2278 partial2278 = true := by
  decide +kernel

private theorem receipt2277 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2277, by decide⟩ cache2277 partial2277 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2278,2279,2280,2281])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(5017196410379475 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2278
  · exact receipt2279
  · exact receipt2280
  · exact receipt2281

private theorem receipt2276 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2276, by decide⟩ cache2276 partial2276 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2277,2282,2283,2284])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(5023795091152050 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2277
  · exact receipt2282
  · exact receipt2283
  · exact receipt2284

private theorem receipt2275 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2275, by decide⟩ cache2275 partial2275 = true := by
  decide +kernel

private theorem receipt2274 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2274, by decide⟩ cache2274 partial2274 = true := by
  decide +kernel

private theorem receipt2273 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2273, by decide⟩ cache2273 partial2273 = true := by
  decide +kernel

private theorem receipt2272 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2272, by decide⟩ cache2272 partial2272 = true := by
  decide +kernel

private theorem receipt2271 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2271, by decide⟩ cache2271 partial2271 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2272,2273,2274,2275])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(5003999048834067 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2272
  · exact receipt2273
  · exact receipt2274
  · exact receipt2275

private theorem receipt2270 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2270, by decide⟩ cache2270 partial2270 = true := by
  decide +kernel

private theorem receipt2269 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2269, by decide⟩ cache2269 partial2269 = true := by
  decide +kernel

private theorem receipt2268 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2268, by decide⟩ cache2268 partial2268 = true := by
  decide +kernel

private theorem receipt2267 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2267, by decide⟩ cache2267 partial2267 = true := by
  decide +kernel

private theorem receipt2266 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2266, by decide⟩ cache2266 partial2266 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2267,2268,2269,2270])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4993001247546227 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2267
  · exact receipt2268
  · exact receipt2269
  · exact receipt2270

private theorem receipt2265 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2265, by decide⟩ cache2265 partial2265 = true := by
  decide +kernel

private theorem receipt2264 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2264, by decide⟩ cache2264 partial2264 = true := by
  decide +kernel

private theorem receipt2263 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2263, by decide⟩ cache2263 partial2263 = true := by
  decide +kernel

private theorem receipt2262 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2262, by decide⟩ cache2262 partial2262 = true := by
  decide +kernel

private theorem receipt2261 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2261, by decide⟩ cache2261 partial2261 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2262,2263,2264,2265])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4982003446258387 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2262
  · exact receipt2263
  · exact receipt2264
  · exact receipt2265

private theorem receipt2260 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2260, by decide⟩ cache2260 partial2260 = true := by
  decide +kernel

private theorem receipt2259 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2259, by decide⟩ cache2259 partial2259 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2260,2261,2266,2271])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4995198659271314 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2260
  · exact receipt2261
  · exact receipt2266
  · exact receipt2271

private theorem receipt2258 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2258, by decide⟩ cache2258 partial2258 = true := by
  decide +kernel

private theorem receipt2257 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2257, by decide⟩ cache2257 partial2257 = true := by
  decide +kernel

private theorem receipt2256 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2256, by decide⟩ cache2256 partial2256 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![2257,2258,2259,2276])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(5006190017059377 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2257
  · exact receipt2258
  · exact receipt2259
  · exact receipt2276

private theorem receipt2255 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2255, by decide⟩ cache2255 partial2255 = true := by
  decide +kernel

private theorem receipt2254 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2254, by decide⟩ cache2254 partial2254 = true := by
  decide +kernel

private theorem receipt2253 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2253, by decide⟩ cache2253 partial2253 = true := by
  decide +kernel

private theorem receipt2252 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2252, by decide⟩ cache2252 partial2252 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![2253,2254,2255,2256])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4962207403940272 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2253
  · exact receipt2254
  · exact receipt2255
  · exact receipt2256

private theorem receipt2251 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2251, by decide⟩ cache2251 partial2251 = true := by
  decide +kernel

private theorem receipt2250 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2250, by decide⟩ cache2250 partial2250 = true := by
  decide +kernel

theorem receipt2249 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 ⟨2249, by decide⟩ cache2249 partial2249 = true := by
  apply actual_split (i := (15 : Fin 20))
    (children := ![2250,2251,2252,2285])
    (by
      change (.split (15 : Fin 20)
        (fun a => ⟨(5025977467345231 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2250
  · exact receipt2251
  · exact receipt2252
  · exact receipt2285

private theorem receipt2248 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2248, by decide⟩ cache2248 partial2248 = true := by
  decide +kernel

private theorem receipt2247 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2247, by decide⟩ cache2247 partial2247 = true := by
  decide +kernel

private theorem receipt2246 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2246, by decide⟩ cache2246 partial2246 = true := by
  decide +kernel

private theorem receipt2245 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2245, by decide⟩ cache2245 partial2245 = true := by
  decide +kernel

private theorem receipt2244 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2244, by decide⟩ cache2244 partial2244 = true := by
  decide +kernel

private theorem receipt2243 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2243, by decide⟩ cache2243 partial2243 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2244,2245,2246,2247])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4942411361622163 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2244
  · exact receipt2245
  · exact receipt2246
  · exact receipt2247

private theorem receipt2242 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2242, by decide⟩ cache2242 partial2242 = true := by
  decide +kernel

private theorem receipt2241 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2241, by decide⟩ cache2241 partial2241 = true := by
  decide +kernel

private theorem receipt2240 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2240, by decide⟩ cache2240 partial2240 = true := by
  decide +kernel

private theorem receipt2239 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2239, by decide⟩ cache2239 partial2239 = true := by
  decide +kernel

private theorem receipt2238 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2238, by decide⟩ cache2238 partial2238 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2239,2240,2241,2242])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4931413560334323 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2239
  · exact receipt2240
  · exact receipt2241
  · exact receipt2242

private theorem receipt2237 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2237, by decide⟩ cache2237 partial2237 = true := by
  decide +kernel

private theorem receipt2236 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2236, by decide⟩ cache2236 partial2236 = true := by
  decide +kernel

private theorem receipt2235 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2235, by decide⟩ cache2235 partial2235 = true := by
  decide +kernel

private theorem receipt2234 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2234, by decide⟩ cache2234 partial2234 = true := by
  decide +kernel

private theorem receipt2233 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2233, by decide⟩ cache2233 partial2233 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2234,2235,2236,2237])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4920415759046483 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2234
  · exact receipt2235
  · exact receipt2236
  · exact receipt2237

private theorem receipt2232 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2232, by decide⟩ cache2232 partial2232 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2233,2238,2243,2248])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4944608773347122 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2233
  · exact receipt2238
  · exact receipt2243
  · exact receipt2248

private theorem receipt2231 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2231, by decide⟩ cache2231 partial2231 = true := by
  decide +kernel

private theorem receipt2230 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2230, by decide⟩ cache2230 partial2230 = true := by
  decide +kernel

private theorem receipt2229 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2229, by decide⟩ cache2229 partial2229 = true := by
  decide +kernel

private theorem receipt2228 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2228, by decide⟩ cache2228 partial2228 = true := by
  decide +kernel

private theorem receipt2227 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2227, by decide⟩ cache2227 partial2227 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2228,2229,2230,2231])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4907218397501075 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2228
  · exact receipt2229
  · exact receipt2230
  · exact receipt2231

private theorem receipt2226 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2226, by decide⟩ cache2226 partial2226 = true := by
  decide +kernel

private theorem receipt2225 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2225, by decide⟩ cache2225 partial2225 = true := by
  decide +kernel

private theorem receipt2224 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2224, by decide⟩ cache2224 partial2224 = true := by
  decide +kernel

private theorem receipt2223 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2223, by decide⟩ cache2223 partial2223 = true := by
  decide +kernel

private theorem receipt2222 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2222, by decide⟩ cache2222 partial2222 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2223,2224,2225,2226])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4896220596213235 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2223
  · exact receipt2224
  · exact receipt2225
  · exact receipt2226

private theorem receipt2221 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2221, by decide⟩ cache2221 partial2221 = true := by
  decide +kernel

private theorem receipt2220 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2220, by decide⟩ cache2220 partial2220 = true := by
  decide +kernel

private theorem receipt2219 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2219, by decide⟩ cache2219 partial2219 = true := by
  decide +kernel

private theorem receipt2218 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2218, by decide⟩ cache2218 partial2218 = true := by
  decide +kernel

private theorem receipt2217 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2217, by decide⟩ cache2217 partial2217 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2218,2219,2220,2221])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4885222794925395 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2218
  · exact receipt2219
  · exact receipt2220
  · exact receipt2221

private theorem receipt2216 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2216, by decide⟩ cache2216 partial2216 = true := by
  decide +kernel

private theorem receipt2215 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2215, by decide⟩ cache2215 partial2215 = true := by
  decide +kernel

private theorem receipt2214 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2214, by decide⟩ cache2214 partial2214 = true := by
  decide +kernel

private theorem receipt2213 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2213, by decide⟩ cache2213 partial2213 = true := by
  decide +kernel

private theorem receipt2212 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2212, by decide⟩ cache2212 partial2212 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2213,2214,2215,2216])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4874224993637555 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2213
  · exact receipt2214
  · exact receipt2215
  · exact receipt2216

private theorem receipt2211 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2211, by decide⟩ cache2211 partial2211 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2212,2217,2222,2227])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4898418007938194 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2212
  · exact receipt2217
  · exact receipt2222
  · exact receipt2227

private theorem receipt2210 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2210, by decide⟩ cache2210 partial2210 = true := by
  decide +kernel

private theorem receipt2209 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2209, by decide⟩ cache2209 partial2209 = true := by
  decide +kernel

private theorem receipt2208 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2208, by decide⟩ cache2208 partial2208 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![2209,2210,2211,2232])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4909407217718321 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2209
  · exact receipt2210
  · exact receipt2211
  · exact receipt2232

private theorem receipt2207 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2207, by decide⟩ cache2207 partial2207 = true := by
  decide +kernel

private theorem receipt2206 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2206, by decide⟩ cache2206 partial2206 = true := by
  decide +kernel

private theorem receipt2205 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2205, by decide⟩ cache2205 partial2205 = true := by
  decide +kernel

theorem receipt2204 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2204, by decide⟩ cache2204 partial2204 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![2205,2206,2207,2208])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4856628511577008 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2205
  · exact receipt2206
  · exact receipt2207
  · exact receipt2208

private theorem receipt2203 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2203, by decide⟩ cache2203 partial2203 = true := by
  decide +kernel

private theorem receipt2202 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2202, by decide⟩ cache2202 partial2202 = true := by
  decide +kernel

private theorem receipt2201 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2201, by decide⟩ cache2201 partial2201 = true := by
  decide +kernel

private theorem receipt2200 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2200, by decide⟩ cache2200 partial2200 = true := by
  decide +kernel

private theorem receipt2199 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2199, by decide⟩ cache2199 partial2199 = true := by
  decide +kernel

private theorem receipt2198 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2198, by decide⟩ cache2198 partial2198 = true := by
  decide +kernel

private theorem receipt2197 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2197, by decide⟩ cache2197 partial2197 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2198,2199,2200,2201])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4841231589774035 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2198
  · exact receipt2199
  · exact receipt2200
  · exact receipt2201

private theorem receipt2196 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2196, by decide⟩ cache2196 partial2196 = true := by
  decide +kernel

private theorem receipt2195 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2195, by decide⟩ cache2195 partial2195 = true := by
  decide +kernel

private theorem receipt2194 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2194, by decide⟩ cache2194 partial2194 = true := by
  decide +kernel

private theorem receipt2193 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2193, by decide⟩ cache2193 partial2193 = true := by
  decide +kernel

private theorem receipt2192 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2192, by decide⟩ cache2192 partial2192 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2193,2194,2195,2196])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4830233788486195 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2193
  · exact receipt2194
  · exact receipt2195
  · exact receipt2196

private theorem receipt2191 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2191, by decide⟩ cache2191 partial2191 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2192,2197,2202,2203])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4845630709764626 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2192
  · exact receipt2197
  · exact receipt2202
  · exact receipt2203

private theorem receipt2190 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2190, by decide⟩ cache2190 partial2190 = true := by
  decide +kernel

private theorem receipt2189 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2189, by decide⟩ cache2189 partial2189 = true := by
  decide +kernel

private theorem receipt2188 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2188, by decide⟩ cache2188 partial2188 = true := by
  decide +kernel

private theorem receipt2187 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2187, by decide⟩ cache2187 partial2187 = true := by
  decide +kernel

private theorem receipt2186 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2186, by decide⟩ cache2186 partial2186 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2187,2188,2189,2190])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4817036426940787 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2187
  · exact receipt2188
  · exact receipt2189
  · exact receipt2190

private theorem receipt2185 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2185, by decide⟩ cache2185 partial2185 = true := by
  decide +kernel

private theorem receipt2184 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2184, by decide⟩ cache2184 partial2184 = true := by
  decide +kernel

private theorem receipt2183 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2183, by decide⟩ cache2183 partial2183 = true := by
  decide +kernel

private theorem receipt2182 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2182, by decide⟩ cache2182 partial2182 = true := by
  decide +kernel

private theorem receipt2181 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2181, by decide⟩ cache2181 partial2181 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2182,2183,2184,2185])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4806038625652947 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2182
  · exact receipt2183
  · exact receipt2184
  · exact receipt2185

private theorem receipt2180 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2180, by decide⟩ cache2180 partial2180 = true := by
  decide +kernel

private theorem receipt2179 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2179, by decide⟩ cache2179 partial2179 = true := by
  decide +kernel

private theorem receipt2178 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2178, by decide⟩ cache2178 partial2178 = true := by
  decide +kernel

private theorem receipt2177 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2177, by decide⟩ cache2177 partial2177 = true := by
  decide +kernel

private theorem receipt2176 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2176, by decide⟩ cache2176 partial2176 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2177,2178,2179,2180])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4795040824365107 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2177
  · exact receipt2178
  · exact receipt2179
  · exact receipt2180

private theorem receipt2175 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2175, by decide⟩ cache2175 partial2175 = true := by
  decide +kernel

private theorem receipt2174 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2174, by decide⟩ cache2174 partial2174 = true := by
  decide +kernel

private theorem receipt2173 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2173, by decide⟩ cache2173 partial2173 = true := by
  decide +kernel

private theorem receipt2172 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2172, by decide⟩ cache2172 partial2172 = true := by
  decide +kernel

private theorem receipt2171 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2171, by decide⟩ cache2171 partial2171 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2172,2173,2174,2175])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4784043023077267 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2172
  · exact receipt2173
  · exact receipt2174
  · exact receipt2175

private theorem receipt2170 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2170, by decide⟩ cache2170 partial2170 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2171,2176,2181,2186])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4808236037377906 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2171
  · exact receipt2176
  · exact receipt2181
  · exact receipt2186

private theorem receipt2169 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2169, by decide⟩ cache2169 partial2169 = true := by
  decide +kernel

private theorem receipt2168 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2168, by decide⟩ cache2168 partial2168 = true := by
  decide +kernel

private theorem receipt2167 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2167, by decide⟩ cache2167 partial2167 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![2168,2169,2170,2191])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4819225247158033 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2168
  · exact receipt2169
  · exact receipt2170
  · exact receipt2191

private theorem receipt2166 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2166, by decide⟩ cache2166 partial2166 = true := by
  decide +kernel

private theorem receipt2165 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2165, by decide⟩ cache2165 partial2165 = true := by
  decide +kernel

private theorem receipt2164 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2164, by decide⟩ cache2164 partial2164 = true := by
  decide +kernel

theorem receipt2163 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2163, by decide⟩ cache2163 partial2163 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![2164,2165,2166,2167])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4766446541016720 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2164
  · exact receipt2165
  · exact receipt2166
  · exact receipt2167

theorem receipt2162 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2162, by decide⟩ cache2162 partial2162 = true := by
  decide +kernel

theorem receipt2161 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2161, by decide⟩ cache2161 partial2161 = true := by
  decide +kernel

private theorem receipt2158 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2158, by decide⟩ cache2158 partial2158 = true := by
  decide +kernel

private theorem receipt2157 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2157, by decide⟩ cache2157 partial2157 = true := by
  decide +kernel

private theorem receipt2156 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2156, by decide⟩ cache2156 partial2156 = true := by
  decide +kernel

private theorem receipt2155 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2155, by decide⟩ cache2155 partial2155 = true := by
  decide +kernel

private theorem receipt2154 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2154, by decide⟩ cache2154 partial2154 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2155,2156,2157,2158])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4746650498698610 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2155
  · exact receipt2156
  · exact receipt2157
  · exact receipt2158

private theorem receipt2153 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2153, by decide⟩ cache2153 partial2153 = true := by
  decide +kernel

private theorem receipt2152 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2152, by decide⟩ cache2152 partial2152 = true := by
  decide +kernel

private theorem receipt2151 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2151, by decide⟩ cache2151 partial2151 = true := by
  decide +kernel

private theorem receipt2150 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2150, by decide⟩ cache2150 partial2150 = true := by
  decide +kernel

private theorem receipt2149 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2149, by decide⟩ cache2149 partial2149 = true := by
  decide +kernel

private theorem receipt2148 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2148, by decide⟩ cache2148 partial2148 = true := by
  decide +kernel

private theorem receipt2147 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2147, by decide⟩ cache2147 partial2147 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2148,2149,2150,2151])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4731253576895635 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2148
  · exact receipt2149
  · exact receipt2150
  · exact receipt2151

private theorem receipt2146 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2146, by decide⟩ cache2146 partial2146 = true := by
  decide +kernel

private theorem receipt2145 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2145, by decide⟩ cache2145 partial2145 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2146,2147,2152,2153])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4735652696886354 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2146
  · exact receipt2147
  · exact receipt2152
  · exact receipt2153

private theorem receipt2144 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2144, by decide⟩ cache2144 partial2144 = true := by
  decide +kernel

private theorem receipt2143 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2143, by decide⟩ cache2143 partial2143 = true := by
  decide +kernel

private theorem receipt2142 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2142, by decide⟩ cache2142 partial2142 = true := by
  decide +kernel

private theorem receipt2141 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨2141, by decide⟩ cache2141 partial2141 = true := by
  decide +kernel

private theorem receipt2140 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2140, by decide⟩ cache2140 partial2140 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![2141,2142,2143,2144])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4715856655092659 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2141
  · exact receipt2142
  · exact receipt2143
  · exact receipt2144

private theorem receipt2139 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2139, by decide⟩ cache2139 partial2139 = true := by
  decide +kernel

private theorem receipt2138 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2138, by decide⟩ cache2138 partial2138 = true := by
  decide +kernel

private theorem receipt2137 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨2137, by decide⟩ cache2137 partial2137 = true := by
  decide +kernel

private theorem receipt2136 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2136, by decide⟩ cache2136 partial2136 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![2137,2138,2139,2140])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4707058414062386 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2137
  · exact receipt2138
  · exact receipt2139
  · exact receipt2140

private theorem receipt2135 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨2135, by decide⟩ cache2135 partial2135 = true := by
  decide +kernel

private theorem receipt2134 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2134, by decide⟩ cache2134 partial2134 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![2135,2136,2145,2154])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4737847960603377 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2135
  · exact receipt2136
  · exact receipt2145
  · exact receipt2154

private theorem receipt2133 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2133, by decide⟩ cache2133 partial2133 = true := by
  decide +kernel

private theorem receipt2132 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2132, by decide⟩ cache2132 partial2132 = true := by
  decide +kernel

private theorem receipt2131 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨2131, by decide⟩ cache2131 partial2131 = true := by
  decide +kernel

theorem receipt2130 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨2130, by decide⟩ cache2130 partial2130 = true := by
  apply actual_split (i := (16 : Fin 20))
    (children := ![2131,2132,2133,2134])
    (by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4693861052516976 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt2131
  · exact receipt2132
  · exact receipt2133
  · exact receipt2134


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock1
