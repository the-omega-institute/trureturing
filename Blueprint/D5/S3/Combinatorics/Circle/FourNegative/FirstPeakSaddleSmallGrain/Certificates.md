# Twelve unbounded phase charts

## Abstract

Nineteen direct c=2 margins

**Definition 1.1 (Physical seams followed by capacities).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates.margin`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates.margin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At z=4 put D=5y+1, A=xD+1, B=xt(y+1)+t+1, L=4xt+4t+5 and M=4ty+D. The first twelve Fin19 entries are the exact old and enlarged seam pairs. The seven additional entries are s-1,x-2s,r-1,s-r,v,t-2v-2,y-8(h+1). Margins requires all nineteen to be nonnegative.

**Lemma 1.2 (A direct phase chart with unbounded T).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates.chart_K1_J1_0`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates.chart_K1_J1_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The twelve retained theorems chart_K1_J1_0 through _3, chart_K1_J2_0 through _3 and chart_K2_J1_0 through _3 use t=16,32,64,128 plus 10T with T>=0 and the explicit native s,r,h,v. Each proves nineteen polynomial inequalities. The three t=8 exceptions are inline in Arithmetic.select_chart rather than standalone named certificates. No finite exponent cutoff or external certificate is a premise.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates.chart_K1_J1_0`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates.margin`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Descending/Endpoint](../Descending/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Masks](../MaxPlusTwo/Chambers/Masks.md)
