# All c>=2, a>=2c+1, d>=a, b>=d+1

## Abstract

Low-X four-bank joint orders

**Theorem 1.1 (A shared physical permutation and the ear at cut zero).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Endpoint.actualSource_second_peak_low_x_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Endpoint.actualSource_second_peak_low_x_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural a,b,c,d with c>=2, a>=2c+1, d>=a and b>=d+1, put k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). There exist one list sigma of Fin k labels and one natural j<=k such that OriginalOrder k A sigma and OriginalOrder (k+1) (2A) (earWord k sigma j). The construction takes j=0. Both words permute all their physical labels, have exact centered-source sum zero, and satisfy the strip bounds for every natural take-prefix, including empty, full and overlong prefixes. Their zero sums also preserve these bounds under any number of repetitions. The unrestricted four-gap joint lift and Circle J remain open.

Write z=2^c, x=2^a, h=2^(d-a), q=2^(b-a-1), E=x/(2z^2), D=x/4 and S=hx/(2z). The four positive banks have dyadic coefficient rows (0,z/4,0,D-E), (S-1,z/4-1,r,D), (hx/2-S,0,2q-1-r-e,E-1), and (0,0,xq-2q+e,0), in chain order U,V,W,X. The banks end at the four actual negative terminals U,X,W,V. PhysicalBanks proves that the underlying label sets are disjoint and cover all nonterminal labels, and computes their actual old and new masses. Terminals uses the doubled integer native identities for each terminal; integer quotient values are never replaced by rational division.

The e reservation is enabled exactly when 2a-2<b and has exponent b+1-2a. The r reservation is enabled exactly when 2c<=b-d. Its exponent is b-d-2c plus one in the collision 2a=d+2c+1 with the e reservation enabled. These two reserved bits are distinct within the native W ladder. E=1, the exponent-zero e=1 reservation, d=a, b=d+1 and reservation collisions all remain in the domain; none is discarded by an extra strict inequality.

Selection transfers the rational interval certificates to all physical dyadic parameters. It separates the two reservation thresholds and uses the affine interval identities and the concave second-margin chord identity from Intervals. This supplies three old lower seams and three new upper peaks from the actual bank masses. Positivity within each bank and the exact final V terminal bounds complete the endpoint through AscendingD2.Schedule.four_perm and four_strip.

The other strip sides follow from matched charge at every actual old label: chi(i)=2 oldValue(i)-newValue(i)>=0, and the whole word has charge A. Thus every prefix has nonnegative remaining charge A+newPrefix-2 oldPrefix. First the old lower side gives the new lower side; the new upper side then gives twice oldPrefix<=N, hence oldPrefix<=floor(N/2), where N=2^k-1. The fresh label contributes exactly A. Source totals, signs and chain values come from PacketNormalForm.Source; the actual source and ear conversion is PacketNormalForm.Endpoint.actual_nat_joint_iff. These are mathematical applications of the existing prefix and transport results, with the new low-X bank allocation supplying the missing margins.

The Reg companion represents the entire original family with four data binders and four domain proof binders through the two actual OriginalOrder readouts. It proves whole-family variation, deletion sensitivity for each readout, and dependence on the actual source seed using the existing dependent-family template. Continuation is unknown.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Endpoint.actualSource_second_peak_low_x_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint](../PacketNormalForm/Endpoint.md)
