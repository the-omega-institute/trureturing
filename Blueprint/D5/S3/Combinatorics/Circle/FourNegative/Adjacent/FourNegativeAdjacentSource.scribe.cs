using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.Adjacent;

internal sealed class FourNegativeAdjacentSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent paired-gap physical source identities",
        H("The same four chains in both centered moduli"),
        Blocks(
            Paragraph(Text("Let r,s>=2 be independent naturals, x=2^r, y=2^s, k=2r+2s and N=x^2 y^2-1. Set A=1+x+x^2+x^2y, B=1+y+xy+x^2y, L=1+y+y^2+xy^2, M=1+x+xy+xy^2 and e=1+x+xy. The private coefficient_bounds proof establishes strict positivity and 2D<N for each old coefficient D. It expands at x=4+u,y=4+v with u,v>=0, producing polynomials with positive coefficients. The new coefficients 2A,2B-1,2L-1-y and 2M-e are positive as well.")),
            Paragraph(Text("The private chains proof starts at the actual label zero and uses yA=N+B, yB=N+L, xL=N+M and xM=N+A. The new recurrences use modulus 2N+1 and successor coefficients 2B-1,2L-1-y,2M-e,A. It directly reuses the generic shift at FourNegativeAdjacentDoubleJointLift and centered_ladder at ThreeBitSource; no source rotation is introduced. On U_i=i and V_i=s+i for i<s, and W_i=2s+i and X_i=2s+r+i for i<r, every nonterminal value is its positive coefficient times 2^i. The terminal old values are -(N-B)/2, -(N-L)/2, -(N-M)/2 and -(N-A)/2. The new terminal values use the corresponding new successor coefficient and modulus 2N+1. The fresh value at the original physical label k is exactly A.")),
            Paragraph(Text("FourNegativeAdjacentReverse, FourNegativeAdjacentFarLeft and FourNegativeAdjacentFarRight consume these source identities at its actual physical block, mass, negative-jump and ear readouts. The identities apply for all independent r,s>=2 without a primitive-period, distinct-values or unit-gcd assumption. Multiplication by two acts on centered residue values; the physical labels remain occurrences of that action and are never identified by equal numerical values. A full-period return is not used as injectivity or minimal-period evidence.")),
            Paragraph(Text("This module supplies the actual source table. FourNegativeAdjacentPairsJointLift combines the literal common orders and coupled prefix bounds for all five dyadic branches to prove the independent paired-gap endpoint. Unrestricted four-independent-gap physical J and Circle C3.1 remain active and open."))), []));
}
