using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.Adjacent;

internal sealed class FourNegativeAdjacentNearJointLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common physical joint order for the three central paired-gap branches",
        H("Near-diagonal paired gaps inside the independent endpoint"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-four-negative-adjacent-near-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentNearJointLift.actualSource_four_negative_adjacent_near_joint_lift"),
                H("The unbounded three-branch checkpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let r,s>=2 be natural coordinates with r<=s+1 and s<=r+1. Put k=2r+2s and A=1+2^r+2^(2r)+2^(2r+s). There are a list sigma of the original Fin(k) physical labels and a natural cut j<=k such that OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)) both hold. Each OriginalOrder includes its actual physical permutation, exact integer total zero and every natural prefix in its centered half-modulus strip. The old strip is [0,(2^k-2)/2] and the new strip is [0,2^k-1]. Equal numerical values retain separate physical labels; no coprimality or primitive-period assumption is made.")),
                    Paragraph(Text("The parameter hypotheses give exactly three branches. If r=s, the repeated_source theorem supplies four physical copies of the one-bit period. The natural old order has width H=(2^(r-1)-1)A with 2H+A=2^k-1. Nonnegative source charges summing to A then prove that placing the literal ear first gives the new strip. If r=s+1, this proof directly consumes the accepted actualSource_four_negative_adjacent_double_joint_lift theorem at its owning module and preserves its numeric cut j=2s+r. If s=r+1, the reverse construction transfers the first U and V positive occurrences to the X and W blocks, respectively, and places the ear first. The exceptional pair (2,3) is handled by its exact physical list; the symbolic reverse construction applies to every r>=3.")),
                    Paragraph(Text("The cyclic doubling action explains the relationship between these constructions without identifying physical occurrences. Independent old recurrences yA=N+B,yB=N+L,xL=N+M,xM=N+A determine the four chains, while the new modulus 2N+1 changes their coefficients by nonnegative charges. The diagonal factors through an actual repeated numerical source; the independent table still uses every physical label. The joint endpoint uses the same sigma in both moduli and the literal earWord, so an arbitrary phase rotation or a value-based quotient cannot substitute for its witness.")),
                    Paragraph(Text("The Reg mirror reconstructs the full two-coordinate theorem telescope, including both lower bounds and the near-diagonal relation, with both actual OriginalOrder predicate-valued readouts. Its variation replaces the family by rejecting readouts, each deletion rejects the whole family at a valid parameter, and its dependence varies the actual seed for each readout. The residual continuation is unknown. These registration facts do not enlarge the mathematical parameter range.")),
                    Paragraph(Text("FourNegativeAdjacentPairsJointLift consumes this near-diagonal theorem together with the explicit mask inventories, numeric ear cuts and simultaneous old/new all-prefix bounds of FourNegativeAdjacentFarLeft and FourNegativeAdjacentFarRight. That endpoint covers all independent r,s>=2; this theorem records its three central branches. Unrestricted four-independent-gap physical J and Circle C3.1 remain active and open. The research context is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2; no external novelty is claimed."))),
                DescribeRole.Theorem)), []));
}
