using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class PrimitiveBridgeCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive stochastic bridges and the full integer path-difference lattice.",
        H("Primitive bridge cancellation"),
        Blocks(
            Paragraph(Text(
                "Let V be an arbitrary finite nonempty set, q a natural number, P a real "
                + "row-stochastic primitive matrix on V, and g an integer q-vector on every "
                + "ordered vertex pair. A supported edge i to j has P(i,j)>0. Gamma(n,i,j) "
                + "consists of the actual supported quiver paths of length n from i to j, "
                + "including the empty path at length zero. Write G(p) for the sum of the "
                + "edge charges and W(p) for the product of the transition probabilities. "
                + "The set D contains G(a)-G(b) for every pair of supported paths of equal "
                + "length and equal endpoints, over all lengths and endpoints. Lambda is "
                + "the integer span of D.")),
            Paragraph(Text(
                "For a real q-vector x, dot(x,lambda) is the sum of x(k) times lambda(k). "
                + "The twisted matrix has entries M(x)(i,j)=P(i,j) exp(i dot(x,g(i,j))). "
                + "The full annihilator U consists of x for which dot(x,lambda) is an "
                + "integer multiple of 2 pi for every lambda in Lambda. For a finite set F "
                + "of integer vectors, E(F,x) is the sum over F of 1-cos(dot(x,lambda)). "
                + "Charges on edges of zero transition probability have no effect on these objects.")),
            Describe.Lean(
                DescribeId.Create("primitive-bridge-cancellation"),
                DeclarationHandle.Create("D5/S3/TotalVariation/PrimitiveBridgeCancellation.primitive_bridge_cancellation"),
                H("One bridge length and uniform cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any prescribed endpoints iStar and jStar there exist L>0, a finite "
                    + "set F of distinct integer q-vectors, and c>0, all independent of x, "
                    + "such that the integer span of F is Lambda. Every lambda in F is "
                    + "G(a)-G(b) for actual paths a,b in Gamma(L,iStar,jStar), with "
                    + "c<=W(a)W(b). The entry a0=(P^L)(iStar,jStar) is positive. For every "
                    + "real q-vector x, c E(F,x)<=a0^2-|M(x)^L(iStar,jStar)|^2, where the "
                    + "absolute value is the norm of that scalar complex entry. Moreover, "
                    + "E(F,x)=0 if and only if x belongs to the full U. This includes q=0 "
                    + "and the zero lattice, with no gauge or quotient-metric identification.")),
                    Paragraph(Text(
                    "Fixed-length supported paths are finite because their vertex lists "
                    + "determine them. Splitting off the last supported edge gives the exact "
                    + "matrix-power recurrence, for both P and M(x). Integer finite generation "
                    + "selects finitely many original differences. Primitivity and stochastic "
                    + "row sums provide paths at every sufficiently large length. A common "
                    + "prefix and a common suffix are attached to both members of each selected "
                    + "pair, preserving its difference. Distinct differences make the selected "
                    + "ordered path pairs injective. Their positive weighted cosine deficits "
                    + "can therefore be retained once each from the nonnegative sum over all "
                    + "ordered bridge pairs. Integer span then gives the complete zero set."))),
                DescribeRole.Theorem))));
}
