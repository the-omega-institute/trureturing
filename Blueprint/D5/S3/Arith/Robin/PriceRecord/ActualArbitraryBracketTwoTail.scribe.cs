using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualArbitraryBracketTwoTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unconditional asymptotic bounds for the full binary tail of original strict records.",
        H("The full original binary tail at every coefficient above four"),
        Describe.Lean(
            DescribeId.Create("arbitrary-bracket-full-original-binary-tail"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualArbitraryBracketTwoTail.full_original2tail_power_bound"),
            H("A uniform threshold before both the original integer and its price"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For EVERY real K>4 there exists a natural M such that, for EVERY natural m>=M "
                    + "and EVERY real mu>0, if F_mu(n)<F_mu(m) for ALL positive natural n<m, then "
                    + "2^(v_2(m)-optimalLayerCount(ownPrice(m),2))<K log(m). Here F is the literal "
                    + "goldenResourceObjective, T=log(m), ownPrice(m)=1/(T log(T)), and subtraction "
                    + "in the exponent is natural truncated subtraction. The tail contains EVERY "
                    + "original binary layer after the strict canonical cutoff, including equality "
                    + "layers. If the cutoff is at least v_2(m), the tail is empty and its power is one. "
                    + "The threshold M precedes m and mu. No bad-layer, bracket, non-global, BHP, "
                    + "or comparison-price hypothesis remains in the public theorem.")),
                Paragraph(Text(
                    "The all-integer bracketing theorem supplies an actual s>0 with "
                    + "strictInteger(s)<=m<=maximalInteger(s). Put c=ownPrice(m), "
                    + "h=(v_2(m)-optimalLayerCount(c,2))log(2), and let R be the full ordinary tail reward. "
                    + "The existing actual integer deletion gives F_s(deleted)-F_s(m)=s h-R and R<2 c log(2). "
                    + "If m is globally optimal at s, use g=0 and s h<=R. Otherwise the existing greatest "
                    + "feasible optimizer C<m gives g=log(m/C)>0 and s g exp(g)<1. Its global comparison "
                    + "with the full deletion and the ORIGINAL strict mu-record give "
                    + "s h-R<(s-mu)g, and global comparison with m also implies mu<s. "
                    + "Both cases yield h<g+2(c/s)log(2), with g>=0 and s g exp(g)<1.")),
                Paragraph(Text(
                    "For each r>1 choose 1<alpha<r and epsilon>0 with (1-epsilon)alpha>1. "
                    + "The existing strict_inventory_uniform_growth gives log(U_(alpha T))>T eventually. "
                    + "If c/s>r, an eventual scalar inequality gives s<c/r<=price(alpha T). "
                    + "The exact strict inventory divisibility law then gives U_(alpha T)|strictInteger(s)<=m, "
                    + "contradicting that growth. Thus c/s<=r uniformly over every bracket price, using only "
                    + "the lower bracket and retaining all simultaneous ties. This step uses the existing "
                    + "unconditional MediumPNT theorem through uniform inventory growth; it adds no prime "
                    + "distribution supplier, inverse-price API, or all-layer summation theorem.")),
                Paragraph(Text(
                    "For T>1, c/s<=r and s g exp(g)<1 force g<log(r T): at a larger g the product "
                    + "is at least one. Hence h<log(r T)+2r log(2), so the exact original tail power "
                    + "is smaller than r exp(2r log(2)) T. Continuity at r=1, where this coefficient "
                    + "equals four, permits r>1 with r exp(2r log(2))<K. This is a new composition "
                    + "of the existing canonical inventory growth, literal bracketing and actual full-tail "
                    + "deletion and optimizer-gap results. It makes no claim of a new PNT, a finite "
                    + "coefficient-four theorem at arbitrary price, a single-layer bound, the eight-bank "
                    + "small-slack obstruction, Robin beyond 5040, or RH."))),
            DescribeRole.Theorem)));
}
