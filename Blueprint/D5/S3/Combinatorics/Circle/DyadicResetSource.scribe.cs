using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class DyadicResetSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native repeated one-bit source and its exact strip.",
        H("The native repeated one-bit source and its exact strip"),
        Blocks(
            Describe.Lean(DescribeId.Create("dyadic-package-dyadicresetsource"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/DyadicResetSource.legal_iff"),
                H("The native repeated one-bit source and its exact strip"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For natural m>=3 and r>=1, set k=m*r, d=(2^k-1)/(2^m-1), B=2^(m-2), and M=2*B-1. At every actual physical label i in Fin(k), actualSource(k,d,i) is d*2^(i mod m) unless i mod m=m-1, when it is -d*M. The positive denominations are precisely 1,2,4,...,B in units of d. They are not all integers between one and B. Each residue has r distinct physical occurrences.")),
                    Paragraph(Text("The source equality consumes the original repeated_source, multiplier and scaling declarations in ThreeRowSource. The original owner is made reusable rather than duplicated. The native capacity is ExpandingSourcePath.half(k). It satisfies M*d<=half(k)<(M+1)*d, while the modulus is (4*B-1)*d. Every attainable prefix is divisible by d. Consequently native Legal is equivalent to Nodup together with InStrip(scaled,M,0,W); this includes every natural take, the empty prefix, and takes beyond the list length.")),
                    Paragraph(Text("LARGE is exactly the pair of physical residue classes m-2 and m-1. SMALL stops at B/2. Equal numerical values, repeated periods, and nonunits do not merge labels or add hypotheses. The source family is a genuine restriction on t. The arbitrary-source Circle C3.1 statement remains open."))),
                DescribeRole.Theorem)), []));
}
