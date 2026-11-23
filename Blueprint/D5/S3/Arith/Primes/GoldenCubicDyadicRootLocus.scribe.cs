using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicDyadicRootLocusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every positive native Lucas level the rational Cardano cubic has a sharp dyadic root locus.",
        H("Exact dyadic root locus of the native rational Cardano cubic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-cubic-dyadic-locus"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicDyadicRootLocus.native_cubic_dyadic_locus"),
                H("One full-width even class and two half-width odd classes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let x be the actual Lucas value at index 3^j, j positive, and B equal x squared plus three. The rational Cardano polynomial is T cubed minus 3BT plus 2Bx. Its odd roots collide modulo two, so simple-root lifting in that residue ring alone only finds the even branch.")),
                    Paragraph(Text("Lift an even root of the half-scaled polynomial by a constructive correction, invert its odd derivative factor, and use the square-discriminant identity to produce the two odd branches. Their difference is twice an odd integer. At each precision at least three the full solution locus is the union of one even class at the tested depth and two distinct odd classes one bit shallower.")),
                    Paragraph(Text("The statement is an arbitrary-depth residue theorem, not an identification of a global tame conductor or a resolution of Wall-Sun-Sun."))),
                DescribeRole.Theorem))));
}
