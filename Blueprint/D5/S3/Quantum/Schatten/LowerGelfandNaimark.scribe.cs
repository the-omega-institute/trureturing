using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class LowerGelfandNaimarkDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/LowerGelfandNaimark";
    private static LibraryNoteRef Background => LibraryNoteRef.Create("D5/L/Eigenstructure/bhatia1997matrixanalysis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The lower Gelfand–Naimark ratio inequality.",
        H("The lower Gelfand–Naimark ratio inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zhangli-lowergelfandnaimark-lower-gelfand-naimark-ratio"),
                DeclarationHandle.Create(Module + ".lower_gelfand_naimark_ratio"),
                H("Arbitrary-subset singular-value ratios"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("For invertible complex n by n matrices C and D and any subset I of the decreasing singular-value indices, the product over i in I of sᵢ(CD)/sᵢ(D) is at most the product of the |I| largest singular values of C. Invertibility makes every denominator positive; the empty subset gives the empty product one. The proof clips the scaled singular values of C below at one, compares Gram matrices, and bounds the subset product by the full determinant product."))),
                DescribeRole.Theorem))));
}
