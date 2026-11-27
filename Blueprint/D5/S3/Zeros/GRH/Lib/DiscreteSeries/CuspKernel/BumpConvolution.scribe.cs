using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.CuspKernel;

internal sealed class BumpConvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bump Convolution", H("Bump Convolution"),
        Blocks(
            Paragraph(Text("Convolution with compactly supported smooth functions is smooth; derivatives fall on the bump.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BumpConvolution.hasDerivAt_smear"),
                H("hasDerivAt_smear"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Derivatives of a convolution fall on the test function: if a curve γ in U(diag ε) has γ'(t) = γ(t)X, then smear α along γ has derivative at t the value at γ(t) of smear (Xα), Xα the right derivative.")))))));
}
