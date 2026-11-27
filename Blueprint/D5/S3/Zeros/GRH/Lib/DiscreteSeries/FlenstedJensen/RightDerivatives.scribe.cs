using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen;

internal sealed class RightDerivativesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Right Derivatives", H("Right Derivatives"),
        Blocks(
            Paragraph(Text("Smooth functions on U(p,q) as gl_n-module by right derivatives; chain rule.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/RightDerivatives.hasDerivAt_curve"),
                H("hasDerivAt_curve"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Chain rule along a curve γ in U(J): if γ'(t) = γ(t)X, then for smooth f the derivative of f ∘ γ at t is the right derivative of f along X at γ(t).")))))));
}
