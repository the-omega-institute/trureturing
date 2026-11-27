using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen;

internal sealed class PsiSmoothDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Psi Smooth", H("Psi Smooth"),
        Blocks(
            Paragraph(Text("The coefficient as a smooth function on the group; continuity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/PsiSmooth.dsCoeffSmooth"),
                H("dsCoeffSmooth"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The restriction of ψ_λ to U(diag ε), as an element of the space of smooth complex-valued functions on that group.")))))));
}
