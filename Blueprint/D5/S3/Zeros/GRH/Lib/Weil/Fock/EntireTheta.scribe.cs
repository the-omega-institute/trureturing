using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Fock;

internal sealed class EntireThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entire Theta", H("Entire Theta"),
        Blocks(
            Paragraph(Text("Theta function of a real vacuum datum is entire and determines the datum.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Fock/EntireTheta.differentiable_entireTheta"),
                H("differentiable_entireTheta"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For V with all signs positive and f a real vacuum, that is, fixed by inserting the Gaussian as real datum, the theta function Θ_f(y) = f(y)·exp(|y|²/2) on real vectors is entire.")))))));
}
