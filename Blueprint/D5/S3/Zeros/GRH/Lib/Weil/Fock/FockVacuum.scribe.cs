using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Fock;

internal sealed class FockVacuumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fock Vacuum", H("Fock Vacuum"),
        Blocks(
            Paragraph(Text("Sign projections, real multiplier as conjugate determinant of negative block, its norm bound. The Gaussian is a reproducing vacuum; integrability and polynomial growth bounds.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Fock/FockVacuum.integrable_exp_mul_realVac"),
                H("integrable_exp_mul_realVac"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For every real C, the function u ↦ exp(C‖u‖) exp(−|u|²/2) on ℂ^ι, with ‖u‖ the maximum norm and |u| the Euclidean norm, is integrable for the normalised Lebesgue measure realMeasure.")))))));
}
