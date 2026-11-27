using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class SubmersionZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Submersion Zero", H("Submersion Zero"),
        Blocks(
            Paragraph(Text("Separating forms separate U ⊗ V; ultrametric bound on Mx; vanishing via submersion.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/SubmersionZero.eq_zero_of_submersion"),
                H("eq_zero_of_submersion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let G be entire on a complex Banach space F, and f: E → F strictly differentiable at a with surjective derivative. If G∘f vanishes near a, then G = 0.")))))));
}
