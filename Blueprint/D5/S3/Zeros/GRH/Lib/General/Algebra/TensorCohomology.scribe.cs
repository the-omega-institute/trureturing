using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class TensorCohomologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor Cohomology", H("Tensor Cohomology"),
        Blocks(
            Paragraph(Text("Flat change of coefficients in Ext cohomology is a map of delta-functors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/TensorCohomology.devissage"),
                H("devissage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For M flat over S, the maps M ⊗_S Ext^n(N, Φ) → Ext^n(N, M ⊗ Φ) admit dévissage in N (Devissage): the four and five lemmas apply to them along short exact sequences.")))))));
}
