using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Trace;

internal sealed class LabelRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Label Rigidity", H("Label Rigidity"),
        Blocks(
            Paragraph(Text("A Hecke eigensystem meets at most one primitive cuspidal type at a chosen place.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Trace/LabelRigidity.hasRigidLabels_spaceY_zero"),
                H("hasRigidLabels_spaceY_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Y₀ satisfies Data.HasRigidLabels: for each eigensystem p and chosen place above g, the idempotent e_c kills the p-part for all but at most one primitive label c of degree r.")))))));
}
