using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class GluingWithSupportsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gluing With Supports", H("Gluing With Supports"),
        Blocks(
            Paragraph(Text("Compatible classes with supports glue when lower degrees vanish.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/GluingWithSupports.exists_glued_class"),
                H("exists_glued_class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Gluing: let finitely many W_i ⊂ V lie in an intersection-closed class whose members A have H^n(A, U ∩ A) = 0 for n < d, with U ∪ ⋃ W_i dense. Then classes in H^d(W_i, U ∩ W_i) agreeing on overlaps come from H^d(V,U).")))))));
}
