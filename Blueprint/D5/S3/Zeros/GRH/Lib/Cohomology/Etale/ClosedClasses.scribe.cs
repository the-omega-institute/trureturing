using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class ClosedClassesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed Classes", H("Closed Classes"),
        Blocks(
            Paragraph(Text("Closed classes of functors: stable under bijections, finite unions and exact functors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/ClosedClasses.comap"),
                H("comap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If a property P of functors C → Ab holds for 0 and, in short exact sequences whose first term has P, holds for the middle term iff for the last, then N ↦ P(ΦN) has the same two features, for Φ exact.")))))));
}
