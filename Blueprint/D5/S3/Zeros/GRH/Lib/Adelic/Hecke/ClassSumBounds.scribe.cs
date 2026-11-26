using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Hecke;

internal sealed class ClassSumBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Class Sum Bounds", H("Class Sum Bounds"),
        Blocks(
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Hecke/ClassSumBounds.sqrt_weylNormSq_classSum_le"),
                H("sqrt_weylNormSq_classSum_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Class sums stay integral after clearing automorphism orders; triangle inequality for their norms.")))))));
}
