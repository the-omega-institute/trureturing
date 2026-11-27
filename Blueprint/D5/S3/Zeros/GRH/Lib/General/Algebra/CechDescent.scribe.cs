using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class CechDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cech Descent", H("Cech Descent"),
        Blocks(
            Paragraph(Text("Long exact sequences of abelian groups, their morphisms and the shift. Long exact Ext sequences, four and five lemmas for ladders. Dévissage for maps of delta-functors; Čech descent of bijectivity, step by step.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/CechDescent.bijective_range_of_cech"),
                H("bijective_range_of_cech"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Čech descent: if the maps f obey the five and four lemmas (Devissage) and are bijective in all degrees on Z of every fibre power of p: E → Y, E included, then they are so on Z[im p].")))))));
}
