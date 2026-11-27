using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Periods;

internal sealed class DegreeAndUnipotentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree And Unipotent", H("Degree And Unipotent"),
        Blocks(
            Paragraph(Text("Graded hermitian spaces: definite part plus string, unipotent and Bessel subgroups. Degree of graded matrices, adjoints, basic facts on the Bessel subgroup.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Periods/DegreeAndUnipotent.mem_besselGroup_iff_sub_one"),
                H("mem_besselGroup_iff_sub_one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("g lies in Grading.besselGroup if and only if it fixes each string vector of grade ≥ 0 up to higher grades: for such an index k, the entry (i, k) of its matrix minus 1 vanishes whenever grade(i) ≤ grade(k).")))))));
}
