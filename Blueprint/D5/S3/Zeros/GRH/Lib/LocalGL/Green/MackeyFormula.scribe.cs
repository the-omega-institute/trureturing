using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Green;

internal sealed class MackeyFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mackey Formula", H("Mackey Formula"),
        Blocks(
            Paragraph(Text("Similarity classes of matrices, class functions, parabolic induction product, rank parts, means. Class functions under parabolic induction form a commutative ring; constant one is invertible. Block means (coproduct), cuspidality, inner product, adjoints, Brauer lift, cuspidal function. Group order times a central idempotent of the group algebra is a character. Mackey formula: block means are multiplicative for parabolic induction.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Green/MackeyFormula.blockAverage_mul"),
                H("blockAverage_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Mackey formula: the block averaging map δ of Hall.blockAverage is multiplicative, δ(F * H) = δF * δH, with the Hall product taken in each of the two variables on the right.")))))));
}
