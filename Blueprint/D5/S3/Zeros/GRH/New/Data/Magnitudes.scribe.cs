using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Data;

internal sealed class MagnitudesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Magnitudes", H("Magnitudes"),
        Blocks(
            Paragraph(Text("Logarithmic size calculus (upper and lower exponent bounds) for the parameters of the data.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Data/Magnitudes.roundUp_mem_Icc"),
                H("roundUp_mem_Icc"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If the real number F satisfies exp(l) ≤ F for some real l, so that F > 0, then the rounded value N₁⌈F/N₁⌉ (Data.roundUp) lies in the closed interval [F, F + N₁].")))))));
}
