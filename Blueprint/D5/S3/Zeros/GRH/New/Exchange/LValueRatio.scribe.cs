using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class LValueRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "L Value Ratio", H("L Value Ratio"),
        Blocks(
            Paragraph(Text("Finitely many pairs (character, integer), from finiteness of tame Hecke characters. Powers of tame characters, m-fold twists, characters of the chain. Ratio of twisted to untwisted Hecke L-value; the trivial twist.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/LValueRatio.ratio"),
                H("ratio"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The ratio |L(z, (νϑ^s)⁻¹)| / |L(z, ν⁻¹)|, Euler factors removed at the chosen places above g in both, and at Q in the numerator.")))))));
}
