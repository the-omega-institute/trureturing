using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.SiegelWeil;

internal sealed class AuxPairVanishingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Aux Pair Vanishing", H("Aux Pair Vanishing"),
        Blocks(
            Paragraph(Text("Vanishing descent for one level datum passes to all data, via reflection sums.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/SiegelWeil/AuxPairVanishing.descentsVanish_of_reflectionSum"),
                H("descentsVanish_of_reflectionSum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Suppose ψ ≠ 1 at each place of Q, the reflection sums of all nonzero rows at M kill y, and the conjugate u-coordinate of y has zero descent to W for all data P ⊗ Υ. Then its descents vanish for all data vacuum off M, Q and conjugates.")))))));
}
