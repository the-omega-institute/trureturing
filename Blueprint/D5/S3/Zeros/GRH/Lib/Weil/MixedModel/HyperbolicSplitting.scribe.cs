using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class HyperbolicSplittingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hyperbolic Splitting", H("Hyperbolic Splitting"),
        Blocks(
            Paragraph(Text("Standard polarisation of the hyperbolic space as a splitting.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/HyperbolicSplitting.hyperbolicSplitting"),
                H("hyperbolicSplitting"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The splitting of hyperbolic space of rank 2p over the zero space, with l the first p and k the last p basis vectors.")))))));
}
