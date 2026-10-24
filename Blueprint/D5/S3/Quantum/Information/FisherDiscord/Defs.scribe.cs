using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FisherDiscord;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/liluozhang2025fisherdiscord");

    private static DocumentBlock.Describe Item(string name, string title, string body) =>
        Describe.Lean(DescribeId.Create("fisher-discord-defs-" + name.ToLowerInvariant().Replace("₂", "2")),
            DeclarationHandle.Create("D5/S3/Quantum/Information/FisherDiscord/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(body))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite matrix definitions for Fisher discord and partial trace.",
        H("Fisher discord conventions"), Blocks(
            Paragraph(Text("Partial trace sums the matrix entries with identical second coordinates.")),
            Item("liftLeft", "Local observables", "The observable on the first factor is tensored with the identity on the second factor."),
            Item("IsSLD", "Symmetric logarithmic derivatives", "A Hermitian matrix L is a symmetric logarithmic derivative when i(rho H-H rho)=(L rho+rho L)/2."),
            Item("fisherSLD", "Fisher information", "The normalization is one quarter of the real part of trace(rho L L). The spectral formula establishes independence from the chosen Hermitian solution."),
            Item("skewWY", "Skew information", "Skew information is minus one half the real trace of the square of the commutator between the positive matrix square root and the observable."),
            Item("claim", "Partial trace comparison", "The second-factor partial trace is the sum of entries with identical second coordinates. The comparison quantifies over all finite dimensions, joint density matrices, Hermitian local observables and Hermitian SLD solutions on both spaces. Fisher discord is Fisher information minus skew information."))));
}
