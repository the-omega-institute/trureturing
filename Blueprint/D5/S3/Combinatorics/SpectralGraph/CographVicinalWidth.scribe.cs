using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class CographVicinalWidthDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/mandalmanna2026distance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vicinal width under component cuts.",
        H("Vicinal width under component cuts"),
        Blocks(
            Entry("vicinal_compl_iff", "Reversing vicinal order",
                "Complementation exchanges the two vertices in the vicinal comparison."),
            Entry("hasChainCover_compl_iff", "Chain covers of complements",
                "The same assignment to chain labels works for a graph and its complement."),
            Entry("dilworthNumber_compl", "Complement invariance",
                "Complementation preserves the infimum of feasible chain-cover sizes."),
            Entry("width", "Natural width",
                "On finite graphs choose the least feasible vicinal chain-cover size.", DescribeRole.Definition),
            Entry("dilworthNumber_eq_width", "Agreement of the two widths",
                "The least natural size equals the extended-natural infimum after casting."),
            Entry("width_compl", "Natural width under complement",
                "A graph and its complement have the same natural width."),
            Entry("width_singleton", "Singleton width",
                "The unique vertex requires and supplies one chain."),
            Entry("width_components", "Width of a component cut",
                "Take the maximum of one and the sum of the widths of the nonsingleton components. Isolates can be placed in an existing chain."))));

    private static DocumentBlock Entry(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("cographvicinalwidth-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
