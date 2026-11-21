using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class NormalizedCographCotreeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mannamandaltura2026cographdistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized cotrees on native graph vertices.",
        H("Normalized cotrees on native graph vertices"),
        Blocks(
            Entry("cutGraph", "Graph to cut",
                "A union splits by graph components and a join splits by complement components.", DescribeRole.Definition),
            Entry("Cotree", "Normalized cotree",
                "Leaves have singleton carriers. Internal nodes use native induced component graphs and alternate the union and join labels.", DescribeRole.Definition),
            Entry("rootKind", "Root label",
                "The label distinguishes a singleton, a union and a join.", DescribeRole.Definition),
            Entry("not_connected_compl_of_not_induced_pathFour", "Complement components",
                "The complement of a finite connected nontrivial cograph is disconnected."),
            Entry("exists_cotree", "Existence of a normalized cotree",
                "Recurse on the strict decrease in carrier cardinality along graph and complement component cuts."),
            Entry("adj_iff_join_of_component_ne", "Cross edges",
                "Distinct components of the cut are completely adjacent at a join and completely nonadjacent at a union."),
            Entry("nontrivial_iff", "Internal support",
                "A subtree has a nontrivial carrier exactly when it has an internal root."),
            Entry("universal_iff_leaf_child", "Universal vertices",
                "At a join, the universal vertices are precisely those in leaf children."),
            Entry("exists_join_root", "Join root",
                "A nontrivial connected cograph has a normalized cotree with join at its root."),
            Entry("width_leaf", "Leaf width",
                "Each singleton subtree has width one."),
            Entry("width_node", "Width at an internal node",
                "Take the maximum of one and the sum of the widths of the nonleaf children."))));

    private static DocumentBlock Entry(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("normalizedcographcotree-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
