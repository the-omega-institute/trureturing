using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class UniversalRootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/UniversalRoot.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimal forts and a universal root.",
        H("Minimal forts and a universal root"),
        Blocks(
            Node("minimality", "Inclusion-minimal fort", "MinimalFort", "A set is a nonempty fort in the existing generic graph predicate, and every subset that is a fort contains the entire set. The empty subset is among the quantified subsets but is not a fort.", DescribeRole.Definition),
            Node("all-forts", "All minimal forts", "minimalForts", "The finite family ranges over every finite vertex subset and retains exactly those satisfying inclusion minimality. There is no orbit quotient or chosen subclass.", DescribeRole.Definition),
            Node("graph", "The universal-root graph", "cone", "The vertex type is Option V. None is the added root. It is adjacent to every Some v; edges between Some v and Some w are exactly the base graph edges. The root has no loop.", DescribeRole.Definition),
            Node("root-free-set", "Root-free vertex subsets", "lift", "The injective map Some embeds a base subset without the root.", DescribeRole.Definition),
            Node("root-set", "Root-containing subsets", "rootSet", "The subset consists of the universal root and exactly the embedded vertices of the base subset.", DescribeRole.Definition),
            Node("base-set", "Recovering base vertices", "baseSet", "The recovered base subset consists exactly of vertices v whose Some v belongs to the given cone subset.", DescribeRole.Definition),
            Node("root-free-fort", "Root-free forthood", "isFort_lift_iff", "For every finite simple base graph and every base subset, the embedded subset is a fort exactly when it is a base fort and its cardinality differs from one. The extra condition is imposed by the unselected universal root.", DescribeRole.Theorem),
            Node("root-fort", "Root-containing forthood", "isFort_rootSet_iff", "For every finite simple base graph, adjoining the selected root gives a fort exactly when the base subset is closed dominating. Each unselected base vertex already has the selected root as one neighbor and needs a selected base neighbor.", DescribeRole.Theorem),
            Node("non-singleton", "No singleton fort without isolated vertices", "fort_card_ne_one", "If every base vertex has a neighbor, a base fort cannot have cardinality one. A neighbor of the sole selected vertex would otherwise have exactly one selected neighbor.", DescribeRole.Theorem),
            Node("connected", "Connectivity of the actual graph", "cone_connected", "For any finite base graph, including an empty or disconnected one, the cone is connected: the root reaches itself and is adjacent to every other vertex.", DescribeRole.Theorem),
            Node("root-free-minimal", "All root-free minimal forts", "minimalFort_lift_iff", "If the finite base graph has no isolated vertices, embedding a subset gives a minimal fort exactly when that subset is a minimal fort of the base. Every cone subset without the root is recovered from its base vertices, so both minimality directions quantify over every subset.", DescribeRole.Theorem),
            Node("root-minimal", "All root-containing minimal forts", "minimalFort_rootSet_iff", "For every finite base graph without isolated vertices and every base subset S, the subset consisting of the root and S is a minimal fort exactly when S is inclusion-minimal closed dominating and no subset of S is a nonempty base fort. Proper subsets retaining the root test minimal domination; subsets losing the root test the exclusion of base forts.", DescribeRole.Theorem),
            Node("rootedchoices", "All rooted minimal-fort choices", "rootedChoices", "For any finite decidable simple graph, this family filters every base vertex subset S by whether the universal root together with S is an actual inclusion-minimal nonempty fort of the cone. No dominating-set formula is substituted for the fort predicate.", DescribeRole.Definition)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
