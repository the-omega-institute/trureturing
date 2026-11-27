using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class LeafPruningDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/LeafPruning.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting all original leaves of a finite rooted tree with an internal root leaves the actual internal-vertex subtree and lowers vertex-height by one.",
        H("Leaf pruning of actual rooted trees"),
        Blocks(
            Node("prune", "The internal-vertex subtree", "prune",
                Disp(Call("prune", F.Id("T"), F.Id("h"))),
                "Assume h says that the root of T has a child. The pruned carrier is precisely the subtype of original internal vertices. Its parent map is the original parent map restricted to this subtype, and its root is the original root. The parent of every nonroot vertex is internal; at the root closure follows from h. Parent iteration commutes with the subtype inclusion, proving that every retained vertex still reaches the root.",
                DescribeRole.Definition),
            Node("qualifying", "The target equality supplies the internal root", "qualifying_root",
                Disp(Seq(Call("height", F.Id("T")), Eq, Call("internalCount", F.Id("T")),
                    Sp, To, Sp, Call("Internal", F.Id("T"), Call("root", F.Id("T"))))),
                "Vertex-height is positive. Thus equality with the internal-vertex count supplies an internal vertex and one of its nonroot children. On the path from that child to the root, the last nonroot vertex is a child of the root. Consequently every tree satisfying the equality can be pruned on a nonempty rooted carrier; the singleton does not create an exceptional qualifying case.",
                DescribeRole.Theorem),
            Node("reduction", "The exact pruning reduction", "pruning_reduction",
                Disp(Seq(Call("height", F.Id("T")), Eq,
                    Call("height", Call("prune", F.Id("T"), F.Id("h"))), Plus, D(1),
                    Sp, Land, Sp, Open,
                    Call("height", F.Id("T")), Eq, Call("internalCount", F.Id("T")),
                    Sp, Iff, Sp,
                    Call("card", Call("Internal", F.Id("T"))), Eq,
                    Call("height", Call("prune", F.Id("T"), F.Id("h"))), Plus, D(1), Close)),
                "For every finite vertex type and every rooted parent tree T whose root is internal, pruning lowers vertex-height by exactly one. Depth is unchanged on retained vertices because all parent iterates agree. Every nonroot original vertex lies one level below an internal parent, giving the upper height bound. Conversely each retained vertex has a child one level below it, giving the reverse bound. The pruned vertex cardinality is the original internal-vertex count, so the equality defining the counting problem becomes size of the pruned tree equals its vertex-height plus one. This is a structural reduction; classifying the remaining shapes and counting their unordered decorations are further mathematical obligations.",
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("leaf-pruning-" + id),
            DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
