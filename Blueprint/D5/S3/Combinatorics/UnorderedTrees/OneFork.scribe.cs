using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class OneForkDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/UnorderedTrees/OneFork.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual finite rooted tree whose size exceeds its vertex-height by one has exactly one leaf outside a deepest root path. The leaf attaches to a nonterminal vertex of that path.",
        H("The one-off-path skeleton"),
        Blocks(
            Node("spine", "The original root path", "spine",
                Disp(Call("spine", F.Id("T"), F.Id("v"))),
                "The spine is the finite set of parent iterates of v from step zero through its depth, including v and the root. Parent iteration subtracts depth until the root is reached, so these iterates are pairwise distinct on the specified interval. The spine is closed under the parent map and has cardinality depth(v) plus one.",
                DescribeRole.Definition),
            Node("classification", "A unique omitted leaf", "one_off_spine",
                ClassificationFormula(false),
                "For every finite vertex type and actual rooted parent tree T, assume card(V) = height(T) + 1. There exist vertices v and w such that v has maximal depth; w is outside the spine of v; and a vertex x is outside that spine if and only if x = w. The vertex w is a leaf, its parent is on the spine, and that parent is different from v. A deepest vertex exists on the nonempty finite carrier. The spine has exactly height(T) vertices, leaving a singleton complement. A child of the omitted vertex would give a second omitted vertex; an omitted parent would have to equal the vertex itself, contradicting the depth law. Attachment at v would exceed the maximal depth. This includes attachment at the root and the equal-arm boundary.",
                DescribeRole.Theorem),
            Node("qualifying", "Skeletons of the qualifying actual trees", "qualifying_one_off_spine",
                ClassificationFormula(true),
                "For every finite actual rooted tree T satisfying vertex-height equals internal-vertex count, the root is internal. There is a deepest path in the pruned tree whose complement is exactly one leaf, attached to a different path vertex from the deepest endpoint. The theorem quantifies the retained vertices on the original internal-vertex subtype and proves all the preceding maximal-depth, complement, leaf and parent properties there. It follows by the leaf-pruning height law and the actual-vertex one-off-path theorem. No enumeration of decorations or generating-series identity follows without further proof.",
                DescribeRole.Theorem))));

    private static Formula ClassificationFormula(bool qualifying)
    {
        Formula t = F.Id("T"), v = F.Id("v"), w = F.Id("w"), x = F.Id("x");
        Formula s = qualifying ? Call("prune", t, F.Id("h")) : t;
        Formula path = Call("spine", s, v);
        Formula inPath(Formula y) => Seq(y, Sp, InMacro, Sp, path);
        Formula body = Seq(
            Forall, Sp, x, Comma, Sp,
            new Formula.Relation(Call("depth", s, x), FormulaRelationOperator.LessThanOrEqual,
                Call("depth", s, v)), Sp, Land, Sp,
            Neg, inPath(w), Sp, Land, Sp,
            Open, Forall, Sp, x, Comma, Sp, Neg, inPath(x), Sp, Iff, Sp, x, Eq, w, Close,
            Sp, Land, Sp, Neg, Call("Internal", s, w), Sp, Land, Sp,
            inPath(Call("parent", s, w)), Sp, Land, Sp,
            Call("parent", s, w), Neq, v);
        Formula premise = qualifying
            ? Seq(Call("height", t), Eq, Call("internalCount", t))
            : Seq(Call("card", F.Id("V")), Eq, Call("height", t), Plus, D(1));
        Formula quantifiers = qualifying
            ? Seq(Exists, Sp, F.Id("h"), Colon, Sp,
                Call("Internal", t, Call("root", t)), Comma, Sp,
                Exists, Sp, v, Comma, Sp, w, Colon, Sp, Call("InternalVertices", t), Comma, Sp)
            : Seq(Exists, Sp, v, Comma, Sp, w, Colon, Sp, F.Id("V"), Comma, Sp);
        return Disp(Seq(premise, Sp, To, Sp, quantifiers, body));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("one-fork-" + id),
            DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
