using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class RunningIntersectionMessagesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ConceptDynamics/Gluing/RunningIntersectionMessages.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive separator messages characterize nonemptiness of the raw join on a finite "
            + "running-intersection tree.",
        H("Running Intersection Messages"),
        Blocks(
            Paragraph(Text(
                "Node is a finite node type and Var is an arbitrary variable type. Value assigns "
                    + "a value type to each variable. S assigns a scope to each node, and Gamma "
                    + "assigns a set of complete assignments on that scope. Assignment, restriction, "
                    + "componentScope and rawJoin are the existing dependent record constructions. "
                    + "The global scope U is componentScope S on all nodes, hence the union of S n.")),
            Describe.Lean(DescribeId.Create("recursive-separator-messages"),
                DeclarationHandle.Create(Module + "separatorMessages"),
                H("Recursive separator messages"),
                StatementSource.FromAuthor(Disp(MessageDefinition())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For e directed from v to its parent p, a message contains the separator "
                        + "restriction of a Gamma v row precisely when that row passes every "
                        + "child message w to v, where w is adjacent to v and differs from p. "
                        + "The message carrier uses S p intersect S v. Swapping the intersection "
                        + "order is only equality transport. Recursion decreases the cardinality "
                        + "of the actual component reachable from v after deleting the edge. "
                        + "Each child component is a strict subset. A chosen root selects the "
                        + "darts pointing toward it; the same recurrence is defined for either "
                        + "orientation of every tree edge. No global join is used to define messages."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("root-acceptance-iff-raw-join"),
                DeclarationHandle.Create(Module + "raw_join_nonempty_iff_root"),
                H("Root acceptance characterizes the raw join"),
                StatementSource.FromAuthor(Disp(RootStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Running intersection means that the occurrence-induced graph of each "
                            + "variable is preconnected. Every occurring variable therefore has "
                            + "connected occurrences; absent variables impose no condition. The "
                            + "root is an actual node. Root acceptance asks for one Gamma r row "
                            + "whose restriction passes every inward message at the root.")),
                    Paragraph(Text(
                        "A single global raw-join record yields every message membership by "
                            + "well-founded induction on the actual deleted-edge components. "
                            + "Conversely, message witnesses propagate local rows along the unique "
                            + "paths from the root. The selected rows agree on every complete edge "
                            + "separator. Their singleton relations are nonempty and have equal "
                            + "complete edge projection images. The existing local-row extension "
                            + "theorem glues this singleton family, and the resulting record "
                            + "belongs to the original local relations.")),
                    Paragraph(Text(
                        "No edge projection consistency is assumed for Gamma. Value types, "
                            + "relations, scopes and separators may be empty or infinite. A one-node "
                            + "tree reduces to nonemptiness of its sole relation. For a fixed k, "
                            + "take Value constant with value O, S n equal to Sigma n and Gamma n "
                            + "equal to R n at that same k. The raw join is then the natural join "
                            + "on the union of those supports. This statement concerns join "
                            + "nonemptiness only; capacity bounds, message counts, separator width "
                            + "and certificate claims require separate results."))),
                DescribeRole.Theorem))));

    private static Formula MessageDefinition()
    {
        var e = F.Id("e");
        var parent = Call("snd", e);
        var node = Call("fst", e);
        var child = F.Id("w");
        var row = F.Id("a");
        var children = All("w", F.Id("Node"), Seq(
            Call("Adj", F.Id("T"), child, node), Sp, Land, Sp,
            NotEqual(child, parent), Sp, To, Sp,
            Member(Restriction(row, node, child),
                Message(Call("dart", F.Id("T"), child, node)))));
        var witness = Ex("a", Call("Assignment", F.Id("Value"), Call("S", node)), Seq(
            Member(row, Call("Gamma", node)), Sp, Land, Sp,
            Equal(Restriction(row, parent, node), F.Id("t")), Sp, Land, Sp, children));
        var messageSet = Seq(OpenBrace, F.Id("t"), Colon, Sp,
            Call("Assignment", F.Id("Value"), Separator(parent, node)), Sp, Vert, Sp,
            witness, CloseBrace);
        return Parameters(Seq(Call("IsTree", F.Id("T")), Sp, To, Sp,
            All("e", Call("Dart", F.Id("T")), Equal(Message(e), messageSet))));
    }

    private static Formula RootStatement()
    {
        var root = F.Id("r");
        var child = F.Id("w");
        var row = F.Id("a");
        var children = All("w", F.Id("Node"), Seq(
            Call("Adj", F.Id("T"), child, root), Sp, To, Sp,
            Member(Restriction(row, root, child), Message(Call("dart", F.Id("T"), child, root)))));
        var acceptance = Ex("a", Call("Assignment", F.Id("Value"), Call("S", root)), Seq(
            Member(row, Call("Gamma", root)), Sp, Land, Sp, children));
        var join = Call("rawJoin", F.Id("Value"), F.Id("S"), F.Id("Gamma"), Call("univ", F.Id("Node")));
        return Parameters(Seq(Call("IsTree", F.Id("T")), Sp, Land, Sp,
            Call("RunningIntersection", F.Id("T"), F.Id("S")), Sp, To, Sp,
            All("r", F.Id("Node"), Seq(Call("Nonempty", join), Sp, Iff, Sp, acceptance))));
    }

    private static Formula Parameters(Formula body) =>
        All("Node", F.Id("Type"), All("Var", F.Id("Type"),
            Seq(OpenBracket, Call("Finite", F.Id("Node")), CloseBracket, Comma, Sp,
                All("T", Call("SimpleGraph", F.Id("Node")),
                    All("Value", Call("Family", F.Id("Var"), F.Id("Type")),
                        All("S", Call("Function", F.Id("Node"), Call("Set", F.Id("Var"))),
                            All("Gamma", Call("RelationFamily", F.Id("Value"), F.Id("S")), body)))))));

    private static Formula All(string variable, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(variable), Colon, Sp, type, Comma, Sp, body);

    private static Formula Ex(string variable, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(variable), Colon, Sp, type, Comma, Sp, body);

    private static Formula Member(Formula element, Formula set) =>
        Seq(element, Sp, InMacro, Sp, set);

    private static Formula Separator(Formula p, Formula q) =>
        Call("intersection", Call("S", p), Call("S", q));

    private static Formula Restriction(Formula row, Formula p, Formula q) =>
        Call("restrict", row, Separator(p, q));

    private static Formula Message(Formula dart) =>
        Call("M", F.Id("T"), F.Id("Value"), F.Id("S"), F.Id("Gamma"), dart);
}
