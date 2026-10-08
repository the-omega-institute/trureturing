using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class StationaryHistoryIncidenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual full histories derive unrestricted slot edges, incidence statistics, and degree balances.",
        H("StationaryHistoryIncidence"),
        Blocks(
            Paragraph(Text(
                "Fix P greater than one, arbitrary finite ell and h, a stationary controller C on Q, "
                + "and Initialized C hP ell h. The original physical period is 3P and its digit alphabet "
                + "has three elements. Every original label begins at the same nominal initial state. "
                + "Waits remain positive literal integers, including modular wraps; singleton continuation "
                + "and every control cycle terminating on all initialized inputs remain in scope. "
                + "Only actual read states enter the slot graph. The full nominal carrier Q, including unused "
                + "states, remains the carrier of C and is not replaced by that graph.")),
            Paragraph(Text(
                "Node is the finite type History C hP I of complete indexed read prefixes from "
                + "StationaryReadHistory. A node n has slot row(n)=(readControl(n),color(n)). "
                + "Rows is the image of all nodes; nonroots retains every node with a parent. "
                + "Edges is the image of nonroot nodes under n maps to (row(parent(n)),row(n)). "
                + "Equal slot pairs define one graph edge, while their fibers retain every distinct "
                + "full history. Incoming and outgoing are the edge fibers at their second and first "
                + "endpoints. J sums incoming degree minus one over actual nonroot rows; Xi sums "
                + "edge-fiber cardinality minus one over actual edges. These are derived quantities.")),
            Result("actual_edge_incidence", "actual-edge-incidence", "Actual forest-edge multiplicity",
                Scope(EqF(SumOver("z", At("nonrootRows"),
                    Seq(Card(SetOf("n", At("nonroots"), EqF(At("row", V("n")), V("z")))), Minus, D(1))),
                    Seq(At("J"), Plus, At("Xi")))),
                "The raw_history_surplus supplier is applied to the actual physicalForest and actual row map. "
                + "The counted fiber consists of different full prefixes, not source visits or repeated drawings."),
            Result("outgoing_degree", "outgoing-degree", "At most two distinct outgoing slots",
                Scope(All("n", Hist, LE(Card(At("outgoing", At("row", V("n")))), D(2)))),
                "One actual source row fixes its literal delay and next read target. Exact reuse of the "
                + "digit-translation supplier confines all of its children, across every full history and "
                + "read level, to two absolute target digits. This bound includes pure resolving rows "
                + "containing several unary histories."),
            Paragraph(Text(
                "Binaries is the set of histories with exactly two children. ProductionRows is their "
                + "row image. Binary-row uniqueness makes this image injective. TwoRows consists of "
                + "actual rows having two distinct outgoing graph edges; resolvingRows is TwoRows "
                + "minus ProductionRows. Terminal-row uniqueness gives 3P different terminal rows. "
                + "The three roots have no incoming edge and share the first read control. "
                + "Writing N=3(P-1), the graph degree balance gives the following exact counts.")),
            Result("two_outgoing_count", "two-outgoing-count", "Production and pure resolving counts",
                Scope(And(EqF(Card(At("twoRows")), Seq(NBinary, Plus, At("J"))),
                    EqF(Card(At("productionRows")), NBinary),
                    EqF(Card(At("resolvingRows")), At("J")))),
                "The incoming balance is |edges|+3=|rows|+J. The outgoing balance is "
                + "|edges|+3P=|rows|+|TwoRows|. Their difference forces |TwoRows|=N+J; "
                + "subtracting N production rows leaves exactly J pure resolving rows."),
            Paragraph(Text(
                "An actual row representative is a selected full history on that row. Target(z) and "
                + "literal(z) are its next target and literal wait, independent of the representative "
                + "on a continuing row. Targets is the set of actual nonfirst read controls. G is the "
                + "target image of TwoRows. For each q, twoAt(q) is the two-row fiber at q, targetSlots(q) "
                + "is its nonroot digit-slot fiber, and targetJ(q) sums the incoming surpluses of those slots.")),
            Result("target_incidence", "target-incidence", "Distinct two-row incidence at a target",
                Scope(All("q", V("Q"), And(
                    LE(Seq(D(2), Times, Card(At("twoAt", V("q")))), Seq(D(3), Plus, At("targetJ", V("q")))),
                    LE(Seq(Card(At("twoAt", V("q"))), Minus, D(1)), At("targetJ", V("q")))))),
                "t different two-outgoing rows give 2t different incoming edges at their common target. "
                + "At most three digit slots subtract at most three first incidences. Nonnegative "
                + "surplus gives t-1<=targetJ(q), including t=0 and t=1. Summing these bounds "
                + "and the actual J balance proves |G|>=N without degree or collision restrictions."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Hist => At("History");
    private static Formula NBinary => Seq(D(3), Times, Grp(Seq(V("P"), Minus, D(1))));
    private static Formula At(string name, params Formula[] args) =>
        Call(name, [V("C"), V("hP"), V("I"), .. args]);
    private static Formula Card(Formula set) => Call("card", set);
    private static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula LE(Formula a, Formula b) => Seq(a, Le, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, type, Comma, Grp(body));
    private static Formula SetOf(string name, Formula set, Formula condition) =>
        Seq(OpenBrace, V(name), InMacro, Sp, set, Mid, Grp(condition), CloseBrace);
    private static Formula SumOver(string name, Formula set, Formula summand) =>
        Seq(Sum, Underscore, Grp(Member(V(name), set)), Grp(summand));
    private static Formula And(params Formula[] terms) =>
        Seq([.. terms.SelectMany((t, i) => i == 0 ? new[] { Grp(t) } : new[] { Land, Grp(t) })]);
    private static Formula Instances(Formula body, params Formula[] types) =>
        Seq([.. types.Select(t => Seq(OpenBracket, t, CloseBracket)), body]);
    private static Formula Scope(Formula body) => All("P", Nat, All("Q", Seq(V("Type"), Underscore, Grp(V("u"))),
        Instances(All("C", Call("Controller", V("P"), V("Q")),
        All("hP", Seq(D(1), Lt, V("P")), All("ell", Nat, All("h", Nat,
        All("I", Call("Initialized", V("C"), V("hP"), V("ell"), V("h")), body))))),
        Call("DecidableEq", V("Q")), Call("NeZero", Seq(D(3), Times, Sp, V("P"))))));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static DocumentBlock ResultAt(string owner, string declaration, string id, string title,
        Formula statement, string explanation) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/" + owner + "." + declaration),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static DocumentBlock Result(string declaration, string id, string title,
        Formula statement, string explanation) => ResultAt("StationaryHistoryIncidence", declaration, id, title, statement, explanation);
}
