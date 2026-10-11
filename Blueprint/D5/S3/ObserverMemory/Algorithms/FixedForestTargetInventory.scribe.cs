using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class FixedForestTargetInventoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete physical forest supplies the canonical target inventory and original same-digit assignments.",
        H("Physical histories and target inventory"),
        Blocks(
            Paragraph(Text(
                "PhysicalForest retains every original label and indexed read event, its unique forest parent, "
                + "absolute digit, cumulative literal wait, original leaf output and exact phase interval. "
                + "The three roots use the digit of x+ell; each path has a positive finite read count at most h. "
                + "All child waits are positive literal integers. Singleton continuations are retained. "
                + "History levels order the forest; they impose no order on read-control states.")),
            Paragraph(Text(
                "Prescribed retains the marked physical source nodes A,B,H,K,H1,K1, their roles, "
                + "disjoint physical supports, equal literal requests and original child digits. "
                + "A represents the merged A/B binary target. Z and Fin e extras are separate tags. "
                + "H may equal A or B, so its target may be Q. Z remains outside all binary targets.")),
            Paragraph(Text(
                "Compatible checks only the forced source rows: equal rows may contain the same node, "
                + "H/K, or H1/K1. It mentions no controller, execution, alpha, resource injection or capacity. "
                + "The operational owner derives this check from OriginalImplementation and proves the incompatible branch empty.")),
            Paragraph(Text(
                "Ordinary demands are exactly unary nodes excluding K,H1,K1. Assignment injects them into "
                + "unoccupied absolute-digit slots, preserves each child's digit and hits every extra target. "
                + "A baseline is the maximum binary-parent literal request, the resolving request at Z, "
                + "or one for an extra. L is the joint maximum of that baseline and every assigned demand. "
                + "All three spare digits of one extra therefore share one maximum.")),
            Result("leaf_count", "leaf-count", "Exactly the original fixed-label leaves",
                ForestScope(EqF(Call("card", Call("completeLeaves", V("F"))),
                    Seq(D(3), V("P")))),
                "Choose an original label in a leaf support. Its event must be final, since a "
                + "further event would supply a child. Conversely every label's last event is a leaf "
                + "and has that fixed output. This gives a leaf-label equivalence and exactly 3P leaves. "
                + "The root colors give exactly three distinct roots. Singleton continuation nodes remain internal."),
            Result("placement_fibers", "placement-fibers", "No additional history collision",
                Assigned(All("n", V("Node"), All("m", V("Node"), Imp(
                    EqF(Call("placement", V("F"), V("R"), V("alpha"), V("n")),
                        Call("placement", V("F"), V("R"), V("alpha"), V("m"))),
                    Call("Shared", V("F"), V("R"), V("n"), V("m")))))),
                "Forced rows use source incidence; ordinary rows use same-digit spare slots. "
                + "A spare row cannot meet a forced row, and injectivity prevents ordinary demands from sharing a row."),
            Result("request_bound", "request-bound", "Every literal source request fits its joint target tail",
                AssignmentScope(All("n", V("Node"), Imp(Call("Internal", V("F"), V("n")),
                    LE(Call("delay", V("F"), V("n")),
                        Call("L", V("F"), V("R"), V("alpha"),
                            Call("nextTarget", V("F"), V("R"), V("alpha"), V("n"))))))),
                "Binary requests are included in the baseline. K shares H's literal request. "
                + "H1/K1 share the resolving request. Every remaining unary request is included through alpha."),
            Result("occupied_counts", "occupied-counts", "The canonical 3/2/2/0 inventory",
                Scope(All("q", Call("Target", V("F"), V("R"), V("e")),
                    EqF(Call("card", Call("occupied", V("F"), V("R"), V("q"))),
                        Call("occupiedDigitCount", V("R"), V("q"))))),
                "The A/B representative Q occupies three digits, every other binary target two, "
                + "Z two and every extra zero before assignment. The count follows from the "
                + "original parent and child-digit incidence, including the absorbed K arrival."))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
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
    private static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula LE(Formula a, Formula b) => Seq(a, Le, b);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, type, Comma, Grp(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula AllN(string[] names, Formula body) =>
        names.Reverse().Aggregate(body, (b, n) => All(n, N, b));
    private static Formula Instances(Formula body, params Formula[] types) =>
        Seq([.. types.Select(t => Seq(OpenBracket, t, CloseBracket)), body]);
    private static Formula ForestScope(Formula body) => AllN(["P", "h", "ell"],
        All("Node", V("Type"), Instances(All("hP", Seq(D(1), Lt, V("P")),
            All("F", Call("PhysicalForest", V("P"), V("h"), V("ell"), V("Node"), V("hP")), body)),
            Call("Fintype", V("Node")), Call("DecidableEq", V("Node")))));
    private static Formula Scope(Formula body) => AllN(["P", "h", "ell", "e"],
        All("Node", V("Type"), Instances(All("hP", Seq(D(1), Lt, V("P")),
            All("F", Call("PhysicalForest", V("P"), V("h"), V("ell"), V("Node"), V("hP")),
                All("R", Call("Prescribed", V("F")), body))),
            Call("Fintype", V("Node")), Call("DecidableEq", V("Node")))));
    private static Formula AssignmentScope(Formula body) => Scope(
        All("alpha", Call("Assignment", V("F"), V("R"), V("e")), body));
    private static Formula Assigned(Formula body) => Scope(
        All("alpha", Call("Assignment", V("F"), V("R"), V("e")),
            Imp(Call("Compatible", V("F"), V("R"), V("e")), body)));
    private static DocumentBlock Result(string declaration, string id, string heading,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory." + declaration),
            H(heading), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
