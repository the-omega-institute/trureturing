using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.CarryGraph;

internal sealed class CanonicalEmbeddingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CarryGraph/CanonicalEmbedding.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(Formula x, Formula t, Formula f) =>
        Par(Seq(Forall, Sp, x, Colon, Sp, t, Comma, Sp, f));
    private static Formula Ex(Formula x, Formula t, Formula f) =>
        Par(Seq(Exists, Sp, x, Colon, Sp, t, Comma, Sp, f));
    private static Formula And(params Formula[] fs) => Par(Seq(fs.SelectMany((f, i) =>
        i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Leq(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Pair(Formula x, Formula y) => Par(Seq(x, Comma, Sp, y));
    private static Formula SumOver(Formula i, Formula t, Formula f) =>
        Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, t)), f);
    private static Formula Floor(Formula x) => Seq(Lfloor, x, Rfloor);
    private static DocumentBlock Definition(string name, string title, Formula f, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        var m = V("m"); var p = V("p"); var k = V("k"); var d = V("d"); var i = V("i");
        var g = V("gamma"); var s = V("s"); var a = V("a");
        var n = Seq(Mathbb, Grp(V("N"))); var r = Seq(Mathbb, Grp(V("R")));
        var indices = Call("Fin", m); var lawType = Par(Seq(indices, Sp, To, Sp, r));
        var next = Seq(d, Sp, Plus, Sp, D(1));
        Formula N(Formula depth, Formula label) => Floor(Mul(new Formula.Power(D(2), depth), Call("p", label)));
        Formula Bit(Formula label) => Sub(N(next, label), Mul(D(2), N(d, label)));
        Formula Indicator(Formula predicate) => Call("indicator", predicate);
        var equality = Equal(N(d, i), N(d, k));
        var equalityCount = SumOver(i, indices, Indicator(equality));
        var residual = Sub(new Formula.Power(D(2), d), SumOver(i, indices, N(d, i)));
        var departing = Call("if", Equal(Bit(k), D(1)), D(0),
            SumOver(i, indices, Call("if", equality, Bit(i), D(0))));
        var larger = SumOver(i, indices, Call("if", equality, D(0), Bit(i)));
        Formula Parameters(Formula f) => All(m, n, All(p, lawType, All(k, indices, f)));
        var stateDefinition = Parameters(All(d, n,
            Equal(Call("canonicalState", p, k, d), Pair(residual, equalityCount))));
        var actionDefinition = Parameters(All(d, n,
            Equal(Call("canonicalAction", p, k, d), Par(Seq(Bit(k), Comma, Sp, departing, Comma, Sp, larger)))));
        var pathDefinition = Parameters(Equal(Call("canonicalPath", p, k),
            Pair(Par(Seq(d, Sp, Mapsto, Sp, Call("canonicalState", p, k, d))),
                Par(Seq(d, Sp, Mapsto, Sp, Call("canonicalAction", p, k, d))))));
        var positive = All(i, indices, Seq(D(0), Sp, Lt, Sp, Call("p", i)));
        var normalized = Equal(SumOver(i, indices, Call("p", i)), D(1));
        var least = All(i, indices, Leq(Call("p", k), Call("p", i)));
        var floorGroup = Seq(OpenBrace, i, Sp, InMacro, Sp, indices, Mid, equality, CloseBrace);
        var embedding = All(p, lawType, Imp(positive, Imp(normalized,
            Ex(k, indices, And(least, Ex(g, V("Path"), And(Call("IsRootPath", m, g),
                Equal(Call("anchorValue", g), Call("p", k)),
                Equal(Call("anchorValue", g), Call("sInf", Call("range", p))),
                Equal(Call("pathCost", g), Call("cost", p)),
                All(d, n, Equal(Call("r", Call("state", g, d)), residual)),
                All(d, n, Equal(Call("e", Call("state", g, d)), Call("card", floorGroup))))))))));
        var totality = All(s, V("State"), Imp(Call("IsState", m, s),
            Ex(a, V("Action"), Call("Legal", m, s, a))));
        var zeroBoundary = All(s, V("State"), All(a, V("Action"),
            Imp(Call("Legal", m, s, a), Imp(Equal(Call("r", s), D(0)),
                And(Equal(Call("b", a), D(0)), Equal(Call("h", a), D(0)),
                    Equal(Call("c", a), D(0)), Equal(Call("successor", s, a), s))))));
        var oneBoundary = All(s, V("State"), All(a, V("Action"),
            Imp(Call("Legal", m, s, a), Imp(Equal(Call("e", s), D(1)), Equal(Call("h", a), D(0))))));
        var statement = All(m, n, Imp(Leq(D(2), m), And(totality, zeroBoundary, oneBoundary, embedding)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Canonical binary digits embed every positive normalized real law into the original carry graph.",
            H("Canonical Carry Embedding and Boundary Completeness"), Blocks(
                Paragraph(Text("All labels belong to Fin m. The integer prefix at depth d is floor(2^d p(i)); the next digit is the depth-(d+1) prefix minus twice the depth-d prefix. Indicator takes the integer value one when its argument holds and zero otherwise. State, Action, Legal, successor, IsRootPath, anchorValue and pathCost are the original carry-graph objects. The function cost is the dyadic residual tail sum. Natural powers and cardinalities in integer state fields use their canonical integer casts.")),
                Definition("canonicalState", "Floor states", stateDefinition,
                    "The first coordinate is the integer dyadic residual. The second counts the labels with the same floor prefix as label k, including k itself."),
                Definition("canonicalAction", "Canonical digit actions", actionDefinition,
                    "The anchor digit determines the action row. For an anchor zero, h counts the one-digits in the equality group; for an anchor one, h is zero. The coordinate c counts the one-digits outside that group."),
                Definition("canonicalPath", "One common-law path", pathDefinition,
                    "The path consists of the floor state and digit action at each natural depth, both computed from the same real vector and the same anchor label."),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("All real laws and both boundaries"), StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
                    Blocks(Paragraph(Text("For every m at least two, every state has a legal action. At zero residual the only legal action has b=h=c=0 and returns to the same state; all subsequent residual charges vanish. If the equality group has one label then h=0 for every legal action.")),
                        Paragraph(Text("Every strictly positive normalized real vector has a smallest coordinate k. Its canonical path starts at (1,m), preserves that minimum as its anchor value, has exactly the dyadic cost, and retains the displayed floor residual and equality-group size at every depth. The same k and the same path work for all depths.")),
                        Paragraph(Text("A positive prefix difference cannot return to zero after doubling and adding the next digit difference. If the anchor digit is one, every still-equal label also has digit one. If the anchor digit is zero, exactly the still-equal labels with digit one depart. These facts give e(d+1)=e(d)-h(d), while the complete column digit count gives the residual successor. Floor bounds give legal states and action ranges. The canonical binary series recovers the anchor mass; the cost equality follows term by term from the residual identity.")),
                        Paragraph(Text("Terminating binary coordinates, ties for the smallest mass and noncomputable real vectors are included. No rationality, distinctness or effective-computation assumption is imposed. Lumbroso's presentation of Knuth-Yao DDG supplies background for the existing dyadic cost expression; the carry-graph embedding is the present mathematical relation. Existence of the infinite path gives no finite effective algorithm for arbitrary real input."))),
                    DescribeRole.Theorem))));
    }
}
