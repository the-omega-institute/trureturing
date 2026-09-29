using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class WheelHivExtinctionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/WheelHivExtinctionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/espinosagarcia2026hivwheels");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In the Mukwembi model of HIV infection on the wheel W_18 with replacement parameter R = 4, every admissible initial state reaches the all-healthy state by time 25, so 4 belongs to the extinction set of W_18 and Conjecture 1 of Espinosa-Garcia et al., which puts that set equal to {3} together with all R >= 17, is false.",
        H("The extinction set of the wheel W_18 contains 4"),
        Blocks(
            Node("wheel", "The wheel W_n", WheelFormula(),
                "The wheel W_n = K_1 joined with the cycle C_(n-1) on the vertices 0, ..., n - 1: vertex 0 is the hub, adjacent to every other vertex, and the cycle runs through 1, 2, ..., n - 1 and closes from n - 1 back to 1.",
                "wheelAdj", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "Infected neighbours", CountFormula(),
                "d_(t,I)(v), the number of neighbours of v that are infected (state 1) in the state f.",
                "infectedCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("step", "The update rule", StepFormula(),
                "An infected vertex (1) dies (2). A healthy vertex (0) becomes infected when at least one neighbour is infected and stays healthy otherwise. A dead vertex (2) is replaced by an infected one when at least R neighbours are infected and by a healthy one otherwise.",
                "step", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ext", "The extinction set", ExtinctionFormula(),
                "The positive R such that every admissible initial state f0, a map from the vertices to {0, 1} read as the state castSucc composed with f0, reaches the all-healthy state 0 after some number t of steps.",
                "extinctionSet", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", ClaimFormula(),
                "Conjecture 1 of the source: the extinction set of W_n is {3} together with all R >= n - 1 for even n >= 12, and {4} together with all R >= n - 1 for odd n >= 17.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation", Disp(new Formula.Not(F.Id("claim"))),
                "All 2^18 admissible initial states of W_18 are simulated at once. For each vertex, one natural number records in its bit j whether that vertex is infected in the state reached from the j-th initial state, whose vertex v is infected exactly when bit v of j is set, and a second number records the dead vertices. One step of the rules becomes bitwise operations on these numbers; for the dead hub, whether at least 4 of its 17 neighbours are infected is decided bit by bit by counting masks. The proof shows that at every bit the masks after t steps describe the t-th state of the corresponding initial state, and the kernel evaluates the masks after 25 steps to zero. Hence every admissible initial state reaches the all-healthy state by time 25 when R = 4, so 4 lies in the extinction set of W_18, whereas 4 is neither 3 nor at least 17.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("espinosa-garcia-2026-hiv-wheel-extinction-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("hivwheel-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula Val(Formula vertex) => Call("val", vertex);

    private static Formula WheelFormula()
    {
        Formula n = F.Id("n"), u = F.Id("u"), v = F.Id("v");
        Formula cycle = Or(Or(Or(Or(Or(Equal(Val(u), D(0)), Equal(Val(v), D(0))),
            Equal(Add(Val(u), D(1)), Val(v))), Equal(Add(Val(v), D(1)), Val(u))),
            Parenthesized(And(Equal(Val(u), D(1)), Equal(Val(v), Subtract(n, D(1)))))),
            Parenthesized(And(Equal(Val(v), D(1)), Equal(Val(u), Subtract(n, D(1))))));
        return Disp(Iff(Call("wheelAdj", n, u, v), And(NotEqual(u, v), Parenthesized(cycle))));
    }

    private static Formula CountFormula()
    {
        Formula v = F.Id("v"), u = F.Id("u"), f = F.Id("f"), adj = F.Id("adj");
        Formula set = Seq(OpenBrace, u, Colon, new Formula.Apply(adj, [v, u]), Sp, Land, Sp,
            Equal(new Formula.Apply(f, [u]), D(1)), CloseBrace);
        return Disp(Equal(Call("infectedCount", adj, f, v), Call("card", set)));
    }

    private static Formula StepFormula()
    {
        Formula v = F.Id("v"), f = F.Id("f"), adj = F.Id("adj"), r = F.Id("R");
        Formula fv = new Formula.Apply(f, [v]);
        Formula d = Call("infectedCount", adj, f, v);
        Formula value = IfThenElse(Equal(fv, D(1)), D(2),
            Parenthesized(IfThenElse(Equal(fv, D(0)), Parenthesized(IfThenElse(Equal(d, D(0)), D(0), D(1))),
                Parenthesized(IfThenElse(AtMost(r, d), D(1), D(0))))));
        return Disp(Equal(new Formula.Apply(Call("step", adj, r, f), [v]), value));
    }

    private static Formula ExtinctionFormula()
    {
        Formula n = F.Id("n"), adj = F.Id("adj"), r = F.Id("R"), t = F.Id("t");
        Formula initial = new Formula.TypeArrow(Call("Fin", n), Call("Fin", D(2)));
        Formula body = And(Less(D(0), r), All("f0", initial, Ex("t", Naturals(),
            Equal(new Formula.Apply(new Formula.Power(Call("step", adj, r), t), [Seq(Named("castSucc"), Sp, Circ, Sp, F.Id("f0"))]), D(0)))));
        return Disp(Iff(Seq(r, Sp, InMacro, Sp, Call("extinctionSet", n, adj)), body));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), r = F.Id("R");
        Formula even = All("n", Naturals(), Implies(And(Call("Even", n), AtMost(D(1, 2), n)),
            Equal(Call("extinctionSet", n, Call("wheelAdj", n)),
                Seq(OpenBrace, D(3), CloseBrace, Sp, Cup, Sp, OpenBrace, r, Colon, AtMost(Subtract(n, D(1)), r), CloseBrace))));
        Formula odd = All("n", Naturals(), Implies(And(Call("Odd", n), AtMost(D(1, 7), n)),
            Equal(Call("extinctionSet", n, Call("wheelAdj", n)),
                Seq(OpenBrace, D(4), CloseBrace, Sp, Cup, Sp, OpenBrace, r, Colon, AtMost(Subtract(n, D(1)), r), CloseBrace))));
        return Disp(Iff(F.Id("claim"), And(Parenthesized(even), Parenthesized(odd))));
    }
}
