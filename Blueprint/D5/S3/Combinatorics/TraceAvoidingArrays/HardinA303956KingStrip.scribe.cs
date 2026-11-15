using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA303956KingStripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA303956KingStrip.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/hardin2018a303956");
    private const string NameQuote = "R. H. Hardin, OEIS A303956, NAME: \"Number of n X 3 0..1 arrays with every element unequal to 0, 1, 2 or 5 king-move adjacent elements, with upper left element zero.\"";
    private const string FormulaQuote = "R. H. Hardin, OEIS A303956, FORMULA: \"Empirical: a(n) = a(n-1) +2*a(n-2) +3*a(n-3) +2*a(n-4) -2*a(n-5) -6*a(n-6) -4*a(n-7) for n>8.\"";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal rooted binary king-strip counts satisfy Hardin's seventh-order recurrence.",
        H("Hardin's recurrence for OEIS A303956"),
        Blocks(
            Node("Admissible", "The literal array predicate", AdmissibleFormula(), true, true,
                NameQuote + " A is a labelled function from Fin n × Fin 3 to Fin 2. The root conjunct fixes the first row's first bit to zero. The finite set contains distinct other cells whose two coordinate distances are at most one and whose bits differ. Each count belongs to {0,1,2,5}. All boundaries are clipped to the rectangle, without self-neighbours, wrapping, padding, symmetry quotient or complement division. The coordinate statement adapts Hardin's source under CC BY-SA 4.0, attributed to Hardin and the OEIS Foundation."),
            Node("a", "The original array count", CountFormula(), true, true,
                NameQuote + " The count is the cardinality of the actual array subtype, cast to the integers. It is defined independently of the recurrence and of the transfer matrix. The source concerns positive heights; the vacuous root condition at height zero does not occur in the asserted recurrence."),
            Node("claim", "The empirical assertion", Eq(V("claim"), Par(ClaimFormula())), true, true,
                FormulaQuote + " All lag indices use natural subtraction. Values and the signed equality lie in the integers. Every natural n greater than eight is quantified; the smallest count argument is at least two."),
            Node("result", "The seventh-order recurrence", ClaimFormula(), false, false,
                "Each row is coded by its three binary entries, with column zero as the least significant bit. An ordered pair of rows is a state. The initial weight checks the zero root and the top row, each transition checks exactly one interior row, and the terminal weight checks the bottom row. Coding and reconstruction give inverse correspondences at every height k+2, so the array count is v T^k t, including k=0. For the polynomial with ascending coefficients (4,6,2,-2,-3,-2,-1,1), its initial row-vector residual r has rt=0, rTt=0 and rT²=0. These identities for the actual local predicate imply vanishing after every power: the first two cases use the scalar identities and every later case uses rT²=0. Expanding gives exactly Hardin's formula. Minimal order, threshold sharpness and other widths require separate arguments."))));

    private static DocumentBlock Node(string name, string title, Formula formula, bool definition,
        bool literature, string prose) => Describe.Lean(
            DescribeId.Create("hardina303956-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hardin-a303956"), ResolutionKind.Proved) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Lam(string name, Formula type, Formula body) => Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Cells() => Seq(Fin(V("n")), Sp, Times, Sp, Fin(D(3)));
    private static Formula Arrays() => Seq(Par(Cells()), Sp, To, Sp, Fin(D(2)));
    private static Formula Val(Formula p, byte i) => App(Q("Fin", "val"), Seq(p, Dot, D(i)));
    private static Formula AdmissibleFormula()
    {
        var p = V("p"); var q = V("q"); var a = V("A");
        var root = All("i", Fin(V("n")), Imp(Eq(App(Q("Fin", "val"), V("i")), D(0)),
            Eq(App(a, Par(Seq(V("i"), Comma, D(0)))), D(0))));
        var near = And(Rel(q, FormulaRelationOperator.NotEqual, p),
            And(Rel(Val(q, 1), FormulaRelationOperator.LessThanOrEqual, Add(Val(p, 1), D(1))),
            And(Rel(Val(p, 1), FormulaRelationOperator.LessThanOrEqual, Add(Val(q, 1), D(1))),
            And(Rel(Val(q, 2), FormulaRelationOperator.LessThanOrEqual, Add(Val(p, 2), D(1))),
            And(Rel(Val(p, 2), FormulaRelationOperator.LessThanOrEqual, Add(Val(q, 2), D(1))),
                Rel(App(a, q), FormulaRelationOperator.NotEqual, App(a, p)))))));
        var neighbours = App(Q("Finset", "filter"), Par(Lam("q", Cells(), near)), Q("Finset", "univ"));
        var allowed = Seq(OpenBrace, D(0), Comma, D(1), Comma, D(2), Comma, D(5), CloseBrace);
        var local = All("p", Cells(), Rel(App(Q("Finset", "card"), neighbours), FormulaRelationOperator.MemberOf, allowed));
        return All("n", V("Nat"), All("A", Arrays(), Eq(Call("Admissible", a), And(root, local))));
    }
    private static Formula CountFormula()
    {
        var subtype = Seq(OpenBrace, V("A"), Colon, Sp, Arrays(), Sp, Bar, Sp, Call("Admissible", V("A")), CloseBrace);
        var count = Par(Seq(App(Q("Nat", "card"), subtype), Colon, Sp, V("Int")));
        return All("n", V("Nat"), Eq(Call("a", V("n")), count));
    }
    private static Formula ClaimFormula()
    {
        Formula Term(byte coefficient, byte lag) => Mul(D(coefficient), Call("a", Par(Sub(V("n"), D(lag)))));
        var rhs = Add(Add(Add(Call("a", Par(Sub(V("n"), D(1)))), Term(2, 2)), Term(3, 3)), Term(2, 4));
        rhs = Sub(Sub(Sub(rhs, Term(2, 5)), Term(6, 6)), Term(4, 7));
        return All("n", V("Nat"), Imp(Rel(D(8), FormulaRelationOperator.LessThan, V("n")), Eq(Call("a", V("n")), rhs)));
    }
}
