using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class KurkovTriangularColumnSumDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/kurkov2026a396981c1");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every lawful A396981 array satisfies Kurkov's positive-column factorial sum.",
        H("Kurkov's Triangular-Block Column Sum"),
        Blocks(
            Node("f", "The positive-index block sequence", BlockIndex(),
                "For q>0, f(q) is the unique integer s>=1 satisfying "
                + "floor(s(s-1)/2)<q<=floor(s(s+1)/2), namely OEIS A002024. "
                + "These are natural-number integer quotients (floor division); the "
                + "rational factorial quotients in the result remain ordinary Q-division. "
                + "The implementation takes the least s with 2q<=s(s+1); the private characterization "
                + "proves equivalence with the source inequalities. Its zero value "
                + "only totalizes the Lean function and supplies no extra source assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsArray", "The literal natural-valued array equations", ArrayEquations(),
                "A has type N -> N -> N. Its zeroth row is one at every column, "
                + "its zeroth column is zero at every positive row, and at positive "
                + "n,q it satisfies A(n,q)=A(n,q-f(q))+(n+f(q)-1)A(n-1,q). "
                + "Natural subtraction agrees with ordinary subtraction on these indices. "
                + "These are the only array hypotheses.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Existence and the complete positive-column identity", Result(),
                "There exists A satisfying IsArray, and for every such A, all natural "
                + "n and all k>=1, (A(n,k+f(k)+1):Q) equals the sum over j=0,...,n "
                + "of (A(j,k):Q)*((n+f(k))!:Q)/((f(k)+j)!:Q). "
                + "Factorials are natural factorials cast to Q before ordinary division; "
                + "every denominator is nonzero. The existence witness is constructed by "
                + "well-founded recursion on (n,q). The block inequalities prove "
                + "f(k+f(k)+1)=f(k)+1, so the original array recurrence at the shifted "
                + "column is a first-order row recurrence. Induction on n and the "
                + "factorial successor identity give the inclusive sum, including n=0. "
                + "The prefatory Stirling identity, Conjectures 2–4 and k=0 are outside "
                + "this theorem. Source: Mikhail Kurkov and OEIS Foundation, CC-BY-SA 4.0.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396981-kurkov-conjecture1-positive-column-factorial-sum"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a396981-c1-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula A(Formula n, Formula q) => new Formula.Apply(V("A"), [n, q]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeqTo(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula ArrayType() => Seq(N(), Sp, To, Sp, N(), Sp, To, Sp, N());
    private static Formula CastQ(Formula value) => Par(Seq(value, Colon, Sp, Q()));
    private static Formula Factorial(Formula value) => Seq(Par(value), Bang);
    private static Formula NatDiv(Formula numerator, Formula denominator) =>
        new Formula.Floor(new Formula.Fraction(numerator, denominator));

    private static Formula BlockIndex()
    {
        var q = V("q");
        var s = V("s");
        var least = Seq(Min, Sp, OpenBrace, s, Sp, InMacro, Sp, N(), Sp, Mid, Sp,
            LeqTo(Mul(D(2), q), Mul(s, Add(s, D(1)))), CloseBrace);
        var definition = All("q", N(), Eqn(Call("f", q), least));
        var sourceBlock = And(LeqTo(D(1), s), And(
            Lt(NatDiv(Mul(s, Sub(s, D(1))), D(2)), q),
            LeqTo(q, NatDiv(Mul(s, Add(s, D(1))), D(2)))));
        var characterization = All("q", N(), Imp(Lt(D(0), q), All("s", N(),
            Seq(Par(Eqn(Call("f", q), s)), Sp, Iff, Sp, Par(sourceBlock)))));
        return And(definition, characterization);
    }

    private static Formula ArrayEquations()
    {
        var n = V("n");
        var q = V("q");
        var fq = Call("f", q);
        var row = All("q", N(), Eqn(A(D(0), q), D(1)));
        var column = All("n", N(), Imp(LeqTo(D(1), n), Eqn(A(n, D(0)), D(0))));
        var recurrence = All("n", N(), All("q", N(), Imp(LeqTo(D(1), n),
            Imp(LeqTo(D(1), q), Eqn(A(n, q), Add(A(n, Sub(q, fq)),
                Mul(Sub(Add(n, fq), D(1)), A(Sub(n, D(1)), q))))))));
        return All("A", ArrayType(), Seq(Call("IsArray", V("A")), Sp, Iff, Sp,
            Par(And(row, And(column, recurrence)))));
    }

    private static Formula Result()
    {
        var n = V("n");
        var k = V("k");
        var j = V("j");
        var fk = Call("f", k);
        var summand = new Formula.Fraction(
            Mul(CastQ(A(j, k)), CastQ(Factorial(Add(n, fk)))),
            CastQ(Factorial(Add(fk, j))));
        var sum = Seq(new Formula.Subscript(Sum, Eqn(j, D(0))),
            Caret, Grp(n), Sp, Par(summand));
        var identity = Eqn(CastQ(A(n, Add(Add(k, fk), D(1)))), sum);
        var existence = Some("A", ArrayType(), Call("IsArray", V("A")));
        var universal = All("A", ArrayType(), Imp(Call("IsArray", V("A")),
            All("n", N(), All("k", N(), Imp(LeqTo(D(1), k), identity)))));
        return And(existence, universal);
    }
}
