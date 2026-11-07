using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceArrays;

internal sealed class HardinA185858Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceArrays/HardinA185858.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hardinbarker2018a185858");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The number of binary arrays with three columns whose adjacent contiguous three-by-three blocks have different traces, divided by 128, has the generating function and radical expression proposed by Colin Barker for OEIS A185858.",
        H("Hardin–Barker A185858"),
        Blocks(
            Node("trace", "Trace of a contiguous block", BlockTraceFormula(),
                "OEIS A185858, NAME (unpaginated): “1/128 the number of (n+2) X 3 binary arrays with no 3 X 3 subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.” Entries lie in Fin 2 and are read by val as natural numbers. The contiguous block starts at row i. Its row index val i + val r lies below n + 2; the Fin constructor carries this bound.",
                "blockTrace", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("valid", "Adjacent traces differ", ValidFormula(),
                "OEIS A185858, NAME (unpaginated): “1/128 the number of (n+2) X 3 binary arrays with no 3 X 3 subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.” There is one block column. Thus only block origins in successive rows are adjacent. Arrays are actual matrices with no identification by symmetry and no periodic boundary.",
                "Valid", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "Number of arrays", CountFormula(),
                "OEIS A185858, NAME (unpaginated): “1/128 the number of (n+2) X 3 binary arrays with no 3 X 3 subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.” Nat.card counts the subtype of matrices satisfying the adjacent-trace inequalities.",
                "count", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "Normalized count", AFormula(),
                "OEIS A185858, NAME (unpaginated): “1/128 the number of (n+2) X 3 binary arrays with no 3 X 3 subblock trace equal to any horizontal or vertical neighbor 3 X 3 subblock trace.” The division takes place in the rationals. The entry has offset 1 and begins 4, 22, 124, 694, 3892.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("series", "Series with zero constant coefficient", SeriesFormula(),
                "OEIS A185858, FORMULA (unpaginated): “G.f.: 2*x*(2 + 3*x) / (1 - 4*x - 9*x^2).” The offset is 1: the coefficient of degree zero is zero, and the coefficient at every positive index n is a n. No value for the source sequence at index zero is asserted.",
                "generatingSeries", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Barker's two formulas", Disp(Iff(F.Id("claim"), ClaimBody())),
                "OEIS A185858, FORMULA (unpaginated): “Conjectures from _Colin Barker_, Apr 17 2018: (Start)” followed by “G.f.: 2*x*(2 + 3*x) / (1 - 4*x - 9*x^2).” and “a(n) = ((2 - sqrt(13))^n*(-4+sqrt(13)) + (2+sqrt(13))^n*(4+sqrt(13))) / (3*sqrt(13)).” The generating function is an identity in PowerSeries ℚ. The second formula holds for natural n at least 1, with a n cast from ℚ to ℝ and sqrt the nonnegative real square root.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of both formulas", Disp(ClaimBody()),
                "A cyclic shift in each column separates the n diagonal triples from six free binary cells. A prescribed trace word s therefore has 64 times the product of choose(3, val(s i)) arrays. The triple sums 0, 1, 2, 3 have multiplicities 1, 3, 3, 1. Splitting a word at its first triple gives four extension equations. Their weighted total satisfies the recurrence with coefficients 4 and 9, and its normalized first two terms are 4 and 22. Coefficient comparison proves the series identity. The two real numbers 2 − sqrt(13) and 2 + sqrt(13) satisfy r² = 4r + 9, so the radical expression has the same recurrence and initial values. Uniqueness of solutions to a linear recurrence proves the second formula for every positive index.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hardin185858-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula QCall(string owner, string name, params Formula[] arguments) =>
        App(Qualified(owner, name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RatType() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinType(Formula size) => Call("Fin", size);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Times(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula ArrayType(Formula n) => Call("Matrix", FinType(Add(n, D(2))), FinType(D(3)), FinType(D(2)));

    private static Formula BlockTraceFormula()
    {
        Formula n = F.Id("n"), b = F.Id("B"), i = F.Id("i"), r = F.Id("r"), c = F.Id("c");
        Formula index = Add(Val(i), Val(r));
        Formula row = Lambda("r", FinType(D(3)),
            Seq(Langle, index, Comma, Sp, Less(index, Add(n, D(2))), Rangle));
        Formula entries = Lambda("r", FinType(Add(n, D(2))),
            Lambda("c", FinType(D(3)), Val(App(b, r, c))));
        Formula trace = QCall("Matrix", "trace", QCall("Matrix", "submatrix", entries, row, Named("id")));
        return Disp(All("n", NatType(), All("B", ArrayType(n), All("i", FinType(n),
            Equal(Call("blockTrace", n, b, i), trace)))));
    }

    private static Formula ValidFormula()
    {
        Formula n = F.Id("n"), b = F.Id("B"), i = F.Id("i"), j = F.Id("j");
        return Disp(All("n", NatType(), All("B", ArrayType(n),
            Iff(Call("Valid", n, b), All("i", FinType(n), All("j", FinType(n),
                Implies(Equal(Val(j), Add(Val(i), D(1))),
                    NotEqual(Call("blockTrace", n, b, i), Call("blockTrace", n, b, j)))))))));
    }

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), b = F.Id("B");
        Formula subtype = Seq(OpenBrace, b, Colon, ArrayType(n), Sp, Mid, Sp,
            Call("Valid", n, b), CloseBrace);
        return Disp(All("n", NatType(), Equal(Call("count", n), QCall("Nat", "card", subtype))));
    }

    private static Formula AFormula()
    {
        Formula n = F.Id("n");
        return Disp(All("n", NatType(), Equal(Call("a", n),
            new Formula.Fraction(Typed(QCall("Nat", "cast", Call("count", n)), RatType()), D(1, 2, 8)))));
    }

    private static Formula SeriesFormula()
    {
        Formula n = F.Id("n");
        Formula body = Seq(Named("if"), Sp, Equal(n, D(0)), Sp, Named("then"), Sp,
            D(0), Sp, Named("else"), Sp, Call("a", n));
        return Disp(Equal(F.Id("generatingSeries"), QCall("PowerSeries", "mk", Lambda("n", NatType(), body))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), x = Qualified("PowerSeries", "X");
        Formula numerator = Times(Times(D(2), x), Parenthesized(Add(D(2), Times(D(3), x))));
        Formula denominator = Subtract(Subtract(D(1), Times(D(4), x)), Times(D(9), new Formula.Power(x, D(2))));
        Formula series = Equal(F.Id("generatingSeries"),
            Times(Parenthesized(numerator), new Formula.Power(Parenthesized(denominator), new Formula.Negate(D(1)))));
        Formula root = QCall("Real", "sqrt", D(1, 3));
        Formula minus = Times(new Formula.Power(Parenthesized(Subtract(D(2), root)), n),
            Parenthesized(Add(new Formula.Negate(D(4)), root)));
        Formula plus = Times(new Formula.Power(Parenthesized(Add(D(2), root)), n), Parenthesized(Add(D(4), root)));
        Formula radical = new Formula.Fraction(Add(minus, plus), Times(D(3), root));
        Formula closed = All("n", NatType(), Implies(AtMost(D(1), n),
            Equal(Typed(QCall("Rat", "cast", Call("a", n)), RealType()), radical)));
        return And(Parenthesized(series), Parenthesized(closed));
    }
}
