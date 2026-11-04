using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class OudraA248186CubicFloorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/OudraA248186CubicFloor.";
    private const string NameSentence = "Least k such that 1/18 - Sum_{h=1..k} 1/(h*(h+1)*(h+2)*(h+3)) < 1/n^3.";
    private const string FormulaSentence = "Conjecture: a(n) = floor(r*n + r^2/n - 1), where r = 3^(-1/3), for n > 2. - _Ridouane Oudra_, Oct 06 2023";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/oudra2023a248186");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Oudra's cubic floor formula for the least reciprocal-product threshold index.",
        H("Oudra's formula for A248186"),
        Blocks(
            Node("residual", "The finite-sum residual", Disp(All("k", Nat(),
                Equal(Call("residual", F.Id("k")), ResidualBody(F.Id("k"))))),
                "OEIS A248186 revision 18, NAME (%N; unpaginated): " + NameSentence
                    + " The sum runs over natural h from 1 through k, including both endpoints; "
                    + "all summands and the subtraction are real-valued. At k=0 the sum is empty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("r", "The real cubic-root constant", Disp(Equal(F.Id("r"),
                new Formula.Power(Cast(D(3), Real()), Div(Seq(Minus, Cast(D(1), Real())), D(3))))),
                "OEIS A248186 revision 18, FORMULA (%F; unpaginated): " + FormulaSentence
                    + " The fixed positive base 3 is raised to the real exponent -1/3.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSequence", "The least positive threshold sequence", Disp(All("A", SequenceType(),
                Iff(Call("IsSourceSequence", F.Id("A")), SourceBody(F.Id("A"))))),
                "OEIS A248186 revision 18, NAME (%N; unpaginated): " + NameSentence
                    + " The source program searches Range[z], hence positive k. The offset is 1,5; "
                    + "n ranges over positive natural numbers, and A(0) is unconstrained. "
                    + "IsLeast requires both membership and minimality; the comparison is strict. "
                    + "The initial values are a(1)=a(2)=1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The source assertion with sequence existence", Disp(Iff(F.Id("claim"), ClaimBody())),
                "OEIS A248186 revision 18, FORMULA (%F; unpaginated): " + FormulaSentence
                    + " A is natural-valued. Its term is cast into the integers before comparison "
                    + "with Int.floor; n is cast into the reals in the formula. Existence is asserted "
                    + "for all positive n, and the formula is asserted for every such sequence at n>2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Oudra's formula holds", Disp(ClaimBody()),
                "Finite telescoping gives residual(k)=1/(3*(k+1)*(k+2)*(k+3)). "
                    + "Writing x=r*n and b=x+r^2/n, the identity r^3=1/3 gives "
                    + "3*(b^3-b)=n^3+1/(3*n^3). For n>2 this lies strictly between n^3 "
                    + "and n^3+1. The polynomial 3*(y^3-y) is strictly increasing for y>=1. "
                    + "Its value at the integer floor of b is an integer, so it is at most n^3; "
                    + "its value at floor(b)+1 exceeds n^3. These bounds identify floor(b)-1 "
                    + "as the least positive admissible index. Translation of the floor by the integer "
                    + "one yields the displayed expression. For n=1 and n=2 the least index is one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oudra-a248186-cubic-floor"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("oudra-a248186-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ResidualBody(Formula k)
    {
        var h = F.Id("h");
        var hr = Cast(h, Real());
        var denominator = Mul(Mul(Mul(hr, Parenthesized(Add(hr, D(1)))),
            Parenthesized(Add(hr, D(2)))), Parenthesized(Add(hr, D(3))));
        var interval = new Formula.Apply(Qualified("Finset", "Icc"), [D(1), k]);
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(h, Sp, InMacro, Sp, interval)),
            Sp, Div(D(1), denominator));
        return Sub(Div(D(1), D(1, 8)), sum);
    }

    private static Formula SourceBody(Formula a)
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var candidates = Seq(OpenBrace, k, Sp, Colon, Sp, Nat(), Sp, Mid, Sp,
            And(Le(D(1), k), Lt(Call("residual", k), Div(D(1), Pow(Cast(n, Real()), 3)))), CloseBrace);
        return All("n", Nat(), Implies(Le(D(1), n), Call("IsLeast", candidates, new Formula.Apply(a, [n]))));
    }

    private static Formula ClaimBody()
    {
        var a = F.Id("A");
        var n = F.Id("n");
        var nr = Cast(n, Real());
        var expression = Sub(Add(Mul(F.Id("r"), nr), Div(Pow(F.Id("r"), 2), nr)), D(1));
        var equality = Equal(Cast(new Formula.Apply(a, [n]), Ints()), Seq(Lfloor, Sp, expression, Sp, Rfloor));
        return And(new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("A"),
                SequenceType(), Call("IsSourceSequence", a)),
            All("A", SequenceType(), Implies(Call("IsSourceSequence", a),
                All("n", Nat(), Implies(Lt(D(2), n), equality)))));
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Ints() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula SequenceType() => Parenthesized(Seq(Nat(), Sp, To, Sp, Nat()));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Pow(Formula value, byte exponent) => new Formula.Power(value, D(exponent));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
}
