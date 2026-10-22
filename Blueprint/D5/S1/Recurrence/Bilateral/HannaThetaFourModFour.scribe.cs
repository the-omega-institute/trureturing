using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Bilateral;

internal sealed class HannaThetaFourModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2026a379764");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A379764 theta-four coefficient conjectures.",
        H("Hanna's theta-four congruences"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A379764 states: \"G.f. A(x) satisfies Sum_{n=-oo..+oo} (4^n*A(x)^n - 4*A(x))^(n+1) = 2*theta_4(x) = 2*Sum_{n=-oo..+oo} (-x)^(n^2).\" The same entry states: \"Conjecture: for n > 0, a(n) is odd iff n is a square.\" It also states: \"Conjecture: for n > 0, a(n) == (-1)^(n-1) (mod 4) iff n is a square, otherwise a(n) is divisible by 4 if n is nonsquare.\"")),
            Paragraph(Text("PowerSeries and LaurentSeries are formal series over the displayed coefficient rings. The bilateral sum is coefficientwise over the finite interval Icc(-(K:Z), K) with N+1 <= K. The coefficient of theta4 is defined by the same finite symmetric window. Int.ModEq is congruence modulo its first argument; divisibility is in Z.")),
            Describe.Lean(DescribeId.Create("a379764-theta4"), DeclarationHandle.Create(Prefix + "theta4"),
                H("The coefficientwise theta-four series"), StatementSource.FromAuthor(Theta4Formula()),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The coefficient at N sums the terms indexed by integer n in the symmetric interval from -(N:Z) to N."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a379764-term"), DeclarationHandle.Create(Prefix + "term"),
                H("The Laurent-series summand"), StatementSource.FromAuthor(TermFormula()),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The integer exponent n is used in LaurentSeries Q after embedding A with HahnSeries.ofPowerSeries."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a379764-isgf"), DeclarationHandle.Create(Prefix + "IsGF"),
                H("The normalized generating-function equation"), StatementSource.FromAuthor(IsGFFormula()),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Normalization is constantCoeff A = 0 and coeff 1 A = 1; every coefficient window with N+1 <= K equals twice the theta-four coefficient."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a379764-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Hanna's two coefficient conjectures"), StatementSource.FromAuthor(ClaimBody()),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("For every normalized solution and every positive n, an integer coefficient witness has the two square biconditionals and the nonsquare divisibility conclusion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a379764-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The two A379764 conjectures"), StatementSource.FromAuthor(ClaimBody()),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The integral fixed-point construction gives a normalized solution. Its coefficient congruence is the theta-four source modulo four, and uniqueness identifies every normalized rational solution with it."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a379764-hanna-theta-mod-four"),
                    ResolutionKind.Proved)))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Divides(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Divides, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(Parenthesized(x), y);
    private static Formula Negative(Formula x) => Seq(Minus, Parenthesized(x));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Not(Formula x) => Seq(FormulaDsl.Neg, Sp, Parenthesized(x));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lambda(string name, Formula type, Formula body) => Parenthesized(Seq(F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula Coeff(Formula n, Formula a) => Call("coeff", n, a);
    private static Formula Constant(Formula a) => Call("constantCoeff", a);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Window(Formula n) => QCall("Finset", "Icc", Negative(Cast(n, Integers())), Cast(n, Integers()));
    private static Formula SumOver(string name, Formula type, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(name), Colon, Sp, type, Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula IfThenElse(Formula p, Formula a, Formula b) => Parenthesized(Seq(Named("if"), Sp, Parenthesized(p), Sp, Named("then"), Sp, a, Sp, Named("else"), Sp, b));
    private static Formula ModEq(Formula modulus, Formula left, Formula right) => QCall("Int", "ModEq", modulus, left, right);

    private static Formula Theta4Formula()
    {
        var n = F.Id("n"); var N = F.Id("N");
        var body = SumOver("n", Integers(), Window(N), IfThenElse(Eqn(Pow(n, D(2)), Cast(N, Integers())), Pow(Negative(D(1)), N), D(0)));
        return Disp(Eqn(Call("theta4"), QCall("PowerSeries", "mk", Lambda("N", Naturals(), body))));
    }

    private static Formula TermFormula()
    {
        var A = F.Id("A"); var n = F.Id("n");
        var B = QCall("HahnSeries", "ofPowerSeries", Integers(), Rationals(), A);
        var rhs = Pow(Sub(Mul(Pow(D(4), n), Pow(B, n)), Mul(D(4), B)), Add(n, D(1)));
        return Disp(All("A", Series(Rationals()), All("n", Integers(), Eqn(Call("term", A, n), rhs))));
    }

    private static Formula IsGFFormula()
    {
        var A = F.Id("A"); var N = F.Id("N"); var K = F.Id("K"); var j = F.Id("j");
        var window = Eqn(SumOver("j", Integers(), Window(K), Coeff(Cast(N, Integers()), Call("term", A, j))), Mul(D(2), Coeff(N, Call("theta4"))));
        var all = All("N", Naturals(), All("K", Naturals(), Implies(Leq(Add(N, D(1)), K), window)));
        var body = And(Eqn(Constant(A), D(0)), And(Eqn(Coeff(D(1), A), D(1)), all));
        return Disp(All("A", Series(Rationals()), Iff(Call("IsGF", A), body)));
    }

    private static Formula ClaimBody()
    {
        var A = F.Id("A"); var n = F.Id("n"); var m = F.Id("m");
        var square = Call("IsSquare", n);
        var witness = And(Eqn(Coeff(n, A), Cast(m, Rationals())), And(Iff(Call("Odd", m), square), And(Iff(ModEq(D(4), m, Pow(Negative(D(1)), Sub(n, D(1)))), square), Implies(Not(square), Divides(D(4), m)))));
        var universal = All("A", Series(Rationals()), Implies(Call("IsGF", A), All("n", Naturals(), Implies(Lt(D(0), n), Exists("m", Integers(), witness)))));
        return Disp(And(Exists("A", Series(Rationals()), Call("IsGF", A)), universal));
    }
}
