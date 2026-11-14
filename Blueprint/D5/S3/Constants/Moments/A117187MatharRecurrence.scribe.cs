using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class A117187MatharRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Constants/Moments/A117187MatharRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mathar2011a117187");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal Catalan generating function in A117187 satisfies the printed order-three recurrence for every natural index at least three.",
        H("Mathar's recurrence for the literal A117187 generating function"),
        Blocks(
            Paragraph(Text("All series are formal power series over the integers; no analytic convergence is assumed. C is the standard Catalan series, Cprime is its formal derivative, and T(f) substitutes X squared for X. Thus T(f)=f(X²). The map U selects the inverse of a series whose constant coefficient is the unit 1. All sequence indices are natural numbers, while recurrence coefficients and values are integers.")),
            Node("catalan_square", "Catalan substitution", Disp(Eq(F.Id("B"), Call("T", F.Id("C")))),
                "B=C(X²), using the standard Catalan series, rather than a sequence defined by a recurrence.", DescribeRole.Definition),
            Node("source_root", "The normalized square-root branch", Disp(Eq(F.Id("S"), Sub(D(1), Mul(D(2), Mul(Pow(F.Id("X"), D(2)), F.Id("B")))))),
                "S=1-2X²C(X²). The result proves S²=1-4X² and constant coefficient 1, and proves uniqueness among all series with these two properties.", DescribeRole.Definition),
            Node("denominator", "The full source denominator", Disp(Eq(F.Id("D"), Mul(P(Sub(D(1), Mul(Pow(F.Id("X"), D(2)), F.Id("B")))), F.Id("S")))),
                "D is exactly (1-X²C(X²))sqrt(1-4X²) with the constant-one branch. Its constant coefficient is 1, so it has a genuine two-sided unit inverse.", DescribeRole.Definition),
            Node("source_series", "The literal source generating function", Disp(Eq(F.Id("F"), Mul(Mul(P(Add(D(1), F.Id("X"))), F.Id("B")), Call("U", F.Id("D"))))),
                "F=(1+X)C(X²)/((1-X²C(X²))sqrt(1-4X²)). Division denotes multiplication by the proven unit inverse, not a formal symbol with an assumed cancellation law.", DescribeRole.Definition),
            Node("a", "Offset-zero source coefficients", Disp(All("n", Naturals(), Eq(Call("a", F.Id("n")), Call("coeff", F.Id("F"), F.Id("n"))))),
                "a(n) is the coefficient of X to the n in the complete source series F.", DescribeRole.Definition),
            Node("result", "Normalized source interpretation and the exact recurrence", ResultFormula(),
                "The Catalan quadratic identity determines the normalized square root and shows that the denominator has constant coefficient 1. The existing Catalan differential identity X(1-4X)Cprime+(1-2X)C=1, together with the quadratic equation, gives Cprime(1-2XC)=C² and C²(1-XC)=C. Substitution X to X² and cancellation with the unit inverse give the full identity F=(1+X)Cprime(X²). Consequently a(2m)=a(2m+1)=binomial(2m+2,m), reusing the Catalan derivative coefficient identity.", DescribeRole.Theorem,
                "Write b(m)=binomial(2m+2,m). Adjacent-binomial identities give E(m)=m(m+2)b(m)-2(m+1)(2m+1)b(m-1)=0 for m≥1. For the printed residual R, polynomial normalization gives R(2m+1)=272E(m) for m≥1 and mR(2m)=4(31m-6)E(m)+4(37m+12)E(m-1) for m≥2. These two domains include every n≥3, including n=3. The source gives no explicit recurrence onset; n≥3 is exactly its order-three nonnegative-index domain. The conclusion concerns this literal source and printed recurrence."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string text, DescribeRole role, string? more = null) =>
        Describe.Lean(DescribeId.Create("a117187-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            name == "result" ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            more is null ? Blocks(Paragraph(Text(text))) : Blocks(Paragraph(Text(text)), Paragraph(Text(more))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("mathar-2011-a117187-recurrence"), ResolutionKind.Proved) : null);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Series() => Call("PowerSeries", Seq(Mathbb, Grp(F.Id("Z"))));
    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Constant(Formula f) => Call("constantCoeff", f);
    private static Formula Radicand() => Sub(D(1), Mul(D(4), Pow(F.Id("X"), D(2))));
    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), s = F.Id("S"), d = F.Id("D"), r = F.Id("r");
        Formula Value(int lag) => Call("a", lag == 0 ? n : Sub(n, D((byte)lag)));
        var root = And(Eq(Constant(s), D(1)), And(Eq(Pow(s, D(2)), Radicand()),
            All("r", Series(), Imp(Eq(Constant(r), D(1)), Imp(Eq(Pow(r, D(2)), Radicand()), Eq(r, s))))));
        var unit = And(Call("IsUnit", d), And(Eq(Mul(d, Call("U", d)), D(1)), Eq(Mul(Call("U", d), d), D(1))));
        var bridge = Eq(F.Id("F"), Mul(P(Add(D(1), F.Id("X"))), Call("T", F.Id("Cprime"))));
        var t0 = Mul(Mul(P(Add(n, D(4))), P(Sub(Mul(D(3,1), n), D(1,2)))), Value(0));
        var t1 = Mul(P(Sub(Add(Mul(D(3,7), Pow(n, D(2))), Mul(D(2,4), n)), D(1,5,6))), Value(1));
        var t2 = Mul(Mul(D(4), P(Add(Add(Mul(D(3,1), Pow(n, D(2))), Mul(D(8,1), n)), D(2,4)))), Value(2));
        var t3 = Mul(Mul(Mul(D(4), P(Add(Mul(D(3,7), n), D(2,4)))), P(Sub(n, D(1)))), Value(3));
        var recurrence = All("n", Naturals(), Imp(new Formula.Relation(D(3), FormulaRelationOperator.LessThanOrEqual, n), Eq(Sub(Sub(Add(t0, t1), t2), t3), D(0))));
        return Disp(And(P(root), And(P(unit), And(P(bridge), recurrence))));
    }
}
