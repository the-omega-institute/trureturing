using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MatharA174193OrderFourRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/MatharA174193OrderFourRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/mathar2016a174193");
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Series => Call("PowerSeries", Q);
    private static Formula X => F.Id("X");
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula f, int n) => new Formula.Power(f, Num(n));
    private static Formula Product(params Formula[] fs) => fs.Aggregate(Multiply);
    private static Formula SumOf(params Formula[] fs) => fs.Aggregate(Add);
    private static Formula Negative(Formula f) => new Formula.Negate(f);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);

    private static Formula SourceBody(Formula a)
    {
        Formula s = F.Id("s");
        return Some("s", Series, And(Equal(Call("constantCoeff", s), Num(1)),
            And(Equal(Pow(s, 2), F.Id("p")),
                Equal(Multiply(F.Id("D"), a), Subtract(F.Id("P"), Multiply(F.Id("B"), s))))));
    }

    private static Formula Recurrence(Formula a)
    {
        Formula n = F.Id("n");
        Formula qn = Parenthesized(Seq(n, Colon, Q));
        Formula Coeff(int k) => Call("coeff", k == 0 ? n : Subtract(n, Num(k)), a);
        Formula equation = Equal(SumOf(
            Product(Negative(Parenthesized(Add(qn, Num(2)))),
                Parenthesized(Subtract(Multiply(Num(404489), qn), Num(1866368))), Coeff(0)),
            Product(Parenthesized(Subtract(Subtract(Multiply(Num(3147815), Pow(qn, 2)),
                Multiply(Num(8680082), qn)), Num(14098754))), Coeff(1)),
            Product(Num(2), Parenthesized(SumOf(Multiply(Negative(Num(2336439)), Pow(qn, 2)),
                Multiply(Num(652022), qn), Num(14514849))), Coeff(2)),
            Product(Num(8), Parenthesized(Subtract(Add(Multiply(Negative(Num(1044770)), Pow(qn, 2)),
                Multiply(Num(10585023), qn)), Num(20370553))), Coeff(3)),
            Product(Num(8), Parenthesized(Subtract(Multiply(Num(642982), qn), Num(2004177))),
                Parenthesized(Subtract(Multiply(Num(2), qn), Num(9))), Coeff(4))), Num(0));
        return All("n", Nat, ImpliesTo(
            new Formula.Relation(Num(4), FormulaRelationOperator.LessThanOrEqual, n), equation));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("A");
        return And(Some("A", Series, Call("IsSourceSeries", a)),
            All("A", Series, ImpliesTo(Call("IsSourceSeries", a), Recurrence(a))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mathar-a174193-" + (name == "P" ? "numerator" : name.ToLowerInvariant())),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathar's order-four recurrence holds for the specified algebraic power series.",
        H("An order-four recurrence for OEIS A174193"),
        Blocks(
            Paragraph(Text("All series have rational coefficients. X is the power-series indeterminate. "
                + "The formal square root is specified by its square and constant coefficient. "
                + "Every recurrence scalar is rational; n and the arguments n-1 through n-4 are natural, "
                + "with natural subtraction under the guard 4 ≤ n.")),
            Node("p", "The radicand", Equal(F.Id("p"), Subtract(Num(1), Multiply(Num(4), X))),
                AssessedProvenance.FromLiterature(Source),
                "The radicand is 1-4*x in OEIS A174193, FORMULA section (no page numbers).",
                DescribeRole.Definition),
            Node("P", "The rational numerator polynomial", Equal(F.Id("P"),
                Subtract(SumOf(Subtract(Num(1), Multiply(Num(8), X)),
                    Multiply(Num(13), Pow(X, 2)), Multiply(Num(24), Pow(X, 3))),
                    Multiply(Num(48), Pow(X, 4)))),
                AssessedProvenance.FromLiterature(Source),
                "The rational part of the source numerator is 1-8*x+13*x^2+24*x^3-48*x^4.",
                DescribeRole.Definition),
            Node("B", "The square-root multiplier", Equal(F.Id("B"),
                Subtract(Subtract(SumOf(Subtract(Num(1), Multiply(Num(6), X)), Pow(X, 2),
                    Multiply(Num(34), Pow(X, 3))), Multiply(Num(26), Pow(X, 4))),
                    Multiply(Num(4), Pow(X, 5)))),
                AssessedProvenance.FromLiterature(Source),
                "The polynomial multiplying the square root is 1-6*x+x^2+34*x^3-26*x^4-4*x^5.",
                DescribeRole.Definition),
            Node("D", "The denominator polynomial", Equal(F.Id("D"),
                Product(Num(2), Pow(X, 2), Parenthesized(Subtract(Num(1), X)), Pow(F.Id("p"), 2))),
                AssessedProvenance.FromLiterature(Source),
                "The denominator is 2*x^2*(1 -x)*(1- 4*x)^2; its constant coefficient is zero.",
                DescribeRole.Definition),
            Node("IsSourceSeries", "The exact algebraic source series",
                All("A", Series, IffTo(Call("IsSourceSeries", F.Id("A")), SourceBody(F.Id("A")))),
                AssessedProvenance.FromLiterature(Source),
                "OEIS A174193, FORMULA section (no page numbers): “G.f.: "
                + "(1-8*x+13*x^2+24*x^3-48*x^4-(1-6*x+x^2+34*x^3-26*x^4-4*x^5)*sqrt(1-4*x))/"
                + "(2*x^2*(1 -x)*(1- 4*x)^2)”. The letters p, P, B and D denote the four "
                + "polynomials above. A is the generating series and s is the square root with "
                + "constant coefficient one. D*A=P-B*s expresses the source fraction after clearing "
                + "its nonunit denominator; existence of A is asserted separately below.",
                DescribeRole.Definition),
            Node("claim", "Mathar's recurrence assertion", IffTo(F.Id("claim"), ClaimBody()),
                AssessedProvenance.FromLiterature(Source),
                "OEIS A174193, FORMULA section (no page numbers): “Conjecture: "
                + "-(n+2)*(404489*n-1866368)*a(n) +(3147815*n^2-8680082*n-14098754)*a(n-1) "
                + "+2*(-2336439*n^2+652022*n+14514849)*a(n-2) "
                + "+8*(-1044770*n^2+10585023*n-20370553)*a(n-3) "
                + "+8*(642982*n-2004177)*(2*n-9)*a(n-4)=0. - _R. J. Mathar_, Jun 14 2016”. "
                + "Here a(n) is coeff n A. OEIS OFFSET 0,3 gives index zero to the first coefficient; "
                + "the second offset component is metadata. All five sequence terms exist for n ≥ 4. "
                + "The assertion includes existence of a source series and quantifies over every such A.",
                DescribeRole.Definition),
            Node("result", "The recurrence holds", ClaimBody(), AssessedProvenance.FromRepo(Source),
                "Map the natural Catalan series to rational coefficients and set s=1-2*X*C. "
                + "Its quadratic equation gives s^2=1-4*X. The numerator P-B*s has a factor X^2; "
                + "the remaining denominator has constant coefficient two and is invertible. "
                + "This constructs a source series. Differentiating its equation twice and cancelling "
                + "nonzero polynomial factors yields a second-order Euler differential identity with "
                + "a cubic right-hand side. The square-root terms cancel by two explicit polynomial "
                + "identities. Coefficients of degree n ≥ 4 therefore give the displayed recurrence. "
                + "The identification with the counting series of Av(321)^{+1}, and the background "
                + "paper's Section 4 questions, are not proved here.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-a174193-order-four-recurrence"),
                    ResolutionKind.Proved)))));
}
