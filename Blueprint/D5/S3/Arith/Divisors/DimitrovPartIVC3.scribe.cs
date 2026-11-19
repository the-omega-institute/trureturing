using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovPartIVC3Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovPartIVC3.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/dimitrovlazarova2026part4c2");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third conjecture in Dimitrov and Lazarova Part 4 holds throughout its full natural-number range.",
        H("Dimitrov and Lazarova Part 4, Conjecture 3"),
        Blocks(
            Node("claim", "The complete third conjecture", ClaimBody(),
                "The statement is Conjecture 3 in Section 4 of the source. Nat.totient is Euler's totient, "
                + "psi is the existing Dedekind psi function, and ArithmeticFunction.sigma 1 is the sum of positive divisors. "
                + "The identity OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of "
                + "p^(e−1)(p+1) over the exact prime-power factors of n. ArithmeticFunction.sigma_one_apply "
                + "identifies the divisor sum. Every pair sum is powered as a whole, and every quotient "
                + "in the displayed inequality is real. Both natural-number quantifiers are unrestricted "
                + "apart from n ≥ 2 and k ≥ 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full powered pair-sum inequality", ClaimBody(),
                "Put a=φ(n), b=ψ(n), c=σ(n) and q=(n+1)/n. The imported arithmetic bounds "
                + "give 0<a≤n−1, n+1≤b≤c and q(a+b)≤2b. The pair-gap inequality gives "
                + "q²(a+b)(a+c)≤(b+c)²; raising it to k yields the corresponding powered gap. "
                + "For x=(a+b)^k, y=(a+c)^k, z=(b+c)^k and Q=q^k≥1, put u=√(xy). "
                + "The inequalities x³+y³≥2u³ and z/u≥Q, followed by the monotonicity of "
                + "t²+2/t for t≥1, imply (x³+y³+z³)/(xyz)≥Q²+2/Q. "
                + "Exact field normalization identifies Q²+2/Q with the source right side. "
                + "This proves the complete natural-number family, extending the source's Theorem 3 at k=1. "
                + "No analytic priority or equality classification is asserted. The imported arithmetic "
                + "development retains its existing supplier attribution and license.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dimitrov-lazarova-part4-conjecture-3"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("dimitrov-partiv-c3-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula a = Cast(Call(Q("Nat", "totient"), n));
        Formula b = Cast(Call(Named("psi"), n));
        Formula c = Cast(Call(Q("ArithmeticFunction", "sigma"), D(1), n));
        Formula three = Mul(D(3), k);
        Formula two = Mul(D(2), k);
        Formula numerator = Add(Add(Pow(Add(a, b), three),
            Pow(Add(b, c), three)), Pow(Add(a, c), three));
        Formula denominator = Mul(Mul(Pow(Add(a, b), k), Pow(Add(b, c), k)), Pow(Add(a, c), k));
        Formula rhsNumerator = Add(Mul(D(2), Pow(Cast(n), three)), Pow(Add(Cast(n), D(1)), three));
        Formula rhsDenominator = Mul(Pow(Cast(n), two), Pow(Add(Cast(n), D(1)), k));
        return All("n", Naturals(), Imp(Le(D(2), n),
            All("k", Naturals(), Imp(Le(D(1), k),
                Ge(Div(numerator, denominator), Div(rhsNumerator, rhsDenominator))))));
    }

    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Reals()));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Ge(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
