using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovPartIVC1Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovPartIVC1.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/dimitrovlazarova2026part4c2");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first conjecture in Dimitrov and Lazarova Part 4 holds throughout its full natural-number range.",
        H("Dimitrov and Lazarova Part 4, Conjecture 1"),
        Blocks(
            Node("claim", "The complete first conjecture", ClaimBody(),
                "The statement is Conjecture 1 in Section 4, page 13 of the source. Nat.totient is Euler's totient, "
                + "psi is the existing Dedekind psi function, and ArithmeticFunction.sigma 1 is the sum of positive divisors. "
                + "The identity OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of "
                + "p^(e−1)(p+1) over the exact prime-power factors of n. ArithmeticFunction.sigma_one_apply "
                + "identifies the divisor sum. All powers are ordinary natural powers. Every quotient "
                + "and the subtraction n−1 are real. Both natural-number quantifiers are unrestricted "
                + "apart from n ≥ 2 and k ≥ 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full powered cubic quotient", ClaimBody(),
                "Put a=φ(n), b=ψ(n), c=σ(n), u=n−1 and v=n+1. The imported arithmetic bounds "
                + "give 0<a≤u and 0<v≤b≤c. For x=(b/a)^k, y=(c/a)^k and r=(v/u)^k, "
                + "these bounds give 1≤r≤x≤y. The original cubic_ratio_bound in DimitrovPartFourC4 "
                + "gives (1+2r³)/r²≤(1+x³+y³)/(xy). Clearing positive denominators identifies "
                + "the left side here with the publisher's right side and the right side here with "
                + "the publisher's left side. This proves the full power family of Conjecture 1. "
                + "The source's Theorem 1 gives k=1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dimitrov-lazarova-part4-conjecture-1"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("dimitrov-partiv-c1-" + name),
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
        Formula numerator = Add(Add(Pow(a, three), Pow(b, three)), Pow(c, three));
        Formula denominator = Mul(Mul(Pow(a, k), Pow(b, k)), Pow(c, k));
        Formula u = new Formula.Binary(Cast(n), FormulaBinaryOperator.Subtract, D(1));
        Formula v = Add(Cast(n), D(1));
        Formula rhsNumerator = Add(Mul(D(2), Pow(v, three)), Pow(u, three));
        Formula rhsDenominator = Mul(Pow(v, two), Pow(u, k));
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
