using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovPartIVC2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovPartIVC2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/dimitrovlazarova2026part4c2");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second conjecture in Dimitrov and Lazarova Part 4 holds throughout its full natural-number range.",
        H("Dimitrov and Lazarova Part 4, Conjecture 2"),
        Blocks(
            Node("claim", "The complete second conjecture", ClaimBody(),
                "The statement is Conjecture 2 in Section 4 of the source. Nat.totient is Euler's totient, "
                + "psi is the existing Dedekind psi function, and ArithmeticFunction.sigma 1 is the sum of positive divisors. "
                + "The identity OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of "
                + "p^(e−1)(p+1) over the exact prime-power factors of n. ArithmeticFunction.sigma_one_apply "
                + "identifies the divisor sum. Every exponent is applied to a function value, and every quotient "
                + "and subtraction in the displayed inequality is real. Both natural-number quantifiers are unrestricted "
                + "apart from n ≥ 2 and k ≥ 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full power-family inequality", ClaimBody(),
                "Put A=φ(n)^k, B=ψ(n)^k, C=σ(n)^k, U=(n−1)^k and V=(n+1)^k. "
                + "The existing bounds psi_ge and sigma_ge_psi, together with positivity and the totient upper bound, "
                + "give 1 ≤ V/U ≤ B/A ≤ C/A. For real 1 ≤ r ≤ x ≤ y, put F=xy+x/y²+y/x². "
                + "The identity F−(x²+2/x)=(y−x)((x³−1)y²+(y−x)(2y+x))/(x²y²) is nonnegative. "
                + "Also x²+2/x−(r²+2/r)=(x−r)((x+r)xr−2)/(xr) is nonnegative. "
                + "Apply these identities at r=V/U, x=B/A and y=C/A. Exact field normalization converts "
                + "the left side to F and the right side to r²+2/r, including all three pairwise numerator terms "
                + "and the denominator exponents 2k and 4k. This covers every prime and composite n and every allowed k. "
                + "The argument uses no new arithmetic-function definition and claims no priority for the analytic inequality. "
                + "The imported arithmetic development retains its existing supplier attribution and license.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dimitrov-lazarova-part4-conjecture-2"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("dimitrov-partiv-c2-" + name),
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
        Formula numerator = Add(Add(Mul(Pow(a, three), Pow(b, three)),
            Mul(Pow(b, three), Pow(c, three))), Mul(Pow(a, three), Pow(c, three)));
        Formula denominator = Mul(Mul(Pow(a, two), Pow(b, two)), Pow(c, two));
        Formula rhsNumerator = Add(Mul(D(2), Pow(Sub(Pow(Cast(n), D(2)), D(1)), three)),
            Pow(Add(Cast(n), D(1)), Mul(D(6), k)));
        Formula rhsDenominator = Mul(Pow(Sub(Cast(n), D(1)), two),
            Pow(Add(Cast(n), D(1)), Mul(D(4), k)));
        return All("n", Naturals(), Imp(Le(D(2), n),
            All("k", Naturals(), Imp(Le(D(1), k),
                Ge(Div(numerator, denominator), Div(rhsNumerator, rhsDenominator))))));
    }

    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Reals()));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Div(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
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
