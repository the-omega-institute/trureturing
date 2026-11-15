using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovPartFourC4Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovPartFourC4.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/dimitrovlazarova2026part4c2");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fourth conjecture in Dimitrov and Lazarova Part 4 holds throughout its full natural-number range.",
        H("Dimitrov and Lazarova Part 4, Conjecture 4"),
        Blocks(
            Node("claim", "The complete fourth conjecture", ClaimBody(),
                "The statement is Conjecture 4 in Section 4, page 13, MathML mm202–204 of the source (DOI 10.3390/math14213935, Mathematics 14(21), 3935; CC BY 4.0). Definitions are in Section 1, pages 1–2. Nat.totient is Euler's totient, "
                + "psi is the existing Dedekind psi function, and ArithmeticFunction.sigma 1 is the sum of positive divisors. "
                + "The identity OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of "
                + "p^(e−1)(p+1) over the exact prime-power factors of n. ArithmeticFunction.sigma_one_apply "
                + "identifies the divisor sum. Every pair sum is powered as a whole, and every quotient "
                + "and n−1 in the displayed inequality are real. Both natural-number quantifiers are unrestricted "
                + "apart from n ≥ 2 and k ≥ 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full powered mixed-product quotient", ClaimBody(),
                "Put a=φ(n), b=ψ(n), c=σ(n), A=a(b+c), B=b(a+c), C=c(a+b) and r=n/(n−1). "
                + "The imported arithmetic bounds and mixed_bound at m=1 give 0<A, r≤B/A≤C/A and 1≤r. "
                + "For x=(B/A)^k, y=(C/A)^k and R=r^k, the consumed cubic_ratio_bound proves "
                + "(1+x³+y³)/(xy)≥(1+2R³)/R². Its proof expands the cleared difference as "
                + "R(R³−1)((x−R)+(y−R))+3R³((x−R)−(y−R))² "
                + "+(4R³−1)(x−R)(y−R)+R²((x−R)³+(y−R)³), whose terms are nonnegative. "
                + "Exact field normalization recovers every factor and ordinary power of the original quotient. "
                + "This is the complete natural-number family; source Theorem 4 supplies only k=1. "
                + "No analytic novelty, equality classification or worldwide priority is claimed. The imported "
                + "arithmetic development retains its existing supplier attribution and license.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dimitrov-lazarova-part4-conjecture-4"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("dimitrov-partfour-c4-" + name),
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
        Formula numerator = Add(Add(Mul(Pow(a, three), Pow(Add(b, c), three)),
            Mul(Pow(b, three), Pow(Add(a, c), three))), Mul(Pow(c, three), Pow(Add(a, b), three)));
        Formula denominator = Mul(Mul(Mul(Mul(Mul(Pow(a, k), Pow(b, k)), Pow(c, k)),
            Pow(Add(a, b), k)), Pow(Add(b, c), k)), Pow(Add(a, c), k));
        Formula minusOne = new Formula.Binary(Cast(n), FormulaBinaryOperator.Subtract, D(1));
        Formula rhsNumerator = Add(Mul(D(2), Pow(Cast(n), three)), Pow(minusOne, three));
        Formula rhsDenominator = Mul(Pow(Cast(n), two), Pow(minusOne, k));
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
