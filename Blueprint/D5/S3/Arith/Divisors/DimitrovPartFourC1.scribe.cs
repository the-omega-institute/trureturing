using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovPartFourC1Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovPartFourC1.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/dimitrovlazarova2026part4c2");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete positive-power quotient in Dimitrov–Lazarova Part 4 Conjecture 1.",
        H("Dimitrov–Lazarova Part 4 Conjecture 1"),
        Blocks(
            Node("claim", "The complete first conjecture", ClaimBody(),
                "Dimitrov and Lazarova state Conjecture 1 in Section 4, page 13 of Mathematics 14(21), 3935 "
                + "(DOI 10.3390/math14213935, CC BY 4.0). Nat.totient is Euler's totient. "
                + "OeisA344695GcdSigmaPsiPrimes.psi_prod identifies psi with the product of "
                + "p^(e−1)(p+1) over the exact prime powers in n. ArithmeticFunction.sigma_one_apply "
                + "identifies ArithmeticFunction.sigma 1 with the sum of positive divisors. All quotients "
                + "and n−1 are real, and all powers are ordinary powers of function values. "
                + "The natural-number ranges n ≥ 2 and k ≥ 1 are complete.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full positive-power cubic quotient", ClaimBody(),
                "Set A=φ(n)^k, B=ψ(n)^k, C=σ(n)^k, U=(n−1)^k and V=(n+1)^k. "
                + "Positivity, Nat.totient_lt, psi_ge and sigma_ge_psi give 0<A≤U≤V≤B≤C. "
                + "Apply DimitrovPartFourC4.cubic_ratio_bound at r=V/U, x=B/A and y=C/A, where x,y≥r≥1. "
                + "The supplier proves the cleared cubic difference is nonnegative by expanding it as "
                + "r(r³−1)((x−r)+(y−r))+3r³((x−r)−(y−r))² "
                + "+(4r³−1)(x−r)(y−r)+r²((x−r)³+(y−r)³). "
                + "Exact field normalization recovers the displayed source quotients. "
                + "At k=1 the result recovers source Theorem 1. The last term in the expansion forces "
                + "x=y=r at equality. In the arithmetic application this forces A=U and hence n prime. "
                + "Conversely every prime has A=U and B=C=V and attains the bound for every allowed k. "
                + "The original cubic lemma is owned by "
                + "the Part IV C4 module, where it was private. The imported C4/C5 arithmetic bounds "
                + "retain their existing supplier attribution and license.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dimitrov-lazarova-part4-conjecture-1"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("dimitrov-part4-c1-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula phi = Cast(Call(Q("Nat", "totient"), n));
        Formula psi = Cast(Call(Named("psi"), n));
        Formula sigma = Cast(Call(Q("ArithmeticFunction", "sigma"), D(1), n));
        Formula threeK = Mul(D(3), k);
        Formula lhs = Div(Add(Add(Pow(phi, threeK), Pow(psi, threeK)), Pow(sigma, threeK)),
            Mul(Mul(Pow(phi, k), Pow(psi, k)), Pow(sigma, k)));
        Formula u = Sub(Cast(n), D(1));
        Formula v = Add(Cast(n), D(1));
        Formula rhs = Div(Add(Mul(D(2), Pow(v, threeK)), Pow(u, threeK)),
            Mul(Pow(v, Mul(D(2), k)), Pow(u, k)));
        return All("n", Naturals(), Imp(Le(D(2), n),
            All("k", Naturals(), Imp(Le(D(1), k), Ge(lhs, rhs)))));
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
