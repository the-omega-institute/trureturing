using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovPairSumC7Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovPairSumC7.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/dimitrov2026c7");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full powered pair-sum inequality for Euler totient, Dedekind psi and the divisor sum.",
        H("Dimitrov's seventh pair-sum inequality"),
        Blocks(
            Node("claim", "The complete original seventh conjecture", ClaimBody(),
                "Conjecture 7 of arXiv:2606.12484v1 quantifies all natural n at least two and k at least one. "
                + "Nat.totient is Euler's function, psi is the product of p^(e-1)(p+1) over exact prime powers, "
                + "and ArithmeticFunction.sigma 1 is the positive-divisor sum. Each entire pair sum is raised to k, "
                + "and every quotient is real.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full seventh inequality", ClaimBody(),
                "Let x=φ(n)+ψ(n), y=φ(n)+σ(n), z=ψ(n)+σ(n) and q=(n+1)/n. "
                + "Totient positivity and DimitrovLowerBoundsC4C5.psi_ge and sigma_ge_psi give 0<x≤y. "
                + "The first projection of DimitrovPsiSigmaSeparation.separation gives q≤z/y, hence qy≤z. "
                + "Since q≥1, raising the inequalities to k gives 0<x^k≤y^k≤z^k "
                + "and 1≤q^k≤z^k/y^k. The first projection of DimitrovNesbittOppositeGap.opposite_gap "
                + "at X=x^k, Y=y^k, Z=z^k and s=q^k gives the lower bound q^k/2+2/(1+q^k). "
                + "Exact field normalization gives the displayed right side. The Library note cites both suppliers "
                + "and the attribution for the imported C4/C5 development. In the bounded source screen, "
                + "Part III Theorem 5 treats k=1. Part IV and the public Lean donor at "
                + "95809b59deefd8dfad81e398250aedd7e1aea3b3 leave the full C7 assertion uncovered.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dimitrov-2606-12484-conjecture-7"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("dimitrov-c7-" + name),
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
        Formula x = Pow(Add(phi, psi), k);
        Formula y = Pow(Add(phi, sigma), k);
        Formula z = Pow(Add(psi, sigma), k);
        Formula lhs = Add(Add(Div(x, Add(y, z)), Div(y, Add(x, z))), Div(z, Add(x, y)));
        Formula u = Pow(Cast(n), Mul(D(2), k));
        Formula v = Pow(Add(Cast(n), D(1)), Mul(D(2), k));
        Formula w = Mul(Pow(Cast(n), k), Pow(Add(Cast(n), D(1)), k));
        Formula rhs = Div(Add(Add(Mul(D(4), u), v), w), Mul(D(2), Add(u, w)));
        return All("n", Naturals(), Imp(Le(D(2), n),
            All("k", Naturals(), Imp(Le(D(1), k), Ge(lhs, rhs)))));
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
