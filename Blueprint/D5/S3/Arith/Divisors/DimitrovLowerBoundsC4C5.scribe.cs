using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovLowerBoundsC4C5Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/dimitrov2026c4c5");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dimitrov's reciprocal-product Conjectures 4 and 5 hold for every n ≥ 2 and k ≥ 1.",
        H("Dimitrov's full reciprocal-product lower bounds"),
        Blocks(
            Node("claim4", "Dimitrov Conjecture 4", Claim4Body(),
                "The source is arXiv:2606.12484v1, §2, PDF page 4. The variables are integers n ≥ 2 and k ≥ 1. "
                + "Nat.totient is Euler's φ, psi is the local Dedekind ψ definition, and ArithmeticFunction.sigma 1 is the positive-divisor sum. "
                + "Every exponent k is a pointwise power of a function value, and all three displayed reciprocal denominators are retained.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim5", "Dimitrov Conjecture 5", Claim5Body(),
                "The source's fifth conjecture uses the pointwise k-th powers in every mixed sum and denominator. "
                + "Its quantifiers and native function meanings are unchanged from Conjecture 4.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result4", "The complete Conjecture 4 inequality", Claim4Body(),
                "The native ordering 0 < φ(n) ≤ n−1 < n+1 ≤ ψ(n) ≤ σ(n) and the ordered reciprocal-product ratio lemma "
                + "give the exact ratio n(n+1)^(k−1)/(n−1)^k. Mixed-power ordering supplies the required lower ratio, "
                + "and exact field normalization produces every source numerator and denominator term. "
                + "Every theorem in this derivation is bind-only; admission_basis is open-problem-resolution for the complete preregistered Conjecture 4 (#30196), with escape_witness none. "
                + "The faithful Reg escape audit is unfinished under issue #30221; no declared_validated mirror is claimed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("dimitrov-2606-12484-conjecture-4"), ResolutionKind.Proved)),
            Node("result5", "The complete Conjecture 5 inequality", Claim5Body(),
                "Apply the same ordered bound to φ(n)^k, ψ(n)^k and σ(n)^k. With q=((n+1)/(n−1))^k, "
                + "the bound becomes (q²+7q+10)/(q+1); clearing the positive denominator and using (n²−1)^k "
                + "is exactly the displayed source right-hand side. Every theorem in this derivation is bind-only; "
                + "admission_basis is open-problem-resolution for the complete preregistered Conjecture 5 (#30197), with escape_witness none. "
                + "The faithful Reg escape audit is unfinished "
                + "under issue #30221; no declared_validated mirror is claimed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("dimitrov-2606-12484-conjecture-5"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("dimitrov-c4-c5-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula Claim4Body()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        return All("n", Naturals(), Imp(Le(D(2), n),
            All("k", Naturals(), Imp(Le(D(1), k), Inequality4(n, k)))));
    }

    private static Formula Claim5Body()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        return All("n", Naturals(), Imp(Le(D(2), n),
            All("k", Naturals(), Imp(Le(D(1), k), Inequality5(n, k)))));
    }

    private static Formula Inequality4(Formula n, Formula k)
    {
        Formula phi = Phi(n);
        Formula psi = Psi(n);
        Formula sigma = Sigma(n);
        Formula a = Mul(Pow(phi, k), Add(psi, sigma));
        Formula b = Mul(Pow(psi, k), Add(Phi(n), Sigma(n)));
        Formula c = Mul(Pow(Sigma(n), k), Add(Phi(n), Psi(n)));
        Formula lhs = Mul(Add(Add(a, b), c), Add(Add(Div(D(1), a), Div(D(1), b)), Div(D(1), c)));
        Formula nm1 = Sub(CastNat(n), D(1));
        Formula np1 = Add(CastNat(n), D(1));
        Formula denominator = Mul(Mul(CastNat(n), Pow(np1, Sub(k, D(1)))), Pow(nm1, k));
        Formula numerator = Add(Add(Mul(Mul(D(5), CastNat(n)), Mul(Pow(np1, Sub(k, D(1))), Pow(nm1, k))),
            Mul(D(2), Pow(nm1, Mul(D(2), k)))),
            Mul(Mul(D(2), Pow(CastNat(n), D(2))), Pow(np1, Sub(Mul(D(2), k), D(2)))));
        return Ge(lhs, Div(numerator, denominator));
    }

    private static Formula Inequality5(Formula n, Formula k)
    {
        Formula phi = Phi(n);
        Formula psi = Psi(n);
        Formula sigma = Sigma(n);
        Formula a = Mul(Pow(phi, k), Add(Pow(psi, k), Pow(sigma, k)));
        Formula b = Mul(Pow(psi, k), Add(Pow(Phi(n), k), Pow(Sigma(n), k)));
        Formula c = Mul(Pow(Sigma(n), k), Add(Pow(Phi(n), k), Pow(Psi(n), k)));
        Formula lhs = Mul(Add(Add(a, b), c), Add(Add(Div(D(1), a), Div(D(1), b)), Div(D(1), c)));
        Formula nm1 = Sub(CastNat(n), D(1));
        Formula n2m1 = Sub(Pow(CastNat(n), D(2)), D(1));
        Formula np1 = Add(CastNat(n), D(1));
        Formula denominator = Add(Pow(nm1, Mul(D(2), k)), Pow(n2m1, k));
        Formula numerator = Add(Add(Mul(new Formula.Number(10), Pow(nm1, Mul(D(2), k))),
            Mul(D(7), Pow(n2m1, k))), Pow(np1, Mul(D(2), k)));
        return Ge(lhs, Div(numerator, denominator));
    }

    private static Formula Phi(Formula n) => Cast(Call(Q("Nat", "totient"), n));
    private static Formula Psi(Formula n) => Cast(Call(Named("psi"), n));
    private static Formula Sigma(Formula n) => Cast(Call(Q("ArithmeticFunction", "sigma"), D(1), n));
    private static Formula CastNat(Formula n) => Cast(n);
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
