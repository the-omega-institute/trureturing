using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class DimitrovNesbittC8Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/DimitrovNesbittC8.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/dimitrov2026c8");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed-power Nesbitt lower bound holds for every n ≥ 2 and k ≥ 1.",
        H("Dimitrov's complete Conjecture 8"),
        Blocks(
            Node("claim", "Dimitrov Conjecture 8", ClaimBody(),
                "The source states: For every integers k ≥ 1 and n ≥ 2, we have the displayed inequality. "
                + "Nat.totient is Euler's totient, psi is Dedekind's function from OeisA344695GcdSigmaPsiPrimes, "
                + "and ArithmeticFunction.sigma 1 is the sum of positive divisors. Function values are raised to pointwise powers; "
                + "the inner sums in all three mixed terms remain unpowered. The natural exponent 2k−2 agrees with the source because k ≥ 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full Conjecture 8 inequality", ClaimBody(),
                "The original arithmetic bounds and mixed_bound in DimitrovLowerBoundsC4C5 give 0 < A ≤ B ≤ C "
                + "and 1 ≤ R ≤ B/A ≤ C/A, where R=n(n+1)^(k−1)/(n−1)^k. "
                + "The ratio-constrained Nesbitt inequality at x=B/A, y=C/A and r=R yields "
                + "(4R²+R+1)/(2(R²+R)). Exact field normalization gives the displayed source bound. "
                + "The analytic step is a modified Apache-2.0 source port: balanced_pair_fraction_le and nesbitt_envelope_mono "
                + "are consumed by normalized_nesbitt_ratio_inequality from pro20541/dimitrov-conjectures-lean at "
                + "95809b59deefd8dfad81e398250aedd7e1aea3b3, FrontierMathLean/NesbittRatioInequality.lean. "
                + "Michael Mazur is the upstream author/maintainer, with substantive OpenAI Codex generation disclosed under his direction. "
                + "Namespace and private visibility are adapted; the source note supplies the immutable URL, hash, license and receiver-pin retirement condition. "
                + "This application includes k=1 and every composite or prime n ≥ 2.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("dimitrov-2606-12484-conjecture-8"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("dimitrov-c8-" + name), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula a = Mul(Pow(Phi(n), k), Add(Psi(n), Sigma(n)));
        Formula b = Mul(Pow(Psi(n), k), Add(Phi(n), Sigma(n)));
        Formula c = Mul(Pow(Sigma(n), k), Add(Phi(n), Psi(n)));
        Formula lhs = Add(Add(Div(a, Add(b, c)), Div(b, Add(a, c))), Div(c, Add(a, b)));
        Formula nm1 = Sub(CastNat(n), D(1));
        Formula np1 = Add(CastNat(n), D(1));
        Formula cross = Mul(Mul(CastNat(n), Pow(np1, Sub(k, D(1)))), Pow(nm1, k));
        Formula squareD = Mul(Pow(CastNat(n), D(2)), Pow(np1, Sub(Mul(D(2), k), D(2))));
        Formula numerator = Add(Add(cross, Pow(nm1, Mul(D(2), k))), Mul(D(4), squareD));
        Formula denominator = Add(Mul(D(2), squareD), Mul(D(2), cross));
        return All("n", Naturals(), Imp(Le(D(2), n), All("k", Naturals(), Imp(Le(D(1), k), Ge(lhs, Div(numerator, denominator))))));
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
