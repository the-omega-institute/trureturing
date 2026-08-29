using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.PrimeRefinement;

internal sealed class LocalNonzeroContinuationZeroDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime Euler factors can stay nonzero at a zero of analytically continued zeta.",
        H("Local Nonzero Factors and a Continued Zeta Zero"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-prime-euler-factor-is-nonzero-at-a-parameter"),
                DeclarationHandle.Create(Prefix + "EveryPrimeEulerFactorNonzeroAt"),
                H("Every prime Euler factor is nonzero at a parameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This predicate records pointwise nonvanishing of each prime-indexed "
                        + "inverse Euler denominator. It asserts no convergence of the "
                        + "corresponding infinite product."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("base-one-is-the-only-local-obstruction-at-minus-two"),
                DeclarationHandle.Create(Prefix + "local_euler_factor_ne_zero_of_ne_one"),
                H("Base one is the only local obstruction at minus two"),
                StatementSource.FromAuthor(LocalNonzeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At minus two, every natural base other than one has a nonzero local "
                        + "inverse denominator. The proof therefore weakens primality to its "
                        + "exact algebraic requirement for this witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("excluding-base-one-is-necessary"),
                DeclarationHandle.Create(Prefix + "base_one_exclusion_is_necessary"),
                H("Excluding base one is necessary"),
                StatementSource.FromAuthor(BaseOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete base-one factor is zero at minus two. Thus extending the "
                        + "local claim to every natural base without an exclusion is false."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-nonzero-does-not-force-continuation-nonzero"),
                DeclarationHandle.Create(
                    Prefix + "local_euler_nonzero_continuation_zero_counterexample"),
                H("Local nonzero does not force continuation nonzero"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The witness is minus two. Every prime local factor and every finite prime "
                        + "window is nonzero there, while the analytically continued Riemann "
                        + "zeta function vanishes by its first trivial-zero theorem. No "
                        + "infinite Euler-product convergence at minus two is claimed."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/EulerProduct"))]));

    private static Formula LocalFactorAtMinusTwo(Formula basis)
    {
        Formula square = new Formula.Power(basis, D(2));
        Formula denominator = Seq(Open, D(1), Sp, Minus, Sp, square, Close);
        return new Formula.Power(denominator, Seq(Minus, D(1)));
    }

    private static Formula LocalNonzeroFormula()
    {
        Formula basis = F.Id("p");
        return Disp(Seq(
            Forall, Sp, basis, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            basis, Sp, Neq, Sp, D(1), Sp, Rightarrow, Sp,
            LocalFactorAtMinusTwo(basis), Sp, Neq, Sp, D(0), Dot));
    }

    private static Formula BaseOneFormula()
    {
        Formula denominator = Seq(
            Operatorname, Grp(F.Id("finiteEulerDenominator")),
            Open, D(1), Comma, Sp, Minus, D(2), Close);
        Formula factor = new Formula.Power(
            Seq(Open, denominator, Close), Seq(Minus, D(1)));
        return Disp(Seq(factor, Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula CounterexampleFormula()
    {
        Formula parameter = F.Id("s");
        Formula primes = F.Id("S");
        Formula prime = F.Id("p");
        Formula finitePrimeSet = Seq(
            primes, Sp, Subset, Underscore, Grp(Mathrm, Grp(F.Id("fin"))), Sp,
            Mathbb, Grp(F.Id("N")));
        Formula primeMembership = Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, primes, Comma, Sp,
            Operatorname, Grp(F.Id("Prime")), Open, prime, Close);
        Formula localPredicate = Seq(
            Operatorname, Grp(F.Id("EveryPrimeEulerFactorNonzeroAt")),
            Open, parameter, Close);
        Formula finiteProduct = Seq(
            Operatorname, Grp(F.Id("finiteEulerProduct")),
            Open, primes, Comma, Sp, parameter, Close);

        return Disp(Seq(
            Exists, Sp, parameter, Sp, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
            localPredicate, Sp, Land, Sp,
            Open, Forall, Sp, finitePrimeSet, Comma, Sp,
            Open, primeMembership, Close, Sp, Rightarrow, Sp,
            finiteProduct, Sp, Neq, Sp, D(0), Close, Sp, Land, Sp,
            Zeta, Open, parameter, Close, Sp, Eq, Sp, D(0), Dot));
    }
}
