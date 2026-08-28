using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class PrimeFactorCountGeneratingFunctionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zeta-law distinct-prime count has a convergent probability generating product.",
        H("Probability Generating Function of the Distinct Prime Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-factor-count-pgf-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "primeFactorCountPGF"),
                H("The distinct-prime probability generating function"),
                StatementSource.FromAuthor(PgfDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The definition integrates z raised to the repository's canonical "
                        + "distinct-prime count under the zeta probability law."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-factor-count-euler-factor-definition"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "primeFactorCountEulerFactor"),
                H("One prime contributes one affine Euler factor"),
                StatementSource.FromAuthor(EulerFactorDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The local factor is the generating function of the imported Bernoulli "
                        + "prime-support coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-factor-count-euler-factors-multipliable"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "prime_factor_count_euler_factors_multipliable"),
                H("The prime-indexed Euler factors are multipliable"),
                StatementSource.FromAuthor(MultipliableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Convergence follows from summability of the prime evidence family and "
                        + "does not otherwise use the distribution of the prime indices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-factor-count-pgf-euler-product"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_factor_count_pgf_euler_product"),
                H("The distinct-prime PGF equals its convergent Euler product"),
                StatementSource.FromAuthor(EulerProductFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For zero through one, finite independent Bernoulli products converge "
                            + "under the integral to the full distinct-prime count.")),
                    Paragraph(Text(
                        "The multiplicity-counting formula remains open because the source "
                            + "does not state its convergence domain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-factor-count-pgf-at-one"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_factor_count_pgf_at_one"),
                H("At one the PGF is total probability"),
                StatementSource.FromAuthor(AtOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The generating integrand is constantly one, so the endpoint is the total "
                        + "mass of the zeta probability law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-factor-count-pgf-at-zero"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_factor_count_pgf_at_zero"),
                H("At zero the PGF is the zeta mass of one"),
                StatementSource.FromAuthor(AtZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The totalized count also vanishes at zero, but the zeta law assigns zero "
                        + "mass there; every natural above one has positive count."))),
                DescribeRole.Theorem))));

    private static Formula PgfDefinitionFormula()
    {
        Formula s = F.Id("s");
        Formula z = F.Id("z");
        Formula n = F.Id("N");
        Formula expectation = Call(
            "ExpectationUnderZeta", s, new Formula.Power(z, F.Grp(Count(n))));
        return F.Disp(DefinedAs(Pgf(s, z), expectation));
    }

    private static Formula EulerFactorDefinitionFormula()
    {
        Formula s = F.Id("s");
        Formula z = F.Id("z");
        Formula p = F.Id("p");
        Formula oneMinusZ = F.Grp(F.D(1), F.Sp, F.Minus, F.Sp, z);
        Formula term = F.Seq(
            oneMinusZ, F.Sp, F.Cdot, F.Sp, PrimeEvidence(p, s));
        return F.Disp(DefinedAs(
            EulerFactor(s, z, p),
            F.Seq(F.D(1), F.Sp, F.Minus, F.Sp, term)));
    }

    private static Formula MultipliableFormula()
    {
        Formula s = F.Id("s");
        Formula z = F.Id("z");
        Formula p = F.Id("p");
        Formula family = F.Seq(
            p, F.Sp, F.Mapsto, F.Sp, EulerFactor(s, z, p));
        return F.Disp(new Formula.Logic(
            OneLessThan(s),
            FormulaLogicOperator.Implies,
            Call("Multipliable", family)));
    }

    private static Formula EulerProductFormula()
    {
        Formula s = F.Id("s");
        Formula z = F.Id("z");
        Formula p = F.Id("p");
        Formula domain = new Formula.Logic(
            OneLessThan(s),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Nonnegative(z),
                FormulaLogicOperator.And,
                AtMostOne(z)));
        Formula result = Equal(
            Pgf(s, z),
            PrimeProduct(p, EulerFactor(s, z, p)));
        return F.Disp(new Formula.Logic(
            domain,
            FormulaLogicOperator.Implies,
            result));
    }

    private static Formula AtOneFormula()
    {
        Formula s = F.Id("s");
        Formula result = Equal(Pgf(s, F.D(1)), F.D(1));
        return F.Disp(new Formula.Logic(
            OneLessThan(s),
            FormulaLogicOperator.Implies,
            result));
    }

    private static Formula AtZeroFormula()
    {
        Formula s = F.Id("s");
        Formula result = Equal(Pgf(s, F.D(0)), Call("ZetaMass", s, F.D(1)));
        return F.Disp(new Formula.Logic(
            OneLessThan(s),
            FormulaLogicOperator.Implies,
            result));
    }

    private static Formula Pgf(Formula s, Formula z) =>
        Call("PrimeFactorCountPGF", s, z);

    private static Formula EulerFactor(Formula s, Formula z, Formula p) =>
        Call("PrimeFactorCountEulerFactor", s, z, p);

    private static Formula Count(Formula n) =>
        Call("PrimeFactorCount", n);

    private static Formula PrimeEvidence(Formula p, Formula s) =>
        new Formula.Power(p, F.Grp(F.Seq(F.Minus, s)));

    private static Formula PrimeProduct(Formula p, Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(p, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("P"))),
            F.Sp, body);

    private static Formula DefinedAs(Formula left, Formula right) =>
        F.Seq(left, F.Sp, F.Colon, F.Eq, F.Sp, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula OneLessThan(Formula value) =>
        new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, value);

    private static Formula Nonnegative(Formula value) =>
        new Formula.Relation(F.D(0), FormulaRelationOperator.LessThanOrEqual, value);

    private static Formula AtMostOne(Formula value) =>
        new Formula.Relation(value, FormulaRelationOperator.LessThanOrEqual, F.D(1));
}
