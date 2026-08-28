using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class RestrictedZetaPosteriorDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single observed prime leaves a restricted zeta posterior.",
        H("Restricted Zeta Posterior"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("restricted-zeta-euler-split"),
                DeclarationHandle.Create(Prefix + "restricted_zeta_euler_split"),
                H("The restricted partition splits the Euler product"),
                StatementSource.FromAuthor(EulerSplitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Above one, removing one prime factor from the full Euler product "
                        + "gives the restricted zeta normalizer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-prime-restricted-zeta-posterior"),
                DeclarationHandle.Create(Prefix + "single_prime_restricted_zeta_posterior"),
                H("One observed exponent leaves a restricted zeta conditional law"),
                StatementSource.FromAuthor(SinglePosteriorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a concrete zeta law, conditioning on one prime exponent leaves "
                        + "the coprime cofactor with its restricted normalizer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-observation-recovers-zeta"),
                DeclarationHandle.Create(Prefix + "empty_prime_observation_recovers_zeta"),
                H("The empty observation recovers the original zeta point mass"),
                StatementSource.FromAuthor(EmptyObservationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With no observed primes, the conditional law is the unconditioned "
                        + "zeta point mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-cofactor-posterior"),
                DeclarationHandle.Create(Prefix + "single_prime_zero_cofactor_posterior"),
                H("A zero cofactor has zero conditional mass"),
                StatementSource.FromAuthor(ZeroCofactorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every observed positive prime power makes the zero cofactor event "
                        + "a null event under the zeta law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("restricted-zeta-partition-nonzero"),
                DeclarationHandle.Create(Prefix + "restricted_zeta_partition_ne_zero"),
                H("The restricted zeta normalizer is nonzero"),
                StatementSource.FromAuthor(PartitionNonzeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime and exponent above one, the restricted normalizer "
                        + "is strictly positive and hence nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zeta-exponent-above-one-necessary"),
                DeclarationHandle.Create(Prefix + "zeta_exponent_above_one_is_necessary"),
                H("The exponent threshold is necessary for normalization"),
                StatementSource.FromAuthor(ExponentNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At exponent one, the integer partition function is infinite, so the "
                        + "strict threshold cannot be dropped."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coprimality-necessary"),
                DeclarationHandle.Create(Prefix + "coprimality_is_necessary"),
                H("Coprimality is necessary for the cofactor reconstruction"),
                StatementSource.FromAuthor(CoprimalityNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At prime two, the exponent-zero observation and cofactor two are "
                        + "incompatible, exhibiting the missing coprimality hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-posterior-degeneracy"),
                DeclarationHandle.Create(Prefix + "restricted_zeta_posterior_at_unit"),
                H("The zero reading and unit cofactor specialize correctly"),
                StatementSource.FromAuthor(UnitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The k equals zero and m equals one specialization is an explicit "
                        + "degenerate audit of the single-prime posterior."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-observation-cannot-cover-all-primes"),
                DeclarationHandle.Create(Prefix + "no_finite_observation_contains_all_primes"),
                H("A finite observation cannot contain every prime"),
                StatementSource.FromAuthor(NoFiniteCoverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The all-primes observation is unavailable for a finite prime budget, "
                        + "so that proposed degeneration is excluded."))),
                DescribeRole.Theorem))));

    private static Formula EulerSplitFormula()
    {
        Formula s = F.Id("s"), p = F.Id("p");
        Formula premise = new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, s);
        Formula split = new Formula.Relation(
            Call("RestrictedZetaEulerProduct", s, p),
            FormulaRelationOperator.Equal,
            Call("RiemannZetaTimesRemovedPrimeFactor", s, p));
        return F.Disp(new Formula.Logic(premise, FormulaLogicOperator.Implies, split));
    }

    private static Formula SinglePosteriorFormula()
    {
        Formula s = F.Id("s"), p = F.Id("p"), k = F.Id("k"), m = F.Id("m");
        Formula premise = new Formula.Logic(
            new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, s),
            FormulaLogicOperator.And,
            Call("Coprime", m, p));
        Formula lhs = Call("ConditionalMass", Call("ZetaLaw", s),
            Call("PrimeObservation", p, k), Call("Cofactor", p, k, m));
        Formula rhs = new Formula.Fraction(
            Call("Weight", s, m), Call("RestrictedZetaPartition", s, p));
        return F.Disp(new Formula.Logic(
            premise, FormulaLogicOperator.Implies,
            new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs)));
    }

    private static Formula EmptyObservationFormula()
    {
        Formula s = F.Id("s"), m = F.Id("m");
        Formula premise = new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, s);
        Formula equality = new Formula.Relation(
            Call("ConditionalMass", Call("ZetaLaw", s), Call("EmptyObservation"),
                Call("Singleton", m)),
            FormulaRelationOperator.Equal,
            new Formula.Fraction(Call("Weight", s, m), Call("Partition", s)));
        return F.Disp(new Formula.Logic(premise, FormulaLogicOperator.Implies, equality));
    }

    private static Formula ZeroCofactorFormula()
    {
        Formula s = F.Id("s"), p = F.Id("p"), k = F.Id("k");
        Formula premise = new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, s);
        Formula equality = new Formula.Relation(
            Call("ConditionalMass", Call("ZetaLaw", s), Call("PrimeObservation", p, k),
                Call("ZeroCofactor", p, k)),
            FormulaRelationOperator.Equal, F.D(0));
        return F.Disp(new Formula.Logic(premise, FormulaLogicOperator.Implies, equality));
    }

    private static Formula PartitionNonzeroFormula()
    {
        Formula s = F.Id("s"), p = F.Id("p");
        Formula premise = new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, s);
        Formula conclusion = new Formula.Relation(
            Call("RestrictedZetaPartition", s, p), FormulaRelationOperator.NotEqual, F.D(0));
        return F.Disp(new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula ExponentNecessaryFormula() =>
        F.Disp(new Formula.Relation(
            Call("Partition", F.D(1)), FormulaRelationOperator.Equal, Infty));

    private static Formula CoprimalityNecessaryFormula() =>
        F.Disp(new Formula.Relation(
            Call("PrimeObservationCofactorIntersection", F.D(2), F.D(0), F.D(2)),
            FormulaRelationOperator.Equal, Call("EmptySet")));

    private static Formula UnitFormula()
    {
        Formula s = F.Id("s"), p = F.Id("p");
        Formula premise = new Formula.Relation(F.D(1), FormulaRelationOperator.LessThan, s);
        Formula equality = new Formula.Relation(
            Call("ConditionalMass", Call("ZetaLaw", s), Call("PrimeObservation", p, F.D(0)),
                Call("Cofactor", p, F.D(0), F.D(1))),
            FormulaRelationOperator.Equal,
            new Formula.Fraction(Call("Weight", s, F.D(1)),
                Call("RestrictedZetaPartition", s, p)));
        return F.Disp(new Formula.Logic(premise, FormulaLogicOperator.Implies, equality));
    }

    private static Formula NoFiniteCoverFormula() =>
        F.Disp(new Formula.Not(Call("FinitePrimeSetContainsAllPrimes")));
}
