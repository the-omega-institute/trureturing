using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class MultiplicativeComplexityActivationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplicative complexity is a finite sum of independent prime occupations.",
        H("Multiplicative Complexity as a Random Activation Pattern"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("multiplicative-complexity-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "multiplicativeComplexity"),
                H("Multiplicative complexity counts prime factors with multiplicity"),
                StatementSource.FromAuthor(ComplexityDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The FPOD complexity of n is Mathlib's existing Omega arithmetic "
                        + "function. The wrapper names the source concept without creating a "
                        + "second prime-factor-count definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-occupation-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "primeOccupancy"),
                H("A prime mode is occupied by its factorization exponent"),
                StatementSource.FromAuthor(OccupancyDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime p, its occupation coordinate at n is the exponent of p in "
                        + "the finite prime factorization of n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("multiplicative-complexity-factorization-sum"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "multiplicativeComplexity_eq_factorization_sum"),
                H("Complexity is the sum of prime occupations"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact Mathlib decomposition of Omega is reused. Its Finsupp sum is "
                        + "over factorization support, so each fixed integer contributes only "
                        + "finitely many nonzero prime exponents."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("occupied-prime-modes-are-finite"),
                DeclarationHandle.Create(DeclarationPrefix + "occupied_prime_modes_finite"),
                H("Only finitely many prime modes are occupied"),
                StatementSource.FromAuthor(FiniteSupportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nonzero prime occupations form the preimage of the finite Finsupp "
                        + "support under the injective prime coercion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("multiplicative-complexity-degenerate-audit"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "multiplicative_complexity_degenerate_audit"),
                H("Zero, one, primes, and prime powers are explicit"),
                StatementSource.FromAuthor(ComplexityAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The totalized convention gives complexity zero to both zero and one. A "
                        + "prime has complexity one, and its kth power has complexity k, "
                        + "including k equal to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primality-is-necessary"),
                DeclarationHandle.Create(DeclarationPrefix + "primality_is_necessary"),
                H("The prime restriction cannot be deleted"),
                StatementSource.FromAuthor(PrimalityCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete nonprime base one has complexity zero rather than one, and "
                        + "its square has complexity zero rather than two. This names the "
                        + "counterexample required by the hypothesis audit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-occupation-has-geometric-law"),
                DeclarationHandle.Create(DeclarationPrefix + "prime_occupancy_geometric"),
                H("Each prime occupation is geometric"),
                StatementSource.FromAuthor(GeometricFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Above exponent one, the probability that the p-coordinate equals k is "
                        + "one minus p to the minus s, times p to the minus sk. This is a direct "
                        + "application of the existing prime-exponent law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-occupations-are-mutually-independent"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_occupancies_mutually_independent"),
                H("All prime occupations are mutually independent"),
                StatementSource.FromAuthor(IndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The full prime-indexed iIndepFun theorem is reused, so every finite "
                        + "subfamily factors, including the empty family and singletons. This "
                        + "is stronger than pairwise independence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-occupation-degenerate-audit"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "prime_occupancy_degenerate_audit"),
                H("A prime coordinate is nonconstant and nontrivial"),
                StatementSource.FromAuthor(OccupancyAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At zero and one the coordinate vanishes, while at its own prime it equals "
                        + "one. These values rule out the constant, identity, and zero-map "
                        + "degenerations for the actual coordinate family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mean-prime-occupation-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "meanPrimeOccupancy"),
                H("The geometric mean occupation has a closed form"),
                StatementSource.FromAuthor(MeanDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The local geometric mean is q divided by one minus q, with q equal to p "
                        + "to the minus s. Its probabilistic reading is restricted to the zeta "
                        + "range above one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mean-prime-occupations-are-summable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "mean_prime_occupancies_summable"),
                H("Mean occupations are summable above one"),
                StatementSource.FromAuthor(MeanSummabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every prime evidence q is at most one half, so q divided by one minus q "
                        + "is at most twice q. The existing sharp prime-evidence theorem then "
                        + "proves summability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mean-occupation-threshold-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "threshold_hypothesis_is_necessary"),
                H("Exponent one is a nonsummable counterexample"),
                StatementSource.FromAuthor(ThresholdCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At exponent one, each mean occupation dominates reciprocal-prime "
                            + "evidence, so the family is not summable.")),
                    Paragraph(Text(
                        "This is stated with Summable rather than a bare real tsum: the "
                            + "repository's totalized tsum is zero for nonsummable families.")),
                    Paragraph(Text(
                        "The warning that physical computation costs need not obey this law is "
                            + "interpretive, not a mathematical assertion. FPOD 136.1 instead "
                            + "adds log evidence; it does not imply these occupation results."))),
                DescribeRole.Theorem))));

    private static Formula ComplexityDefinitionFormula()
    {
        Formula n = F.Id("n");
        return F.Disp(Equal(Complexity(n), OmegaAt(n)));
    }

    private static Formula OccupancyDefinitionFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        return F.Disp(Equal(Occupancy(p, n), Valuation(p, n)));
    }

    private static Formula DecompositionFormula()
    {
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        return F.Disp(Equal(Complexity(n), SumPrimes(p, Occupancy(p, n))));
    }

    private static Formula FiniteSupportFormula()
    {
        Formula n = F.Id("n");
        return F.Disp(Call("Finite", Call("OccupiedPrimeModes", n)));
    }

    private static Formula ComplexityAuditFormula()
    {
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula primePower = new Formula.Power(p, F.Grp(k));
        return F.Disp(And(
            Equal(Complexity(F.D(0)), F.D(0)),
            And(
                Equal(Complexity(F.D(1)), F.D(0)),
                And(
                    Equal(Complexity(p), F.D(1)),
                    Equal(Complexity(primePower), k)))));
    }

    private static Formula PrimalityCounterexampleFormula()
    {
        Formula oneSquared = new Formula.Power(F.D(1), F.Grp(F.D(2)));
        return F.Disp(And(
            Not(Equal(Complexity(F.D(1)), F.D(1))),
            Not(Equal(Complexity(oneSquared), F.D(2)))));
    }

    private static Formula GeometricFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula q = new Formula.Power(p, F.Grp(F.Seq(F.Minus, s)));
        Formula kthMass = new Formula.Power(
            p,
            F.Grp(F.Seq(F.Minus, s, F.Sp, F.Cdot, F.Sp, k)));
        Formula mass = F.Seq(
            F.Grp(F.D(1), F.Sp, F.Minus, F.Sp, q),
            F.Sp, F.Cdot, F.Sp,
            kthMass);
        return F.Disp(Equal(
            Call("ProbabilityUnderZeta", s, Equal(Occupancy(p, F.Id("N")), k)),
            mass));
    }

    private static Formula IndependenceFormula()
    {
        Formula s = F.Id("s");
        Formula domain = new Formula.Relation(
            F.D(1), FormulaRelationOperator.LessThan, s);
        Formula conclusion = Call(
            "MutuallyIndependentUnderZeta",
            s,
            Call("PrimeOccupationFamily"));
        return F.Disp(new Formula.Logic(
            domain,
            FormulaLogicOperator.Implies,
            conclusion));
    }

    private static Formula OccupancyAuditFormula()
    {
        Formula p = F.Id("p");
        return F.Disp(And(
            Equal(Occupancy(p, F.D(0)), F.D(0)),
            And(
                Equal(Occupancy(p, F.D(1)), F.D(0)),
                Equal(Occupancy(p, p), F.D(1)))));
    }

    private static Formula MeanDefinitionFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula q = new Formula.Power(p, F.Grp(F.Seq(F.Minus, s)));
        return F.Disp(Equal(
            MeanOccupancy(s, p),
            new Formula.Fraction(q, F.Seq(F.D(1), F.Sp, F.Minus, F.Sp, q))));
    }

    private static Formula MeanSummabilityFormula()
    {
        Formula s = F.Id("s");
        Formula domain = new Formula.Relation(
            F.D(1), FormulaRelationOperator.LessThan, s);
        Formula family = F.Seq(
            F.Id("p"), F.Mapsto, F.Sp, MeanOccupancy(s, F.Id("p")));
        return F.Disp(new Formula.Logic(
            domain,
            FormulaLogicOperator.Implies,
            IsSummable(family)));
    }

    private static Formula ThresholdCounterexampleFormula()
    {
        Formula family = F.Seq(
            F.Id("p"), F.Mapsto, F.Sp, MeanOccupancy(F.D(1), F.Id("p")));
        return F.Disp(Not(IsSummable(family)));
    }

    private static Formula Complexity(Formula n) =>
        F.Seq(
            new Formula.Subscript(F.Id("C"), F.Times),
            F.Open, n, F.Close);

    private static Formula OmegaAt(Formula n) =>
        F.Seq(F.Omega, F.Open, n, F.Close);

    private static Formula Occupancy(Formula p, Formula n) =>
        F.Seq(
            new Formula.Subscript(F.Id("V"), p),
            F.Open, n, F.Close);

    private static Formula Valuation(Formula p, Formula n) =>
        F.Seq(
            new Formula.Subscript(F.Id("v"), p),
            F.Open, n, F.Close);

    private static Formula MeanOccupancy(Formula s, Formula p) =>
        F.Seq(
            new Formula.Subscript(F.Id("m"), p),
            F.Open, s, F.Close);

    private static Formula SumPrimes(Formula p, Formula term) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(p, F.InMacro, F.Sp, F.Mathbb, F.Grp(F.Id("P"))),
            F.Sp, term);

    private static Formula IsSummable(Formula family) =>
        new Formula.Apply(F.Id("Summable"), [family]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Not(Formula value) =>
        F.Seq(F.Neg, F.Sp, value);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
