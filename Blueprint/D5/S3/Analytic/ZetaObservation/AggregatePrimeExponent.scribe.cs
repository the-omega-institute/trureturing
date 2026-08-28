using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class AggregatePrimeExponentDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Aggregate prime exponents reconstruct nonzero samples and specialize to the "
            + "one-sample geometric law.",
        H("Aggregate Prime Exponents"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("aggregate-prime-exponent-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "aggregateExponent"),
                H("The aggregate exponent sums sample factorizations"),
                StatementSource.FromAuthor(AggregateDefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each natural base, the named statistic sums its factorization "
                        + "exponents across the finite sample."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sample-product-prime-power-product"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "sample_product_eq_prime_power_product"),
                H("Aggregate exponents reconstruct a nonzero sample product"),
                StatementSource.FromAuthor(ReconstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof reuses natural-number unique factorization. Nonzeroness is "
                        + "required because Mathlib totalizes the factorization of zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sample-nonzero-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "sample_nonzero_is_necessary"),
                H("A zero singleton is a reconstruction counterexample"),
                StatementSource.FromAuthor(ZeroCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the singleton sample containing zero, the sample product is zero "
                        + "while the product represented by its aggregate factorization is "
                        + "one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("aggregate-exponent-empty"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "aggregate_exponent_empty"),
                H("The empty sample has zero aggregate and product one"),
                StatementSource.FromAuthor(EmptySampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This records both degenerate identities without any probabilistic or "
                        + "nonzeroness assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("aggregate-exponent-singleton"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "aggregate_exponent_singleton"),
                H("A singleton aggregate is its sole factorization"),
                StatementSource.FromAuthor(SingletonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Summing over the one-element sample index leaves exactly the original "
                        + "factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("aggregate-exponent-one-cons"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "aggregate_exponent_one_cons"),
                H("Adjoining one leaves the aggregate unchanged"),
                StatementSource.FromAuthor(AdjoinOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The factorization of one is zero at every coordinate, so a sample value "
                        + "one contributes no exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("aggregate-exponent-singleton-law"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "aggregate_exponent_singleton_law"),
                H("The one-sample aggregate law is geometric"),
                StatementSource.FromAuthor(SingletonLawFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For exponent above one and a prime coordinate, the imported zeta "
                        + "factorization law gives the exact mass at every natural count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("aggregate-exponent-singleton-zero-mass"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "aggregate_exponent_singleton_zero_mass"),
                H("The one-sample zero mass is one minus the prime weight"),
                StatementSource.FromAuthor(ZeroMassFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Setting the count to zero in the geometric law removes the power-law "
                        + "occupation factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("aggregate-exponent-singleton-independence"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "aggregate_exponent_singleton_iIndep"),
                H("One-sample aggregate prime coordinates are mutually independent"),
                StatementSource.FromAuthor(SingletonIndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The family statement is exactly the repository's prime-factorization "
                        + "independence theorem after simplifying a singleton sum."))),
                DescribeRole.Theorem))));

    private static Formula AggregateDefinitionFormula()
    {
        Formula p = F.Id("p");
        Formula j = F.Id("j");
        Formula m = F.Id("m");
        Formula sample = F.Id("N");
        Formula summand = Call("V", p, Call("At", sample, j));
        Formula sum = F.Seq(
            F.Sum, F.Underscore,
            F.Grp(j, F.InMacro, F.Sp, Call("Fin", m)),
            F.Sp, summand);
        return F.Disp(Equal(Aggregate(p), sum));
    }

    private static Formula ReconstructionFormula()
    {
        Formula j = F.Id("j");
        Formula p = F.Id("p");
        Formula sampleProduct = IndexedProduct(j, Call("At", F.Id("N"), j));
        Formula primeProduct = IndexedProduct(
            p,
            new Formula.Power(p, F.Grp(Aggregate(p))));
        return F.Disp(Equal(sampleProduct, primeProduct));
    }

    private static Formula ZeroCounterexampleFormula()
    {
        Formula left = IndexedProduct(F.Id("j"), F.D(0));
        Formula right = IndexedProduct(
            F.Id("p"),
            new Formula.Power(F.Id("p"), F.Grp(Aggregate(F.Id("p")))));
        return F.Disp(Not(Equal(left, right)));
    }

    private static Formula EmptySampleFormula()
    {
        Formula aggregateZero = Equal(Call("Aggregate", Call("EmptySample")), F.D(0));
        Formula productOne = Equal(Call("Product", Call("EmptySample")), F.D(1));
        return F.Disp(And(aggregateZero, productOne));
    }

    private static Formula SingletonFormula()
    {
        Formula n = F.Id("n");
        return F.Disp(Equal(
            Call("Aggregate", Call("Singleton", n)),
            Call("Factorization", n)));
    }

    private static Formula AdjoinOneFormula()
    {
        Formula sample = F.Id("N");
        return F.Disp(Equal(
            Call("Aggregate", Call("Cons", F.D(1), sample)),
            Call("Aggregate", sample)));
    }

    private static Formula SingletonLawFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula c = F.Id("c");
        Formula primeWeight = new Formula.Power(p, F.Grp(F.Seq(F.Minus, s)));
        Formula occupiedWeight = new Formula.Power(
            p,
            F.Grp(F.Seq(F.Minus, c, F.Sp, F.Cdot, F.Sp, s)));
        Formula mass = F.Seq(
            F.Grp(F.D(1), F.Sp, F.Minus, F.Sp, primeWeight),
            F.Sp, F.Cdot, F.Sp,
            occupiedWeight);
        return F.Disp(Equal(Call("Probability", Equal(Aggregate(p), c)), mass));
    }

    private static Formula ZeroMassFormula()
    {
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula primeWeight = new Formula.Power(p, F.Grp(F.Seq(F.Minus, s)));
        Formula mass = F.Seq(F.D(1), F.Sp, F.Minus, F.Sp, primeWeight);
        return F.Disp(Equal(Call("Probability", Equal(Aggregate(p), F.D(0))), mass));
    }

    private static Formula SingletonIndependenceFormula()
    {
        Formula p = F.Id("p");
        Formula family = F.Seq(p, F.Mapsto, F.Sp, Aggregate(p));
        return F.Disp(Call("MutuallyIndependent", family));
    }

    private static Formula Aggregate(Formula p) =>
        Call("AggregateExponent", p);

    private static Formula IndexedProduct(Formula index, Formula term) =>
        F.Seq(F.Prod, F.Underscore, F.Grp(index), F.Sp, term);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Not(Formula formula) =>
        F.Seq(F.Neg, F.Sp, formula);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
