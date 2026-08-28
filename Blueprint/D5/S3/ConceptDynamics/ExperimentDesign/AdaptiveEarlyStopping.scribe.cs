using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class AdaptiveEarlyStoppingDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ExperimentDesign/AdaptiveEarlyStopping.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive stopping has expectation one plus the residual-model probability, with "
            + "explicit zero- and unit-error boundary cases.",
        H("Adaptive Early Stopping"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("error-probability-nonnegative"),
                DeclarationHandle.Create(Prefix + "error_probability_nonnegative"),
                H("The residual probability is nonnegative"),
                StatementSource.FromAuthor(NonnegativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both residual model masses are nonnegative because the prior is a PMF. "
                        + "Their prescribed sum alone forces epsilon to be nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("expected-experiment-count-eq-one-add"),
                DeclarationHandle.Create(Prefix + "expected_experiment_count_eq_one_add"),
                H("The expected execution count is one plus epsilon"),
                StatementSource.FromAuthor(ExpectationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first experiment stops immediately only under M_XY. The execution "
                            + "count is one there and two under either residual model.")),
                    Paragraph(Text(
                        "The two residual masses enter only through their sum epsilon. Hence the "
                            + "finite PMF-weighted sum is (1-epsilon)+2 epsilon=1+epsilon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("expected-experiment-count-lt-two"),
                DeclarationHandle.Create(Prefix + "expected_experiment_count_lt_two"),
                H("Positive immediate-stop mass gives a strict saving"),
                StatementSource.FromAuthor(StrictFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Substituting the exact expectation reduces the strict comparison with two "
                        + "to the explicit hypothesis epsilon < 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-error-probability-expected-count"),
                DeclarationHandle.Create(Prefix + "zero_error_probability_expected_count"),
                H("Zero error mass executes one experiment"),
                StatementSource.FromAuthor(ZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The point mass at M_XY satisfies the adaptive prior condition with epsilon "
                        + "zero and makes the execution count identically one on its support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("error-probability-lt-one-is-necessary"),
                DeclarationHandle.Create(Prefix + "error_probability_lt_one_is_necessary"),
                H("The strict epsilon hypothesis is necessary"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At epsilon one, the point mass at M_0 satisfies the prior premise and has "
                        + "expected count two. The claimed strict inequality is false."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("extreme-remaining-allocations-same-expectation"),
                DeclarationHandle.Create(
                    Prefix + "extreme_remaining_allocations_same_expectation"),
                H("Extreme residual allocations have the same expectation"),
                StatementSource.FromAuthor(ExtremeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Concentrating all residual mass on M_0 or all of it on M_YX gives expectation "
                        + "two in both cases, confirming that the internal split is irrelevant."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(clause);
        }
        return Seq([.. items]);
    }

    private static Formula PriorType() =>
        Call("PMF", Call("Fin", D(3)));

    private static Formula RealType() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Adaptive(Formula prior, Formula epsilon) =>
        Call("IsAdaptivePrior", prior, epsilon);

    private static Formula Expected(Formula prior) =>
        Call("expectedExperimentCount", prior);

    private static Formula Mass(Formula prior, Formula model) =>
        Call("toReal", Apply(prior, model));

    private static Formula RemainingMass(Formula prior) =>
        Seq(Mass(prior, ModelZero()), Sp, Plus, Sp, Mass(prior, ModelYX()));

    private static Formula Pure(Formula model) =>
        Call("pure", model);

    private static Formula ModelXY() =>
        new Formula.Subscript(F.Id("M"), F.Id("XY"));

    private static Formula ModelZero() =>
        new Formula.Subscript(F.Id("M"), D(0));

    private static Formula ModelYX() =>
        new Formula.Subscript(F.Id("M"), F.Id("YX"));

    private static Formula NonnegativeFormula()
    {
        Formula prior = F.Id("p");
        Formula epsilon = F.Id("epsilon");
        return Disp(Seq(
            Forall, Sp, Typed(prior, PriorType()), Comma, Sp,
            Typed(epsilon, RealType()), Comma, Sp,
            RemainingMass(prior), Sp, Eq, Sp, epsilon, Sp, Rightarrow, Sp,
            D(0), Sp, Leq, Sp, epsilon, Dot));
    }

    private static Formula ExpectationFormula()
    {
        Formula prior = F.Id("p");
        Formula epsilon = F.Id("epsilon");
        return Disp(Seq(
            Forall, Sp, Typed(prior, PriorType()), Comma, Sp,
            Typed(epsilon, RealType()), Comma, Sp,
            Adaptive(prior, epsilon), Sp, Rightarrow, Sp,
            Expected(prior), Sp, Eq, Sp, D(1), Sp, Plus, Sp, epsilon, Dot));
    }

    private static Formula StrictFormula()
    {
        Formula prior = F.Id("p");
        Formula epsilon = F.Id("epsilon");
        Formula premises = And(
            Adaptive(prior, epsilon),
            Seq(epsilon, Sp, Lt, Sp, D(1)));
        return Disp(Seq(
            Forall, Sp, Typed(prior, PriorType()), Comma, Sp,
            Typed(epsilon, RealType()), Comma, Sp,
            premises, Sp, Rightarrow, Sp,
            Expected(prior), Sp, Lt, Sp, D(2), Dot));
    }

    private static Formula ZeroFormula()
    {
        Formula prior = Pure(ModelXY());
        return Disp(Seq(
            Adaptive(prior, D(0)), Sp, Land, Sp,
            Expected(prior), Sp, Eq, Sp, D(1), Dot));
    }

    private static Formula NecessityFormula()
    {
        Formula prior = Pure(ModelZero());
        return Disp(Seq(
            Adaptive(prior, D(1)), Sp, Land, Sp,
            Expected(prior), Sp, Eq, Sp, D(2), Sp, Land, Sp,
            Neg, Open, Expected(prior), Sp, Lt, Sp, D(2), Close, Dot));
    }

    private static Formula ExtremeFormula()
    {
        Formula priorZero = Pure(ModelZero());
        Formula priorReverse = Pure(ModelYX());
        return Disp(Seq(
            Adaptive(priorZero, D(1)), Sp, Land, Sp,
            Adaptive(priorReverse, D(1)), Sp, Land, Sp,
            Expected(priorZero), Sp, Eq, Sp, D(2), Sp, Land, Sp,
            Expected(priorReverse), Sp, Eq, Sp, D(2), Dot));
    }
}
