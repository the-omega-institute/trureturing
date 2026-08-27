using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ExperimentCost;

internal sealed class BlackwellCostOrthogonalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Blackwell dominance orders decision information but imposes no order on an "
            + "independently assigned nonnegative implementation cost.",
        H("Blackwell Order and External Cost"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("blackwell-dominance-can-have-higher-cost"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality."
                        + "exists_blackwell_dominance_with_higher_cost"),
                H("Blackwell dominance can have higher cost"),
                StatementSource.FromAuthor(CostWitnessFormula(Gt)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Implementation cost is a named function from experiment kernels "
                            + "to nonnegative reals, with no compatibility axiom connecting "
                            + "it to Blackwell dominance.")),
                    Paragraph(Text(
                        "The Boolean identity experiment Blackwell-dominates the constant "
                            + "erasure experiment. They are distinct, and assigning costs one "
                            + "and zero respectively gives the strict higher-cost direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("blackwell-dominance-can-have-lower-cost"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality."
                        + "exists_blackwell_dominance_with_lower_cost"),
                H("Blackwell dominance can have lower cost"),
                StatementSource.FromAuthor(CostWitnessFormula(Lt)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the same distinct Boolean experiment pair, reversing the two "
                            + "assigned costs makes the dominating experiment strictly cheaper.")),
                    Paragraph(Text(
                        "Together with the higher-cost witness, this shows that Blackwell "
                            + "dominance alone determines neither strict cost direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-experiments-have-equal-cost"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality."
                        + "equal_experiments_have_equal_cost"),
                H("Equal experiments have equal cost"),
                StatementSource.FromAuthor(EqualExperimentsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Because an external cost assignment is still a function, equal "
                            + "kernels must receive equal values by congruence.")),
                    Paragraph(Text(
                        "Thus reflexive Blackwell dominance is not itself a strict-cost "
                            + "witness; the two existence theorems deliberately use distinct "
                            + "identity and erasure kernels."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-cost-cannot-strictly-compare"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality."
                        + "constant_experiment_cost_cannot_strictly_compare"),
                H("Constant cost cannot strictly compare experiments"),
                StatementSource.FromAuthor(ConstantCostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A constant assignment gives the same nonnegative value to every "
                            + "kernel, so neither strict comparison can hold for any pair.")),
                    Paragraph(Text(
                        "Accordingly the concrete existence witnesses use nonconstant cost "
                            + "functions; their strict inequalities carry that requirement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-boolean-experiments-are-equivalent"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality."
                        + "constant_boolean_experiments_are_blackwell_equivalent"),
                H("Constant Boolean experiments are Blackwell-equivalent"),
                StatementSource.FromAuthor(ConstantExperimentsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The always-false and always-true Boolean experiments can each be "
                            + "obtained from the other by constant deterministic processing.")),
                    Paragraph(Text(
                        "This verifies the fully uninformative degenerate case directly and "
                            + "shows that mutual dominance supplies no external cost order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("blackwell-dominance-still-compares-bayes-risk"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality."
                        + "blackwell_dominance_still_compares_bayes_risk"),
                H("Blackwell dominance still compares Bayes risk"),
                StatementSource.FromAuthor(BayesRiskFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every extended-nonnegative loss and prior measure, a dominating "
                            + "experiment has no larger optimal Bayes risk.")),
                    Paragraph(Text(
                        "This is a direct application of the established Blackwell theorem. "
                            + "Only the unrelated external cost comparison is unconstrained."))),
                DescribeRole.Theorem))));

    private static Formula CostWitnessFormula(Formula comparison)
    {
        Formula boolean = F.Id("Bool");
        Formula kernel = Call("Kernel", boolean, boolean);
        Formula first = F.Id("P");
        Formula second = F.Id("Q");
        Formula cost = F.Id("cost");

        return Disp(Seq(
            Exists, Sp, first, Comma, Sp, second, Colon, Sp, kernel, Comma, Sp,
            cost, Colon, Sp, Call("ExperimentCost", boolean, boolean), Comma, RowBreak,
            Grp(), first, Sp, Neq, Sp, second, Sp, Land, Sp,
            Dominates(first, second), Sp, Land, Sp,
            Apply(cost, first), Sp, comparison, Sp, Apply(cost, second), Dot));
    }

    private static Formula EqualExperimentsFormula()
    {
        Formula parameter = Theta;
        Formula observation = F.Id("X");
        Formula first = F.Id("P");
        Formula second = F.Id("Q");
        Formula cost = F.Id("cost");

        return Disp(Seq(
            Forall, Sp, parameter, Comma, Sp, observation, Comma, Sp,
            cost, Colon, Sp, Call("ExperimentCost", parameter, observation), Comma,
            RowBreak, Grp(), first, Comma, Sp, second, Colon, Sp,
            Call("Kernel", parameter, observation), Comma, Sp,
            first, Sp, Eq, Sp, second, Sp, Rightarrow, Sp,
            Apply(cost, first), Sp, Eq, Sp, Apply(cost, second), Dot));
    }

    private static Formula ConstantCostFormula()
    {
        Formula parameter = Theta;
        Formula observation = F.Id("X");
        Formula first = F.Id("P");
        Formula second = F.Id("Q");
        Formula value = F.Id("c");
        Formula constantCost = Call("constCost", value);

        return Disp(Seq(
            Forall, Sp, parameter, Comma, Sp, observation, Comma, Sp,
            value, Colon, Sp, NonnegativeReal(), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp,
            Call("Kernel", parameter, observation), Comma, RowBreak, Grp(),
            Neg, Grp(Apply(constantCost, first), Sp, Gt, Sp,
                Apply(constantCost, second)), Sp, Land, Sp,
            Neg, Grp(Apply(constantCost, first), Sp, Lt, Sp,
                Apply(constantCost, second)), Dot));
    }

    private static Formula ConstantExperimentsFormula()
    {
        Formula zeroKernel = new Formula.Subscript(F.Id("K"), D(0));
        Formula oneKernel = new Formula.Subscript(F.Id("K"), D(1));

        return Disp(Seq(
            Dominates(zeroKernel, oneKernel), Sp, Land, Sp,
            Dominates(oneKernel, zeroKernel), Dot));
    }

    private static Formula BayesRiskFormula()
    {
        Formula parameter = Theta;
        Formula observation = F.Id("X");
        Formula output = new Formula.Subscript(F.Id("X"), D(1));
        Formula decision = F.Id("Y");
        Formula first = F.Id("P");
        Formula second = F.Id("Q");
        Formula loss = Ell;
        Formula prior = Pi;

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, first, Colon, Sp, Call("Kernel", parameter, observation),
            Comma, Sp, second, Colon, Sp, Call("Kernel", parameter, output), Comma,
            RowBreak, Grp(), Dominates(first, second), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, loss, Colon, Sp, parameter, Sp, To, Sp, decision, Sp, To, Sp,
            F.Id("ENNReal"), Comma, Sp, prior, Colon, Sp, Call("Measure", parameter),
            Comma, RowBreak, Grp(), BayesRisk(loss, first, prior), Sp, Leq, Sp,
            BayesRisk(loss, second, prior), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula NonnegativeReal() =>
        Seq(Mathbb, Grp(F.Id("R")), Underscore, Grp(Geq, Sp, D(0)));

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Dominates(Formula first, Formula second) =>
        Call("BlackwellDominates", first, second);

    private static Formula BayesRisk(Formula loss, Formula experiment, Formula prior) =>
        Call("bayesRisk", loss, experiment, prior);
}
