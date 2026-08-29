using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class RobustMinimaxKernelBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Robust policies, set-valued beliefs, and common-kernel binary risk bounds.",
        H("Robust Minimax Kernel Bound"),
        Blocks(
            Definition(
                "worst-case-cost-definition",
                "worstCaseCost",
                "Worst-case model cost",
                WorstCaseCostFormula(),
                "The source cost J_M is specialized to an extended nonnegative cost. The "
                    + "worst-case cost is its supremum over the supplied model set; the "
                    + "empty supremum is zero."),
            Definition(
                "minimax-policies-definition",
                "minimaxPolicies",
                "Minimax policies",
                MinimaxPoliciesFormula(),
                "This named set is exactly argmin over policies of the model-wise supremum. "
                    + "It records exact minimizers without asserting that one exists."),
            Definition(
                "robust-belief-update-definition",
                "robustBeliefUpdate",
                "Distributionally robust belief update",
                RobustBeliefFormula(),
                "The probability-law carrier is Mathlib PMF, the faithful discrete version "
                    + "of P(X). The update contains every Bayes update of every current PMF "
                    + "under every allowed model."),
            Definition(
                "binary-error-definition",
                "binaryError",
                "Binary zero-one error",
                BinaryErrorFormula(),
                "For a Boolean truth, zero-one error is the PMF mass on the opposite label."),
            Definition(
                "fragility-witness-channel-definition",
                "fragilityWitnessChannel",
                "A fragile and a robust interface",
                FragilityChannelFormula(),
                "The false interface separates states only in the nominal model and changes "
                    + "by at most 1/1000 under misspecification. The true interface reports "
                    + "the state in both models."),
            Definition(
                "fragility-blind-risk-definition",
                "fragilityBlindRisk",
                "Adversarial blind risk",
                BlindRiskFormula(),
                "The concrete zero-one design cost is one exactly when an interface is blind "
                    + "to the two states under the selected model, and zero otherwise."),
            Definition(
                "separated-dirac-classifier-definition",
                "separatedDiracClassifier",
                "Classifier for the necessity audits",
                DiracClassifierFormula(),
                "This law-level classifier distinguishes the two Boolean Dirac transcript laws."),
            Theorem(
                "fragile-interface-not-minimax",
                "fragile_interface_not_minimax",
                "A small channel perturbation defeats the nominal interface",
                FragileWitnessFormula(),
                "Exact nominal separability replaces mutual information in this witness. A "
                    + "1/1000 response perturbation makes the fragile interface blind, while "
                    + "the robust interface remains separating and has lower worst-case cost. "
                    + "Primality is unused: prime is only the source's interface name."),
            Theorem(
                "common-kernel-minimax-lower-bounds",
                "common_kernel_minimax_lower_bounds",
                "A common transcript kernel forces both binary lower bounds",
                CommonKernelBoundsFormula(),
                "The imported factorization theorem first makes the complete transcript laws "
                    + "equal on the common interface fiber. Congruence then gives the same "
                    + "classifier-output PMF. Its complementary Boolean masses sum to one, "
                    + "yielding max error at least 1/2 and Bayes risk at least min(a,1-a). "
                    + "The classifier is any function of the transcript law, which also covers "
                    + "deterministic and randomized final classifiers."),
            Theorem(
                "transcript-factorization-is-necessary-for-lower-bound",
                "transcript_factorization_is_necessary_for_lower_bound",
                "Transcript factorization is necessary",
                FactorizationNecessaryFormula(),
                "A constant interface has equal values at false and true, but the two Dirac "
                    + "transcript laws do not factor through it. The named classifier is perfect, "
                    + "so the one-half conclusion is false without factorization."),
            Theorem(
                "same-fiber-is-necessary-for-lower-bound",
                "same_fiber_is_necessary_for_lower_bound",
                "The common-fiber premise is necessary",
                SameFiberNecessaryFormula(),
                "The identity interface supports the factorized state-recording Dirac law, but "
                    + "false and true lie in different fibers and are classified without error."),
            Theorem(
                "distinct-states-is-necessary-for-lower-bound",
                "distinct_states_is_necessary_for_lower_bound",
                "Distinct states are necessary",
                DistinctNecessaryFormula(),
                "At x equal to y equal to false, a constant transcript and constant correct "
                    + "classifier satisfy factorization and same-fiber equality but have zero "
                    + "error, contradicting a one-half bound."))));

    private static DocumentBlock Definition(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation) =>
        Describe.Lean(
            DescribeId.Create(id),
            Handle(declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Definition);

    private static DocumentBlock Theorem(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation) =>
        Describe.Lean(
            DescribeId.Create(id),
            Handle(declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);

    private static Formula WorstCaseCostFormula()
    {
        Formula models = F.Id("models");
        Formula cost = F.Id("J");
        Formula policy = F.Id("pi");
        return Disp(Equal(
            Call("worstCaseCost", models, cost, policy),
            Call("supModelCost", models, cost, policy)));
    }

    private static Formula MinimaxPoliciesFormula()
    {
        Formula models = F.Id("models");
        Formula cost = F.Id("J");
        return Disp(Equal(
            Call("minimaxPolicies", models, cost),
            Call("argminWorstCaseCost", models, cost)));
    }

    private static Formula RobustBeliefFormula()
    {
        Formula model = F.Id("M");
        Formula prior = F.Id("pi");
        Formula models = F.Id("models");
        Formula beliefs = F.Id("B");
        Formula pair = Call("pair", prior, model);
        Formula domain = Call("product", beliefs, models);
        Formula posterior = Call("BayesUpdate", F.Id("i"), model, prior, F.Id("y"));
        return Disp(Equal(
            Call("robustBeliefUpdate", models, beliefs, F.Id("i"), F.Id("y")),
            new Formula.SetBuilder(posterior, pair, domain)));
    }

    private static Formula BinaryErrorFormula()
    {
        Formula law = F.Id("mu");
        Formula truth = F.Id("x");
        return Disp(Equal(
            Call("binaryError", law, truth),
            Call("mass", law, Call("not", truth))));
    }

    private static Formula FragilityChannelFormula()
    {
        Formula fragile = Call("channel", F.Id("fragile"), F.Id("nominal"), F.Id("x"));
        Formula robust = Call("channel", F.Id("robust"), F.Id("M"), F.Id("x"));
        return Disp(new Formula.Logic(
            Equal(
                fragile,
                Call("scaledBit", Fraction(D(1), D(1, 0, 0, 0)), F.Id("x"))),
            FormulaLogicOperator.And,
            Equal(robust, Call("bit", F.Id("x")))));
    }

    private static Formula BlindRiskFormula()
    {
        Formula interfaceId = F.Id("i");
        Formula model = F.Id("M");
        Formula blind = Equal(
            Call("channel", interfaceId, model, F.Id("false")),
            Call("channel", interfaceId, model, F.Id("true")));
        return Disp(Equal(
            Call("fragilityBlindRisk", interfaceId, model),
            Call("indicator", blind)));
    }

    private static Formula DiracClassifierFormula()
    {
        return Disp(new Formula.Logic(
            Equal(Call("classify", Call("dirac", F.Id("false"))), F.Id("false")),
            FormulaLogicOperator.And,
            Equal(Call("classify", Call("dirac", F.Id("true"))), F.Id("true"))));
    }

    private static Formula FragileWitnessFormula()
    {
        Formula small = Call("sensitivityAtMost", Fraction(D(1), D(1, 0, 0, 0)));
        Formula nominal = Call("separates", F.Id("fragile"), F.Id("nominal"));
        Formula perturbed = new Formula.Not(
            Call("separates", F.Id("fragile"), F.Id("perturbed")));
        Formula robust = Call("separatesEveryModel", F.Id("robust"));
        Formula notMinimax = new Formula.Not(
            Call("minimaxPolicies", F.Id("fragile")));
        return Disp(And(small, And(nominal, And(perturbed, And(robust, notMinimax)))));
    }

    private static Formula CommonKernelBoundsFormula()
    {
        Formula a = F.Id("a");
        Formula errorX = F.Id("errorX");
        Formula errorY = F.Id("errorY");
        Formula maxBound = Relation(
            Fraction(D(1), D(2)),
            FormulaRelationOperator.LessThanOrEqual,
            Call("max", errorX, errorY));
        Formula weightedRisk = Add(
            Multiply(a, errorX),
            Multiply(Subtract(D(1), a), errorY));
        Formula bayesBound = Relation(
            Call("min", a, Subtract(D(1), a)),
            FormulaRelationOperator.LessThanOrEqual,
            weightedRisk);
        Formula premises = And(
            Call("KernelFactorsThrough", F.Id("q"), F.Id("K")),
            And(
                Equal(Call("q", F.Id("x")), Call("q", F.Id("y"))),
                NotEqual(F.Id("x"), F.Id("y"))));
        return Disp(new Formula.Logic(
            premises,
            FormulaLogicOperator.Implies,
            And(maxBound, bayesBound)));
    }

    private static Formula FactorizationNecessaryFormula()
    {
        Formula sameFiber = Equal(
            Call("booleanInterface", F.Id("false")),
            Call("booleanInterface", F.Id("true")));
        Formula noFactor = new Formula.Not(Call(
            "KernelFactorsThrough",
            F.Id("booleanInterface"),
            F.Id("distinguishingBooleanTranscriptKernel")));
        return Disp(And(sameFiber, And(noFactor, Equal(Call("maxError"), D(0)))));
    }

    private static Formula SameFiberNecessaryFormula()
    {
        Formula factors = Call(
            "KernelFactorsThrough",
            F.Id("id"),
            F.Id("distinguishingBooleanTranscriptKernel"));
        Formula differentFibers = NotEqual(
            Call("id", F.Id("false")),
            Call("id", F.Id("true")));
        return Disp(And(factors, And(differentFibers, Equal(Call("maxError"), D(0)))));
    }

    private static Formula DistinctNecessaryFormula()
    {
        Formula factors = Call(
            "KernelFactorsThrough",
            F.Id("booleanInterface"),
            F.Id("constantBooleanTranscriptKernel"));
        Formula sameState = Equal(F.Id("x"), F.Id("y"));
        return Disp(And(factors, And(sameState, Equal(Call("maxError"), D(0)))));
    }

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create(Prefix + declaration);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator relation,
        Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
