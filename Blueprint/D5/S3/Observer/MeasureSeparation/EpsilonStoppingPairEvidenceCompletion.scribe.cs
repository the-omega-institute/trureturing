using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class EpsilonStoppingPairEvidenceCompletionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/MeasureSeparation/EpsilonStoppingPairEvidenceCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Epsilon stopping and pair evidence yield a common classifier under a named dichotomy.",
        H("Epsilon Stopping and Pair-Evidence Completion"),
        Blocks(
            Definition(
                "posterior-error-definition",
                "posteriorError",
                "Posterior MAP error",
                PosteriorErrorFormula(),
                "The error is one minus the supremum posterior mass. On a finite nonempty "
                    + "state type, this supremum is the maximum in Definition 250.1."),
            Definition(
                "epsilon-stopping-time-definition",
                "epsilonStoppingTime",
                "Epsilon-completion stopping time",
                EpsilonStoppingFormula(),
                "The first threshold-hitting natural time is returned. Infinity explicitly "
                    + "records an empty threshold set."),
            Definition(
                "measure-affinity-definition",
                "MeasureAffinity",
                "Abstract measure affinity",
                MeasureAffinityFormula(),
                "This is the named abstract interface used because pinned Mathlib has no "
                    + "measure-level Hellinger affinity. Hellinger affinity is an intended "
                    + "instance, not constructed here."),
            Definition(
                "open-loop-pair-evidence-definition",
                "openLoopPairEvidence",
                "Open-loop pair evidence",
                OpenLoopEvidenceFormula(),
                "The experiment sequence is fixed, and evidence is summed with the repository "
                    + "convention H squared equals twice one minus affinity."),
            Definition(
                "open-loop-local-equivalence-definition",
                "OpenLoopLocallyEquivalent",
                "Selected local laws are equivalent",
                LocalEquivalenceFormula(),
                "At every selected coordinate, the laws for each distinct state pair are "
                    + "mutually absolutely continuous."),
            Definition(
                "open-loop-evidence-dichotomy-definition",
                "OpenLoopEvidenceDichotomy",
                "Named evidence-to-singularity bridge",
                DichotomyFormula(),
                "This packages the missing Kakutani implication as an explicit premise. It does "
                    + "not claim a product-measure dichotomy from pinned Mathlib."),
            Definition(
                "common-zero-error-classifier-definition",
                "HasCommonZeroErrorClassifier",
                "Common zero-error decision regions",
                ClassifierFormula(),
                "A classifier is represented by measurable pairwise disjoint regions whose "
                    + "complements are null under their corresponding transcript laws."),
            Definition(
                "negative-log-affinity-definition",
                "negativeLogAffinity",
                "Extended negative log affinity",
                NegativeLogFormula(),
                "The extended nonnegative value is infinite at zero. Values above one truncate "
                    + "to zero; intended normalized affinities lie in the unit interval."),
            Definition(
                "conditional-affinity-definition",
                "conditionalAffinity",
                "History-conditional affinity",
                ConditionalAffinityFormula(),
                "At time t, the common history is fed to the policy and the selected local laws "
                    + "are compared by the abstract affinity."),
            Definition(
                "predictable-evidence-process-definition",
                "predictableEvidenceProcess",
                "Predictable evidence process",
                PredictableEvidenceFormula(),
                "Evidence before n is the finite sum of negative log conditional affinities "
                    + "along the common-history process."),
            Theorem(
                "epsilon-stopping-time-top-iff",
                "epsilon_stopping_time_eq_top_iff",
                "Infinite stopping exactly means no threshold hit",
                StoppingTopFormula(),
                "This records the empty threshold-set behavior explicitly."),
            Theorem(
                "epsilon-stopping-time-zero-of-initial",
                "epsilon_stopping_time_eq_zero_of_initial",
                "An initial threshold hit stops at zero",
                InitialStopFormula(),
                "Natural-number minimality makes time zero the first hit."),
            Theorem(
                "epsilon-one-stops-immediately",
                "epsilon_one_stops_immediately",
                "Threshold one stops immediately",
                EpsilonOneFormula(),
                "Posterior error is always at most one."),
            Theorem(
                "posterior-error-singleton",
                "posterior_error_singleton",
                "Singleton posterior error is zero",
                SingletonErrorFormula(),
                "The only state has posterior mass one."),
            Theorem(
                "singleton-state-stops-immediately",
                "singleton_state_stops_immediately",
                "A singleton state space stops immediately",
                SingletonStopFormula(),
                "Zero posterior error meets every extended nonnegative threshold at time zero."),
            Theorem(
                "empty-state-has-no-posterior",
                "empty_state_has_no_posterior",
                "The empty state type has no posterior",
                EmptyPosteriorFormula(),
                "A probability mass function cannot normalize on an empty type."),
            Theorem(
                "zero-threshold-may-never-stop",
                "zero_threshold_may_never_stop",
                "A zero threshold may never be reached",
                ZeroThresholdFormula(),
                "The constant fair Boolean posterior has strictly positive error forever."),
            Theorem(
                "singleton-pair-evidence-condition-vacuous",
                "singleton_pair_evidence_condition_vacuous",
                "Singleton pair evidence is vacuous",
                SingletonPairFormula(),
                "There are no distinct state pairs on Unit."),
            Theorem(
                "finite-pairwise-singular-common-classifier",
                "finite_pairwise_singular_common_zero_error_classifier",
                "Finite singular laws admit one common classifier",
                FiniteClassifierFormula(),
                "Canonical measurable refinement turns finite pairwise singular separators into "
                    + "pairwise disjoint conull decision regions."),
            Theorem(
                "open-loop-finite-state-completion",
                "open_loop_finite_state_completion",
                "Open-loop completion under the named dichotomy",
                CompletionFormula(),
                "Local equivalence and divergent pair evidence feed the explicit dichotomy. "
                    + "Finite pairwise singularity then yields a common zero-error classifier."),
            Theorem(
                "evidence-dichotomy-is-necessary",
                "evidence_dichotomy_is_necessary",
                "The abstract setting needs a dichotomy premise",
                DichotomyNecessaryFormula(),
                "Constant zero affinity makes all evidence infinite while identical Dirac "
                    + "transcript laws remain nonsingular."),
            Theorem(
                "negative-log-affinity-zero",
                "negative_log_affinity_zero",
                "Zero affinity has infinite evidence",
                NegativeLogZeroFormula(),
                "The extended logarithm sends zero affinity to infinite negative-log evidence."),
            Theorem(
                "predictable-evidence-zero",
                "predictable_evidence_zero",
                "Predictable evidence starts at zero",
                EvidenceZeroFormula(),
                "The finite sum before time zero has no terms."))));

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

    private static Formula PosteriorErrorFormula() =>
        Disp(Equal(
            Call("posteriorError", F.Id("pi")),
            Subtract(D(1), Call("supPosteriorMass", F.Id("pi")))));

    private static Formula EpsilonStoppingFormula() =>
        Disp(Equal(
            Call("epsilonStoppingTime", F.Id("epsilon"), F.Id("pi")),
            Call("firstOrInfinity", Call("errorAtMost", F.Id("pi"), F.Id("epsilon")))));

    private static Formula MeasureAffinityFormula() =>
        Disp(Equal(
            Call("MeasureAffinity", F.Id("Omega")),
            Call("binaryMap", Call("Measure", F.Id("Omega")), F.Id("ENNReal"))));

    private static Formula OpenLoopEvidenceFormula() =>
        Disp(Equal(
            Call("openLoopPairEvidence", F.Id("x"), F.Id("y")),
            Call("infiniteSum", F.Id("t"),
                Multiply(D(2), Subtract(D(1), Call("rho", F.Id("t"), F.Id("x"),
                    F.Id("y")))))));

    private static Formula LocalEquivalenceFormula() =>
        Disp(Call("allSelectedDistinctLocalLawsEquivalent", F.Id("K"), F.Id("i")));

    private static Formula DichotomyFormula() =>
        Disp(new Formula.Logic(
            And(Call("OpenLoopLocallyEquivalent", F.Id("K"), F.Id("i")),
                Call("allPairEvidenceInfinite", F.Id("rho"), F.Id("K"), F.Id("i"))),
            FormulaLogicOperator.Implies,
            Call("PairwiseMutuallySingular", F.Id("transcriptLaw"))));

    private static Formula ClassifierFormula() =>
        Disp(Call("measurableDisjointConullDecisionRegions", F.Id("transcriptLaw")));

    private static Formula NegativeLogFormula() =>
        Disp(Equal(
            Call("negativeLogAffinity", F.Id("rho")),
            Call("toENNReal", Seq(Open, Minus, Log, Sp, F.Id("rho"), Close))));

    private static Formula ConditionalAffinityFormula() =>
        Disp(Equal(
            Call("conditionalAffinity", F.Id("x"), F.Id("y"), F.Id("t"), F.Id("h")),
            Call("rho", Call("K", Call("policy", F.Id("t"), F.Id("h")), F.Id("x")),
                Call("K", Call("policy", F.Id("t"), F.Id("h")), F.Id("y")))));

    private static Formula PredictableEvidenceFormula() =>
        Disp(Equal(
            Call("predictableEvidenceProcess", F.Id("n"), F.Id("x"), F.Id("y")),
            Call("finiteSumBefore", F.Id("n"),
                Call("negativeLogConditionalAffinity", F.Id("x"), F.Id("y")))));

    private static Formula StoppingTopFormula() =>
        Disp(new Formula.Logic(
            Equal(Call("epsilonStoppingTime", F.Id("epsilon"), F.Id("pi")), Infty),
            FormulaLogicOperator.Iff,
            Call("noTimeHasErrorAtMost", F.Id("pi"), F.Id("epsilon"))));

    private static Formula InitialStopFormula() =>
        Disp(new Formula.Logic(
            Call("errorAtZeroAtMost", F.Id("pi"), F.Id("epsilon")),
            FormulaLogicOperator.Implies,
            Equal(Call("epsilonStoppingTime", F.Id("epsilon"), F.Id("pi")), D(0))));

    private static Formula EpsilonOneFormula() =>
        Disp(Equal(Call("epsilonStoppingTime", D(1), F.Id("pi")), D(0)));

    private static Formula SingletonErrorFormula() =>
        Disp(Equal(Call("posteriorError", Call("PMF", F.Id("Unit"))), D(0)));

    private static Formula SingletonStopFormula() =>
        Disp(Equal(
            Call("epsilonStoppingTime", F.Id("epsilon"), Call("PMFProcess", F.Id("Unit"))),
            D(0)));

    private static Formula EmptyPosteriorFormula() =>
        Disp(Call("IsEmpty", Call("PMF", Emptyset)));

    private static Formula ZeroThresholdFormula() =>
        Disp(Equal(
            Call("epsilonStoppingTime", D(0), Call("constantFairPosterior", F.Id("Bool"))),
            Infty));

    private static Formula SingletonPairFormula() =>
        Disp(Call("allDistinctPairEvidenceInfiniteVacuously", F.Id("Unit")));

    private static Formula FiniteClassifierFormula() =>
        Disp(new Formula.Logic(
            Call("FinitePairwiseMutuallySingular", F.Id("transcriptLaw")),
            FormulaLogicOperator.Implies,
            Call("HasCommonZeroErrorClassifier", F.Id("transcriptLaw"))));

    private static Formula CompletionFormula() =>
        Disp(new Formula.Logic(
            And(Call("OpenLoopLocallyEquivalent", F.Id("K"), F.Id("i")),
                And(Call("allPairEvidenceInfinite", F.Id("rho"), F.Id("K"), F.Id("i")),
                    Call("OpenLoopEvidenceDichotomy", F.Id("rho"), F.Id("K"), F.Id("i")))),
            FormulaLogicOperator.Implies,
            And(Call("PairwiseMutuallySingular", F.Id("transcriptLaw")),
                Call("HasCommonZeroErrorClassifier", F.Id("transcriptLaw")))));

    private static Formula DichotomyNecessaryFormula() =>
        Disp(Call("existsZeroAffinityIdenticalDiracCounterexample"));

    private static Formula NegativeLogZeroFormula() =>
        Disp(Equal(Call("negativeLogAffinity", D(0)), Infty));

    private static Formula EvidenceZeroFormula() =>
        Disp(Equal(Call("predictableEvidenceProcess", D(0), F.Id("x"), F.Id("y")), D(0)));

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create(Prefix + declaration);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
