using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identifiability;

internal sealed class IdentifiabilityEstimabilityComputationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Identifiability/"
            + "IdentifiabilityEstimabilityComputation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-law semantics, finite-sample guarantees, algorithms, and resource bounds "
            + "are registered separately and separated by concrete witnesses.",
        H("Identifiability, Estimability, and Computation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("identifiable-from-an-exact-evidence-interface"),
                DeclarationHandle.Create(DeclarationPrefix + "Identifiable"),
                H("Identifiability is evidence-kernel containment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Definition 281.1 is represented literally by containment of the "
                        + "canonical Setoid.ker of the evidence interface in the target "
                        + "kernel. It is an infinite-precision law-level predicate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("estimable-by-a-positive-finite-sample"),
                DeclarationHandle.Create(DeclarationPrefix + "Estimable"),
                H("Estimability uses a positive finite sample"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Definition 281.2 is deliberately narrowed to one faithful disjunct: "
                        + "there is a positive finite sample size and an estimator that is "
                        + "almost surely exact for every model. Under zero-one loss this is "
                        + "a zero-risk guarantee, stronger than merely finite risk."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("computable-within-an-explicit-resource-budget"),
                DeclarationHandle.Create(DeclarationPrefix + "Computable"),
                H("Computability combines correctness and a resource bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Definition 281.3 is narrowed to exact evaluation by a registered "
                        + "algorithm together with a uniform bound in a supplied natural-"
                        + "valued cost model. It does not claim a Mathlib complexity class."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-law-identification-has-no-finite-exact-converse"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "identifiable_not_finite_sample_accurate"),
                H("Identifiability does not imply finite-sample accuracy"),
                StatementSource.FromAuthor(IdentifiableNotEstimableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The imported Bernoulli product-law witness separates the two Boolean "
                        + "states by a complete-transcript event of probabilities zero and "
                        + "one. Every finite prefix retains an overlapping positive-mass "
                        + "all-false cylinder, so no finite decoder is almost surely exact."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-accuracy-can-exceed-a-resource-budget"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_sample_accurate_not_computable"),
                H("Finite-sample accuracy does not imply tractability"),
                StatementSource.FromAuthor(EstimableNotComputableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A noiseless Boolean observation is exactly estimable at sample size "
                        + "one. The same correct identity evaluator is charged cost two by "
                        + "the explicit model, exceeding the positive acceptable budget one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-parametric-algorithm-does-not-identify-the-full-class"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "parametric_algorithm_not_nonparametric_identifiable"),
                H("A subclass algorithm does not prove global identifiability"),
                StatementSource.FromAuthor(ParametricNotNonparametricFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two-point subclass consisting of some false and some true is "
                        + "decoded exactly within budget. On the full Option Bool class, "
                        + "none and some false have equal evidence but different targets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-kernel-theorem-does-not-certify-a-candidate-formula"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "semantic_kernel_does_not_certify_candidate_formula"),
                H("The semantic layer does not certify a registered formula"),
                StatementSource.FromAuthor(SemanticNotFormulaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Identity evidence identifies the identity target, but this semantic "
                        + "fact does not certify the independently registered Boolean "
                        + "negation formula. This records the first adjacent layer boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-formula-does-not-replace-a-sampling-theorem"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "identification_formula_does_not_replace_sampling_theorem"),
                H("An identification formula does not replace sampling"),
                StatementSource.FromAuthor(FormulaNotSamplingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating the probability-one distinguishing event gives an exact "
                        + "formula on complete laws. The same product-law model still has "
                        + "no almost-surely exact finite-prefix estimator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-sampling-theorem-does-not-certify-an-algorithm"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "sampling_theorem_does_not_certify_candidate_algorithm"),
                H("A sampling theorem does not certify a candidate algorithm"),
                StatementSource.FromAuthor(SamplingNotAlgorithmFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The one-sample identity estimator is almost surely exact in the "
                        + "noiseless Boolean model. That theorem does not make the separately "
                        + "registered Boolean-negation algorithm implement identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("an-algorithm-does-not-supply-a-complexity-bound"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "algorithm_does_not_replace_complexity_bound"),
                H("An algorithm does not replace a complexity bound"),
                StatementSource.FromAuthor(AlgorithmNotComplexityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Identity implements the identity specification pointwise. A separate "
                        + "cost calculation still exceeds budget one, so correctness alone "
                        + "does not register the fifth layer.")),
                    Paragraph(Text(
                        "The Lean degeneracy audit also checks equal kernels, constant maps, "
                            + "an empty carrier, a singleton model, a finite Boolean model, "
                            + "and sample size zero. No prime-specific fact is load-bearing."))),
                DescribeRole.Theorem))));

    private static Formula IdentifiableNotEstimableFormula() => Disp(Seq(
        Call("Identifiable", F.Id("stateLaw"), F.Id("id")), Sp, Land, RowBreak,
        Neg, Sp, Call("Estimable", F.Id("finiteTranscript"), F.Id("id")), Dot));

    private static Formula EstimableNotComputableFormula() => Disp(Seq(
        Call("Estimable", F.Id("deterministicBoolLaw"), F.Id("id")),
        Sp, Land, RowBreak,
        Neg, Sp, Call("Computable", F.Id("id"), F.Id("id"), D(1)), Dot));

    private static Formula ParametricNotNonparametricFormula() => Disp(Seq(
        Call("IdentificationFormula", F.Id("parametricSubclass"),
            F.Id("parametricAlgorithm")), Sp, Land, RowBreak,
        Call("Computable", F.Id("parametricAlgorithm"), D(1)), Sp, Land, RowBreak,
        Neg, Sp, Call("Identifiable", F.Id("nonparametricEvidence"),
            F.Id("nonparametricTarget")), Dot));

    private static Formula SemanticNotFormulaFormula() => Disp(Seq(
        Call("Identifiable", F.Id("id"), F.Id("id")), Sp, Land, RowBreak,
        Neg, Sp, Call("IdentificationFormula", F.Id("id"), F.Id("id"),
            F.Id("not")), Dot));

    private static Formula FormulaNotSamplingFormula() => Disp(Seq(
        Call("IdentificationFormula", F.Id("stateLaw"), F.Id("id"),
            F.Id("lawClassifier")), Sp, Land, RowBreak,
        Neg, Sp, Call("Estimable", F.Id("finiteTranscript"), F.Id("id")), Dot));

    private static Formula SamplingNotAlgorithmFormula() => Disp(Seq(
        Call("FiniteSampleAccurateAt", F.Id("deterministicBoolLaw"), D(1),
            F.Id("id")), Sp, Land, RowBreak,
        Neg, Sp, Call("AlgorithmImplements", F.Id("id"), F.Id("not")), Dot));

    private static Formula AlgorithmNotComplexityFormula() => Disp(Seq(
        Call("AlgorithmImplements", F.Id("id"), F.Id("id")), Sp, Land, RowBreak,
        Neg, Sp, Call("ComplexityBound", D(2), F.Id("id"), D(1)), Dot));
}
