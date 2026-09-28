using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class ForwardInvariantPredictorCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite predictors correspond to invariant covers with bounded future diameter.",
        H("Finite Prediction and Invariant Covers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-future-predictor"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFinitePredictor"),
                H("A finite predictor for every future word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let X be a nonempty set of actual states, A an arbitrary action alphabet, "
                    + "F a total deterministic action on X, and o an observation in a metric space Y. "
                    + "A predictor has a nonempty finite set S with at most s states, an initialization "
                    + "e from X to S, transitions G indexed by A, and an output h in Y. For every "
                    + "initial state x and every finite word w, including the empty word, the distance "
                    + "between h applied to G along w from e(x) and o applied to F along w from x "
                    + "is at most the nonnegative error epsilon. Words act from left to right. "
                    + "Transitions receive only the action and current machine state; output depends "
                    + "only on that state. Initialization need not commute with transitions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("invariant-cover"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.IsInvariantCover"),
                H("A deterministic invariant cover"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each set C(i) is nonempty, and every point of X belongs to at least one C(i). "
                    + "The sets may overlap. For every action a and index i, a single successor "
                    + "delta(a,i) satisfies F(a)[C(i)] contained in C(delta(a,i)). A center y(i) in Y "
                    + "bounds the supremum of the distances from o(x) to y(i), for x in C(i), by "
                    + "epsilon. This supremum is taken in the nonnegative extended reals, so no "
                    + "boundedness assumption is needed to define it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-invariant-cover"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.HasFiniteInvariantCover"),
                H("A cover with a finite state budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The index set is nonempty and finite, with cardinality at most s. "
                    + "No finiteness, topology, or continuity assumption is imposed on X or A."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("future-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover.futureDistance"),
                H("Distance over the full future"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The future distance of x and x-prime is the supremum, over all finite words w, "
                    + "of the distance between their observations after applying the same word. "
                    + "Its value lies in the nonnegative extended reals and can be infinite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("predictor-cover-equivalence-and-diameter"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ForwardInvariantPredictorCover."
                    + "finite_predictor_iff_forward_invariant_cover"),
                H("Equivalence and the diameter of every cover member"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonnegative epsilon and every integer state budget s at least one, "
                        + "a full-future predictor with at most s states exists if and only if a "
                        + "deterministic invariant cover with at most s nonempty members exists. "
                        + "For every invariant cover, any two points in the same member have future "
                        + "distance at most twice epsilon. This last assertion holds even for an "
                        + "infinite index set.")),
                    Paragraph(Text(
                        "From a predictor, collect in C(i) all true states reached by any initial "
                        + "state and any word whose corresponding machine state is i. Remove "
                        + "unreachable machine states. The empty word gives a cover, appending an "
                        + "action gives a deterministic successor, and the prediction guarantee "
                        + "bounds every member around the machine output.")),
                    Paragraph(Text(
                        "Conversely, choose for each true initial state a member containing it. "
                        + "Induction on words keeps the true state in the member named by the machine. "
                        + "The radius bound then proves prediction accuracy. Two points in one member "
                        + "remain in a common successor member after every word. The triangle "
                        + "inequality through its center bounds each pair of observations by twice "
                        + "epsilon, and taking the supremum proves the diameter bound. "
                        + "The construction asserts existence and does not assert effective computability."))),
                DescribeRole.Theorem))));
}
