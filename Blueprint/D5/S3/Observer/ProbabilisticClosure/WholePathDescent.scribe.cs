using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class WholePathDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pointwise one-step intertwining law transports the full joint probability law of every finite observed path.",
        H("Exact Descent of Whole Markov Path Laws"),
        Blocks(
            Paragraph(Text("A path contains its initial state and n subsequent transitions. The PMF recursion shares a single hidden state across consecutive steps. The existing strong-lumpability owner supplies the one-step quotient criterion; this file proves the missing all-length joint-law transport rather than restating that criterion.")),
            Describe.Lean(
                DescribeId.Create("whole-path-descent"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/WholePathDescent.whole_path_descent"),
                H("One-step descent preserves the whole joint path law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every hidden starting state x, assume the push-forward of K(x) equals L(q(x)). Induction on the number of transitions, using PMF bind and map identities, shows that mapping q along the entire hidden path gives exactly the path law of L. The premise is uniform over hidden states; a property only of one equilibrium initial distribution is not substituted for it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("initial-distribution-path-descent"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/WholePathDescent.initial_distribution_path_descent"),
                H("Mixtures of initial states preserve common hidden witnesses"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same law holds under any initial PMF. Mixing happens once at the beginning, not independently inside each observation fiber at every step. The result is an identity of joint distributions, not only equality of individual frame marginals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("path-statistic-descent"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/WholePathDescent.path_statistic_descent"),
                H("Intermediate-event statistics are included"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every function of the observed finite path has the transported distribution. Examples include a visit to a specified region before the horizon or a finite path cost. Infinite-time stopping results and endpoint-conditioned measures still require their own definitions and, for conditioning, positive event probability. The formal result is discrete PMF path sampling; no continuum molecular SDE or neural generator is certified."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent")),
        ]));
}
