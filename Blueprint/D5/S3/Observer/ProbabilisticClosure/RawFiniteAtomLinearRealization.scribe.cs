using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class RawFiniteAtomLinearRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native-test readouts through the exceptional parity quotient.",
        H("Finite atom upper bounds"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-atom-upper-bounds"),
            DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization.result"),
            H("Three finite native-test carriers"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite family of distinct parameters strictly between zero and one, every root probability strictly between zero and one, and positive component weights summing to one, the number of components satisfying alpha equals (one minus alpha) times the parameter is at most one. If alpha is at least one half, the exceptional component count is zero.")),
                Paragraph(Text("The retained-root interface admits a finite carrier of cardinality four times the component count plus two; the emitted-root interface admits cardinality four times the component count plus one. The raw interface admits cardinality four times the component count minus twice the exceptional component count plus one. Every carrier has nonnegative joint output-successor matrices whose columns sum to one across all outputs and successors.")),
                Paragraph(Text("For every measurable independent old seed, causal policy, finite acquired history and measurable old-seed event with positive original joint mass, the feature is nonnegative and normalized. Every finite output-adaptive residual test has its original acceptance mass equal to that conditioning mass times the fixed linear readout. Native events are independently defined by actual source execution. A fresh independent probability seed may sample any measurable family of finite tests; integrating each fixed test row gives the same original-source randomized acceptance probability. For each positive-mass native output, the new history feature is the joint output matrix applied to the old feature, divided by its total output mass. The actual conditional output mass is the total matrix pushforward mass. For a specified next query j, scaling the new feature by the joint mass of its output event gives the old event mass times the unnormalized matrix pushforward. The next query is fixed in this relation; the event is not the complete next-history event under the original randomized policy.")),
                Paragraph(Text("In each exceptional raw component the parity pairs zero-zero and one-one share the even coordinate, while one-zero and zero-one share the odd coordinate. This quotient preserves marker rates, flips even and odd on a zero reply, and sends every marker to the shared terminal coordinate. Pushing the full feature through this quotient preserves every finite output-adaptive test row and every normalized output-successor update. Under the source mixture, almost every source couples the recovered terminal bit to its original root for every causal policy, seed value and finite stopping history."))),
            DescribeRole.Theorem),
            Fact("raw-row-descends", "raw_row_descends", "Finite test rows descend through the raw quotient", "For every finite component family, strictly positive unit-interval alpha, finite test and full raw coordinate, the test row at its encoded raw coordinate equals the full carrier test row at the original coordinate."),
            Fact("raw-component-card", "raw_component_card", "Cardinality of one raw component", "For every unit-interval alpha and component parameter q, the raw canonical parity pairs number two if alpha equals (one minus alpha) times q, and four otherwise."),
            Fact("raw-native-bridge", "raw_native_bridge", "Concrete raw test readouts", "For every finite component family, strictly positive alpha and component parameters, and positive weights summing to one, the concrete rawModel and rawFeature preserve all original-history conditional native finite-test probabilities, with normalized nonnegative history features."),
            Fact("raw-feature-updates", "raw_feature_updates", "Concrete raw feature updates", "Under the same positivity and weight normalization assumptions, the concrete raw feature updates by normalized joint output-successor transport for every history, queried arm and source whose output matrix mass is positive."),
            Fact("raw-card", "raw_card", "Raw carrier cardinality", "For every finite component family and unit-interval alpha, the concrete raw carrier has exactly four times the component count minus twice the exceptional component count plus one coordinates."),
            Fact("raw-probability", "raw_probability", "Raw probability columns", "For every finite component family and strictly positive alpha, the concrete raw joint output-successor matrices are nonnegative and each action column sums to one over all outputs and successor coordinates."))));
    private static DocumentBlock.Describe Fact(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(
            "D5/S3/Observer/ProbabilisticClosure/RawFiniteAtomLinearRealization." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
