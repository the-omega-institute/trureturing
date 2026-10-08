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
                Paragraph(Text("For every finite family of distinct parameters strictly between zero and one, every root probability strictly between zero and one, and positive component weights summing to one, the number of components satisfying alpha equals (one minus alpha) times the parameter is at most one.")),
                Paragraph(Text("The retained-root interface admits a finite carrier of cardinality four times the component count plus two; the emitted-root interface admits cardinality four times the component count plus one. The raw interface admits cardinality four times the component count minus twice the exceptional component count plus one. Every carrier has nonnegative joint output-successor matrices whose columns sum to one across all outputs and successors.")),
                Paragraph(Text("For every measurable independent old seed, causal policy, finite acquired history and measurable old-seed event with positive original joint mass, the feature is nonnegative and normalized. Every finite deterministic residual test has its original acceptance mass equal to that conditioning mass times the fixed linear readout. Native events are independently defined by actual source execution.")),
                Paragraph(Text("In each exceptional raw component the parity pairs zero-zero and one-one share the even coordinate, while one-zero and zero-one share the odd coordinate. This quotient preserves marker rates, flips even and odd on a zero reply, and sends every marker to the shared terminal coordinate. Pushing the full feature through this quotient preserves every finite deterministic test row."))),
            DescribeRole.Theorem))));
}
