using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class EJMPartialBoundLookupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJMPartialBoundLookup.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Assignment-checked lookup of the actual local EJM score bounds.",
        H("A producer lookup proposes; exact transport earns the bound"),
        Blocks(
            Paragraph(Text("The selector tests the twelve actual local coordinate permutations, normalizes known outcomes by first occurrence, and completes this normalization to a common outcome permutation. Literal binary dictionaries map the proposed base-five representative hash to a row index. These calculations are untrusted proposals: the returned lower bound checks the entire row assignment against the actual transported input and falls back to the all-unknown root on a missing or mismatched proposal. Dictionary completeness and canonicalizer optimality are unnecessary for soundness.")),
            Describe.Lean(DescribeId.Create("triangle-root"),
                DeclarationHandle.Create(Prefix + "triangle_root_assignment"),
                H("The literal triangle root has every coordinate unknown"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel checks the actual final triangle row's partial assignment, providing the fallback's required compatibility with every complete ten-coordinate event."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-lower"),
                DeclarationHandle.Create(Prefix + "triangle_lower_bound"),
                H("The checked triangle lookup bounds every compatible full event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Acceptance of every triangle row, together with the actual compatibility transport and centered-score invariance, earns the lookup bound for every completion of the input partial assignment. This is conditional on the complete row-checking obligation; it does not assert that the imported local DAG is already accepted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-root"),
                DeclarationHandle.Create(Prefix + "singleton_root_assignment"),
                H("The literal singleton root has every coordinate unknown"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel checks the actual final singleton row's all-unknown nine-coordinate partial assignment, supplying the fallback's compatibility with every complete event."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-lower"),
                DeclarationHandle.Create(Prefix + "singleton_lower_bound"),
                H("The checked singleton lookup bounds every compatible full event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same checked lookup theorem applies to the actual singleton partial action, rows and centered coefficient score. Its bound is valid once every actual singleton row is accepted; no external minimum or missing representative can silently supply the required numerical inequalities."))), DescribeRole.Theorem))));
}
