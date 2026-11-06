using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class FusionSpinChainOffsetIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fibonacci fusion-chain window dimension has an exact integer offset identity.",
        H("Fibonacci Fusion-Chain Offset Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fusion-spin-chain-window-dimension"),
                DeclarationHandle.Create("D5/S3/Quantum/FusionSpinChainOffsetIdentity.fusionDim"),
                H("Fibonacci window dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer lift of the window algebra dimension is D(n) = F_(2n-1)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fusion-spin-chain-offset-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/FusionSpinChainOffsetIdentity.exact_offset_identity"),
                H("Exact offset identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For integers n and k with |k| < n, the integer lift D(n) = F_(2n-1) satisfies D(n+k)D(n-k) - D(n)^2 = F_(2|k|)^2.")),
                    Paragraph(Text("The proof applies the pinned integer Fibonacci Catalan identity with x = 2(n-k)-1 and a = 2k. The surrounding fusion-category, cut-algebra, FDQC, and QCA bridge remains outside this arithmetic declaration."))),
                DescribeRole.Theorem),
            Paragraph(Text("Escape audit.")),
            Paragraph(Text("The typed source-bound registration compiles, but its source-family binding remains unfinished under issue #27348. The delivered head's required CI reading is DTR-Unregistered for exact_offset_identity and DTR-Undeclared for the Reg occurrence; no declared_validated audit is claimed. The missing evidence is a lawful source-family reconstruction that reaches a four-slot binding certificate while preserving the enrolled source template.")))));
}
