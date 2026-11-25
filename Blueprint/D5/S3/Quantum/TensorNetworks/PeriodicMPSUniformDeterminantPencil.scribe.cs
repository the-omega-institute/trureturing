using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSUniformDeterminantPencilDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSUniformDeterminantPencil";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A determinant pencil from the full periodic trace tensor",
        H("The contracted flattening and the witness pencil"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-uniform-contracted-pencil-determinant"),
                DeclarationHandle.Create(Module + ".det_observedFlattening_traceWord"),
                H("The determinant of the contracted flattening"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose four prefix words and four suffix words around a single physical slot. Contract that slot against a two-vector z. For a periodic binary bond-two trace tensor the resulting determinant is the product of the two guard-coordinate determinants and the square of the determinant of z₀A₀ + z₁A₁. The trace pairing factors the flattening through right multiplication by the pencil, which acts as the pencil on one of the two bond indices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-uniform-hard-core-witness-cores"),
                DeclarationHandle.Create(Module + ".witnessCore"),
                H("The two witness cores"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The zero core has first row (1, 0) and vanishing second row. The one core has rows (1, 1) and (−1, −1). Both are rank one. The zero core is idempotent, so padding a guard with further zeros leaves its product unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("periodic-uniform-hard-core-witness-quartic"),
                DeclarationHandle.Create(Module + ".det_guardedFlattening_witness"),
                H("The witness quartic at every length"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n ≥ 7, the prescribed guards are indexed by their endpoint bits, with one interior zero on the left and n − 6 on the right. The witness pencil has determinant −z₀z₁. Idempotence reduces the guards to the same four-by-four calculation at every length. Evaluation at z = (1, 1) gives determinant −1 and fixes the full-tensor flattening determinant to −(z₀z₁)²."))),
                DescribeRole.Theorem))));
}
