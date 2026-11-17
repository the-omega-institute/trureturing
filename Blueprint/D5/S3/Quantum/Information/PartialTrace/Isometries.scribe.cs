using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.PartialTrace;

internal sealed class IsometriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial trace through product isometries.",
        H("Partial trace through product isometries"),
        Blocks(Describe.Lean(
            DescribeId.Create("partialtraceisometries"),
            DeclarationHandle.Create("D5/S3/Quantum/Information/PartialTrace/Isometries.partialTrace_isometries"),
            H("Partial trace through product isometries"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For finite complex matrices v and w, if w adjoint times w is the identity, tracing the second factor of (v tensor w) z (v tensor w) adjoint gives v times the partial trace of z times v adjoint. The first matrix need not be an isometry. The proof contracts the w coefficients using column orthogonality. The declaration retains its AnticoherenceSpinCovariance namespace."))),
            DescribeRole.Theorem))));
}
