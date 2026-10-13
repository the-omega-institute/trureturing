using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class LogEqualityResolventRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithm equality forces full finite spectral rigidity.",
        H("Logarithm equality forces full finite spectral rigidity"), Blocks(
            Describe.Lean(
                DescribeId.Create("log-equality-forces-functional-intertwining"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/LogEqualityResolventRigidity.log_equality_forces_functional_intertwining"),
                H("From a scalar log equality to all spectral functions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("For strictly positive finite complex A and B, V* V <= I and V* A V <= B, retain the "
                        + "distinguished-vector norm saturation hypothesis. Equality of the actual logarithm "
                        + "quadratic forms then forces f(A) Vb = V f(B)b for every real f. The proof differentiates "
                        + "the finite shifted-log difference, uses the nonnegative resolvent defect and its zero "
                        + "limit at infinity, and then finite spectral rigidity. This implication is a live "
                        + "ingredient of the supported Petz equality theorem, not an equality assumption disguised as "
                        + "recovery."))),
                DescribeRole.Theorem))));
}
