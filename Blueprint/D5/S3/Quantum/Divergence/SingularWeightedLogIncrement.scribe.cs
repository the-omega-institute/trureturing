using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class SingularWeightedLogIncrementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A singular weighted logarithm increment is nonnegative and detects overlap exactly.",
        H("Singular weighted logarithm increment"), Blocks(
            Describe.Lean(DescribeId.Create("weighted-log-increment"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/SingularWeightedLogIncrement.weighted_log_increment_nonneg_and_eq_zero_iff"),
                H("Exact equality for the supported logarithm increment"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/audenaert2014skew"),
                    LibraryNoteRef.Create("D5/L/Divergence/hiai2024affinerenyi")),
                Blocks(
                    Paragraph(Text("Let C and rho be positive semidefinite matrices on Fin n. Let 0 < u ≤ v and e > 0, and suppose u times C ≤ A ≤ v times C. The real trace of A times the difference of log(C + e times rho) and log(C) is nonnegative. It is zero exactly when C times rho is zero.")),
                    Paragraph(Text("Both endpoints are shifted by a positive multiple of the identity. Audenaert's resolvent representation expresses the shifted gap as the integral of a weighted inverse difference. The sandwich bounds each integrand by scalar multiples of the pairing with C. Inverse order and cancellation characterize its zero set. The integral over shifts greater than one gives a positive lower bound whenever there is overlap.")),
                    Paragraph(Text("The upper sandwich places the weight on the support of each endpoint. The supported cross-log limit from AlphaZAffine and UmegakiSupportedNoise therefore yields convergence to the two CFC logarithms, with value zero on each kernel. The fixed lower bound survives this limit."))),
                DescribeRole.Theorem))));
}
