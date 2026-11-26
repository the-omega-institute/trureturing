using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GeodesicCMI;

internal sealed class CapelCostaRicoForwardGeodesicDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/capelcostarico2026geodesic");
    private static readonly LibraryNoteRef Masking =
        LibraryNoteRef.Create("D5/L/Divergence/ambainis2000private");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful three-qubit witness pairs share their AB, AC and BC marginals within each pair.",
        H("Faithful pairs with matching two-body marginals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-geodesic-density-rmatrix"),
                DeclarationHandle.Create(Prefix + "RMatrix"),
                H("Regularized three-qubit witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source, Masking),
                Blocks(Paragraph(Text(
                    "The reference S_u is (I + (1−2u) Z_A Z_B)/8 with identity on C. The witness adds (1−η) √(u(1−u)) X_A Z_B Z_C/4. The balanced real-state masking by I and Y on a qubit is the antecedent for the cancellation on AC."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-density-rmatrix-posdef"),
                DeclarationHandle.Create(Prefix + "RMatrix_posDef"),
                H("Faithfulness under regularization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The unsmoothed matrix is positive semidefinite and S_u is positive definite for 0 < u < 1/2. Mixing in a weight 0 < η < 1 of S_u makes the witness positive definite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-density-pair-marginals"),
                DeclarationHandle.Create(Prefix + "pair_marginals"),
                H("Equality of the three two-body marginals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source, Masking),
                Blocks(Paragraph(Text(
                    "Every one-factor partial trace kills X_A Z_B Z_C. Both AC and BC are I/4. The common AB marginal is diagonal with entries (1−u,u,u,1−u)/2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-density-tracedistance-r-s"),
                DeclarationHandle.Create(Prefix + "traceDistance_R_S"),
                H("Exact distance between the faithful states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The trace distance is (1−η) √(u(1−u)). The Pauli product in the difference is a self-adjoint involution, so the absolute value has a constant eigenvalue on the eight-dimensional space."))),
                DescribeRole.Theorem)),
        []));
}
