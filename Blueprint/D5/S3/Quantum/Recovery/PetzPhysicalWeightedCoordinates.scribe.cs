using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzPhysicalWeightedCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical Petz error has weighted modular coordinates.",
        H("Physical Petz error has weighted modular coordinates"), Blocks(
            Describe.Lean(
                DescribeId.Create("physicalweightederror"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physicalWeightedError"),
                H("The supported physical matrix error"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual supported relative-modular model M, put H=sqrt(S), P_R=spectralSupport(R), and E_M(x)=H Psi(spectralX(x)) P_R-sqrt(R). The right support projection is part of the definition; its kernel columns vanish. All matrices and the adjoint Psi belong to the same actual channel and density-state pair. This definition is consumed by all three coordinate estimates below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("modularcoordinateerror"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.modularCoordinateError"),
                H("The modular inverse-square-root error"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same model define d_M(x)=A^(-1/2) xi-V x, using cfc(t -> 1/sqrt(t)) on the positive support carrier of A. This coordinate vector is not itself the physical matrix error. At x=B^(-1/2) eta it is the inverse-square-root intertwining error consumed by PetzCoreTraceStability."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-positive-coordinate"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_positive_coordinate"),
                H("Each positive coordinate carries a spectral weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For j in the positive S spectrum and i in the positive R spectrum, <v_j,E_M(x)u_i> = -sqrt(s_j/r_i) d_M(x)_(j,i). The model retains input support containment. Consequently the physical error has a spectral weight sqrt(s_j/r_i), rather than an unweighted modular coordinate norm. This identity is consumed by physical_weighted_parseval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-weighted-parseval"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_weighted_parseval"),
                H("Full physical Parseval includes the kernel coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every coordinate vector x, ||E_M(x)||_HS^2 = sum_(j,i) (s_j/r_i) |d_M(x)_(j,i)|^2 over the positive S and R support indices. Positive-support containment makes the omitted zero-spectrum rows vanish, and P_R makes the omitted kernel columns vanish. The equality concerns the full physical matrix and is consumed by physical_hs_sq_le_coordinate_sq. Singular physical density matrices are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-hs-sq-le-coordinate-sq"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates.physical_hs_sq_le_coordinate_sq"),
                H("An actual spectral upper bound controls the physical norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If s_j/r_i <= L for every positive support pair, then ||E_M(x)||_HS^2 <= L sum_(j,i) |d_M(x)_(j,i)|^2. This theorem states exactly that upper-bound hypothesis; it does not replace the weighted norm by an unweighted one with constant one. PetzCoreTraceStability.petz_core_traceNorm_le_weighted_inverse_sqrt_error consumes the estimate at x=B^(-1/2) eta. These are auxiliary spectral and norm consequences, without an independent novelty claim."))),
                DescribeRole.Theorem))));
}
