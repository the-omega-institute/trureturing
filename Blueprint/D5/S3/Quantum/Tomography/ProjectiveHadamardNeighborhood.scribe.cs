using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class ProjectiveHadamardNeighborhoodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projective ratios provide one complex domain across changes of anchor, with a scale-independent residual differential.",
        H("Projective Hadamard complex neighborhoods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projective-hadamard-phaseratiodomain"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/ProjectiveHadamardNeighborhood.phaseRatioDomain"),
                H("phaseRatioDomain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed-width open domain defined by all pairwise phase-modulus ratios. It contains the entire unit phase torus when R is greater than one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("projective-hadamard-projectivehadamardresidual"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/ProjectiveHadamardNeighborhood.projectiveHadamardResidual"),
                H("projectiveHadamardResidual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nonzero-phase Laurent coordinates of the existing paired residual. The matrix is fixed; conjugation is only on its coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("projective-hadamard-projective-reanchoring-preserves-domain-and-residual"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/ProjectiveHadamardNeighborhood.projective_reanchoring_preserves_domain_and_residual"),
                H("projective_reanchoring_preserves_domain_and_residual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every choice of a nonzero anchor preserves the same ratio domain and all actual residual values. The new anchor is exactly one and all coordinate moduli remain between 1/R and R. Successive anchor changes do not accumulate a width loss."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projective-hadamard-phase-ratio-domain-open-torus-and-gauges"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/ProjectiveHadamardNeighborhood.phase_ratio_domain_open_torus_and_gauges"),
                H("phase_ratio_domain_open_torus_and_gauges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The domain is open and contains all unit-phase inputs. Its defining condition is unchanged by nonzero common scaling, permutations, unit coordinate prefactors, and conjugation. Only domain invariance is claimed for the latter transformations; a fixed matrix residual need not be invariant under independent row phases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projective-hadamard-projective-residual-hasfderivat-and-scaled-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/ProjectiveHadamardNeighborhood.projective_residual_hasFDerivAt_and_scaled_bound"),
                H("projective_residual_hasFDerivAt_and_scaled_bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit complex Frechet derivative is derived from the actual Laurent residual. Each Euler-scaled Jacobian entry w_k J_ak has norm at most 10 R M^2 in dimension six. The self-index term cancels before the remaining five terms are bounded. This is not an inverse-Jacobian estimate or an automatic bound on a differently parameterized Cayley Newton map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projective-hadamard-paired-cayley-residual-eq-projective-readout"),
                DeclarationHandle.Create("D5/S3/Quantum/Tomography/ProjectiveHadamardNeighborhood.paired_cayley_residual_eq_projective_readout"),
                H("paired_cayley_residual_eq_projective_readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On every pole-free Cayley chart with unit prefactors, the new coordinate expression equals the already owned pairedCayleyResidual. The equality holds on complex coordinates, not only on the real slice."))),
                DescribeRole.Theorem))));
}
