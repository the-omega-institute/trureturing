using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GroundMode;

internal sealed class NormalizedReadoutDiskDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Candidate source. No Lean kernel or Scribe emitter execution is claimed.",
        H("NormalizedReadoutDisk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-readout-disk-affine-anchor-modulus-lower"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/NormalizedReadoutDisk.affine_anchor_modulus_lower"),
                H("A uniform denominator modulus floor"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same denominator functional acts on every allowed error vector. Cauchy-Schwarz and the reverse triangle inequality give norm(d)-sqrt(e*norm(b)^2) as a lower bound. This is a bound over the whole ball, not a check at sampled denominator values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-readout-disk-affine-anchor-ne-zero"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/NormalizedReadoutDisk.affine_anchor_ne_zero"),
                H("The anchor is uniformly nonzero"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The strict squared margin e*norm(b)^2<norm(d)^2 excludes denominator zeros on the entire error ball. It is derived before taking a ratio."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-readout-disk-affine-ratio-range-iff"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/NormalizedReadoutDisk.affine_ratio_range_iff"),
                H("Exact range of the two affine readouts"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quotient equals z for some vector of squared norm at most e exactly when norm(z*d-a)^2<=e*norm(c-conj(z)*b)^2. Necessity reuses Cauchy-Schwarz. Sufficiency constructs the minimum-norm residual-vector solution, treating a zero residual vector separately. Exact attainability concerns the complex Hilbert error ball. It does not assert that all those errors are actual eigenmode errors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-readout-disk-affine-ratio-disk-iff"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/NormalizedReadoutDisk.affine_ratio_disk_iff"),
                H("A division-free joint complex disk"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Completing the complex square gives D=norm(d)^2-e*norm(b)^2 and B=a*conj(d)-e*inner(c,b). The exact range is norm(D*z-B)^2<=norm(B)^2-D*(norm(a)^2-e*norm(c)^2). In ordinary coordinates the center is B/D and the squared radius is the displayed right side divided by D^2. The off-diagonal complex covariance is retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-readout-disk-orthogonal-readout-gram"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/NormalizedReadoutDisk.orthogonal_readout_gram"),
                H("The projected Riesz Gram data"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a unit candidate, subtracting its component from both Riesz vectors gives two residual energies and their joint covariance. The full inner products are reused; no separate readout or projection carrier is defined. These three identities are the algebraic adapter consumed by the Fourier interval calculation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-readout-disk-orthogonal-error-readout-disk"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/NormalizedReadoutDisk.orthogonal_error_readout_disk"),
                H("The same orthogonal error enters both readouts"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An error orthogonal to the candidate has exactly the same readout under the original and projected Riesz vectors. The affine disk theorem therefore bounds the actual normalized readout. Denominator nonvanishing is a conclusion. No independence assumption is made for numerator and denominator perturbations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-readout-disk-projective-eigenmode-readout-disk"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/NormalizedReadoutDisk.projective_eigenmode_readout_disk"),
                H("Consume the actual operator-domain Rayleigh enclosure"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing projective Rayleigh theorem supplies the norm budget and the existing energy identity supplies orthogonality. The new theorem then bounds the actual normalized readout of the projectively normalized eigenvector. The eigenpair, operator-domain symmetry, coercivity and independently checked anchor margin remain explicit. No Fourier identification, prolate approximation or all-scale limit is inferred from this source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-readout-disk-neumann-prime3-projective-ratio"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/NormalizedReadoutDisk.neumann_prime3_projective_ratio"),
                H("Arithmetic on the newer Neumann-weighted certificate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact energy constants reported in prime3_neumann_weighted_certificate.json give the squared error 44669457/489267186193, strictly less than 1/10000. This checks rational arithmetic only; it does not rerun the spectral interval verifier or discharge the actual form-domain bridge."))),
                DescribeRole.Theorem))));
}
