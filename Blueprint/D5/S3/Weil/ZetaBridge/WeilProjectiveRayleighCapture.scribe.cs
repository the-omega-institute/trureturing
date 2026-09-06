using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilProjectiveRayleighCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Candidate mathematical source; compilation and admission are not claimed.",
        H("WeilProjectiveRayleighCapture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weilprojectiverayleighcapture-eigen-overlap-ne-zero"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilProjectiveRayleighCapture.eigen_overlap_ne_zero"),
                H("The overlap is derived"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonzero eigenvector with real eigenvalue below the coercivity threshold cannot be candidate-orthogonal. Applying the complement bound to that eigenvector would contradict its energy. Neither symmetry nor normalization is needed in this lemma."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilprojectiverayleighcapture-projective-error-energy-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilProjectiveRayleighCapture.projective_error_energy_identity"),
                H("The complex projective energy identity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normalize the actual eigenvector by alpha=<iota(k),iota(u)> and subtract k. Candidate normalization makes this error orthogonal to k. Domain linearity and symmetry retain both mixed terms and give q(w)=lambda*norm(w)^2+q(k)-lambda. The domain may be that of an unbounded operator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilprojectiverayleighcapture-projective-rayleigh-enclosure"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilProjectiveRayleighCapture.projective_rayleigh_enclosure"),
                H("A sharp projective enclosure from energy data"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nonzero overlap is proved first. The exact energy identity and complement coercivity imply candidate energy at least lambda and (T-lambda)*norm(w)^2<=q(k)-lambda. Since q(k)<=U<T, norm(w)^2<1. Replacing lambda by the certified lower bound ell now yields (T-ell)*norm(w)^2<=U-ell. Eigenvector normalization and a separate candidate-above-ground premise are unnecessary. This general variational theorem does not establish the arithmetic Weil hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilprojectiverayleighcapture-prime3-projective-ratio"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilProjectiveRayleighCapture.prime3_projective_ratio"),
                H("Exact arithmetic on the existing fixed-window enclosure"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rational values ell=103/2000000000, U=560909/10000000000000 and T=1/200000 are read from prime3_refined_certificate.json in PR #5602. This theorem verifies the ratio and the radius comparison only. It does not re-run the interval verifier or prove the underlying operator-domain bridge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weilprojectiverayleighcapture-norm-lt-prime3-radius"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilProjectiveRayleighCapture.norm_lt_prime3_radius"),
                H("A rational norm radius"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An upper bound of 15303/16495000 on the squared norm gives norm strictly below 61/2000. The claim concerns any vector meeting this bound, with no zeta-zero data supplied or inferred."))),
                DescribeRole.Theorem))));
}
