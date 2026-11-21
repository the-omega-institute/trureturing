using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Signed;

internal sealed class IdentificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.";
    private const string TwistedGround = "D5/S3/VertexAlgebra/TwistedGround/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identification of the original Gaussian kernels in six signed sectors",
        H("Identification of the original Gaussian kernels in six signed sectors"),
        Blocks(
            Describe.Lean(DescribeId.Create("signed-candidate"), DeclarationHandle.Create(Prefix + "signedCandidate"),
                H("Candidate selected by the original kernel flag"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Boolean square, e and f and complex u, v and r, "
                    + "signedCandidate(square,e,f,u,v,r) selects candidateT(e,f,u,v,r) if square is true "
                    + "and candidateJ(e,f,u,v,r) if square is false. The labels e and f are the same "
                    + "Boolean labels used in kernelMode."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("six-sector-identification"),
                DeclarationHandle.Create(Prefix + "six_sector_identification"),
                H("Literal J and T equal their signed candidates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For Boolean square, e and f with e = false or f = false, complex u and v, "
                        + "and real 0 < r < 1 with ‖u‖ + √r < 1 and ‖v‖ + √r < 1, "
                        + "kernelMode(square,e,f,u,v,(√r : ℂ)) = signedCandidate(square,e,f,u,v,(r : ℂ)). "
                        + "Here kernelMode is the full original ℕ × ℕ mode sum of externalJ or externalT "
                        + "coefficients weighted by uᵖvᑫ. The three label pairs (−−), (−+), and (+−) "
                        + "apply to both kernel flags. The axes and diagonal are included.")),
                    Paragraph(Text("At fixed r, subtract the candidate from the literal kernel on the bidisk "
                        + "of radius 1 − √r. The original Hilbert mode theorem and candidate regularity give "
                        + "joint complex differentiability, so restriction to either coordinate slice "
                        + "justifies subtraction of derivatives. "),
                        Ref(TwistedGround + "PositiveJ/Identification.kernelMode_joint_differentiable"), Text(", "),
                        Ref(TwistedGround + "Signed/CandidateSource.candidates_original_joint_differentiable")),
                    Paragraph(Text("The literal displacement equations and the corresponding J and T candidate "
                        + "equations have the same original modeA and modeH source with the same period "
                        + "ratio. The J equations also have the identical modeB(e)modeB(f) term. "
                        + "Subtracting gives the homogeneous equation with the sum for J and the difference for T. "),
                        Ref(TwistedGround + "OriginalGaussianExternalEquations.displacement_differential"), Text(", "),
                        Ref(TwistedGround + "Signed/JSpatial.candidateJ_original_displacement"), Text(", "),
                        Ref(TwistedGround + "Signed/CandidateSource.candidateT_original_displacement")),
                    Paragraph(Text("Apply signed_spatial_zero directly to the difference on that bidisk using "
                        + "the negative-label hypothesis. Its slice argument uses the analytic identity lemma "
                        + "eqOn_zero_of_preconnected_of_eventuallyEq_zero to extend local vanishing over the "
                        + "whole slice disk. "),
                        Ref(TwistedGround + "Signed/SpatialUniqueness.signed_spatial_zero")),
                    Paragraph(Text("This equality supplies the positive-real radial values for the later "
                        + "complex radial identification in the same six sectors. That transport applies "
                        + "eqOn_of_preconnected_of_mem_closure to the original kernel and the candidate "
                        + "composed with z ↦ z², using the real equalities accumulating at z = 0."))),
                DescribeRole.Theorem))));
}
