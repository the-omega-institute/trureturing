using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial;

internal sealed class CandidateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphy of the signed candidates on the original radial disk",
        H("Signed Gaussian candidates at the radial square"),
        Blocks(
            Describe.Lean(DescribeId.Create("complex-radial-source-radius"),
                DeclarationHandle.Create(Prefix + "sourceRadius"),
                H("Common radial radius"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For complex u and v, the real radius sourceRadius(u,v) is "
                    + "min(1 − ‖u‖, 1 − ‖v‖)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complex-radial-source-radius-iff"),
                DeclarationHandle.Create(Prefix + "norm_lt_sourceRadius_iff"),
                H("The original source bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For complex u, v and z, ‖z‖ < sourceRadius(u,v) holds exactly when "
                    + "‖u‖ + ‖z‖ < 1 and ‖v‖ + ‖z‖ < 1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-radial-source-radius-positive"),
                DeclarationHandle.Create(Prefix + "sourceRadius_pos"),
                H("Positive radius"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For complex u and v with ‖u‖ < 1 and ‖v‖ < 1, "
                    + "0 < sourceRadius(u,v), so the open radial disk contains zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-radial-source-radius-at-most-one"),
                DeclarationHandle.Create(Prefix + "sourceRadius_le_one"),
                H("Unit upper bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex u and v, sourceRadius(u,v) ≤ 1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complex-radial-signed-candidate"),
                DeclarationHandle.Create(Prefix + "signedCandidate"),
                H("The signed candidate selector"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Booleans square, e and f and complex u, v and r, "
                    + "signedCandidate(square,e,f,u,v,r) selects the signed candidateT(e,f,u,v,r) "
                    + "when square is true and the signed candidateJ(e,f,u,v,r) when it is false. "
                    + "The selector and the two source labels are passed through in the same order as in kernelMode."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complex-radial-candidate-holomorphic"),
                DeclarationHandle.Create(Prefix + "candidate_square_analyticOnNhd"),
                H("Analyticity on the original radial disk"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For all Booleans square, e and f and complex u and v, the function "
                        + "z ↦ signedCandidate(square,e,f,u,v,z²) is complex analytic at every point "
                        + "of the open ball about zero of radius sourceRadius(u,v).")),
                    Paragraph(Text("At such a point, ‖z²‖ ≤ ‖z‖ keeps the source sums and the period "
                        + "correction in their differentiability domains. The T denominator E is nonzero "
                        + "using √‖z²‖ = ‖z‖. For J, the original source factors b(u) and b(v) and the "
                        + "sum W(e,u,z²) + W(f,v,z²) are nonzero there. The quotient and product rules "
                        + "give complex differentiability on the open ball, hence analyticity."))),
                DescribeRole.Theorem))));
}
