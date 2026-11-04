using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeBRSTCohomologyBorcherdsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Borcherds identity on original critical BRST cohomology", H("Borcherds identity on original critical BRST cohomology"), Blocks(
            Paragraph(Text("The unrestricted three-integer tensor Borcherds identity is reused on genuine cycle representatives of the original totalCharge. Its four finite action supports pass through the injective cycle subtype and the quotient map before any finsum is mapped. The resulting identity holds for all three integer parameters and arbitrary parity mixtures on the actual critical quotient. Rank 26 and both inverse Gram identities remain explicit; Jacobi, positivity, closure and a nonzero class are not assumed.")),
            Paragraph(Text("The tensor Borcherds proof and its Scott Carnahan vertexAlg attribution remain in the original supplier; this consumer does not duplicate that proof. The derivative law uses the descended Borcherds identity and the original negative-binomial coefficient calculation. Native compilation, axiom closure, semantic registration and formal publication remain separate evidence boundaries. No full string theory or AdS/CFT completion is claimed.")),
            Describe.Lean(DescribeId.Create("original-brst-quotient-borcherds"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBorcherds.borcherds"),
                H("Unrestricted Borcherds identity on the actual quotient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The conclusion includes the four finite supports and the separated signed finsum identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-brst-quotient-state-derivative-modes"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBorcherds.state_derivative_modes"),
                H("Translation differentiates every mode"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The all-integer identity at the vacuum and r=-2 supplies the exact coefficient formula."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-brst-quotient-state-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBorcherds.state_derivative"),
                H("Translation differentiates the descended field"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of all coefficients gives equality of the actual lower-truncated vertex operators."))), DescribeRole.Theorem))));
}
