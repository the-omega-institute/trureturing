using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class PositiveKrausCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The selected-column Gram controls a positive replacement of the canonical local Kraus compression.",
        H("Positive replacement of the Kraus compression"), Blocks(
            Describe.Lean(DescribeId.Create("j"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.J"),
                H("Canonical isometric Kraus column"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The column maps an input vector to the output and environment carrier using the canonical normalized Kraus family. The common-state construction uses its isometric compression."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phi"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.Phi"),
                H("Local channel adjoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Compress the local matrix acting in the canonical Kraus representation. This is the local block action in the reference trace pairing."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phir"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.PhiR"),
                H("Reference-amplified adjoint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Apply Phi blockwise to a complex joint matrix in the reference coordinates. The kernel estimate pairs this adjoint with the actual amplified channel."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pi"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.pi"),
                H("Local matrix representation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The representation acts by the local matrix tensor the environment identity. The selected-column residual is formed in this representation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kraus-complement"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.e"),
                H("Complementary Kraus projection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The defect projection is the identity minus J J adjoint. It gives the support of the selected Gram factor and its replacement after the polar step."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("defectr"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.defectR"),
                H("Joint adjoint defect"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Subtract the product of the two adjoint images from the adjoint image of Y Y adjoint. The trace test and the weighted energy defect use this matrix for Y and its adjoint."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phir-star"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.PhiR_star"),
                H("The reference adjoint preserves conjugate transpose"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For finite nonempty local carriers, every finite reference and arbitrary complex Y, PhiR of the conjugate transpose is the conjugate transpose of PhiR of Y. The Hilbert–Schmidt trace pairing and both Gram bounds use this equality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("matrix-units"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.E"),
                H("Matrix units"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each pair of output indices defines the matrix with a single unit entry. The packed column uses all these matrix units."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cblock"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.Cblock"),
                H("A defect block for a matrix unit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The block is J adjoint times the represented matrix unit times the complementary projection e. The selected-column proof packs these blocks together."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("c"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.C"),
                H("The packed defect matrix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Concatenate the Cblock matrices over the output index pairs. Its Gram matrix is the bound in the joint selected-column estimate."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("d"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.D"),
                H("The packed scalar residual"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Concatenate the residual blocks made from the chosen scalar family and the compressed matrix units. The selected-column estimate factors this matrix through C."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("universalpositivetracetest"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.UniversalPositiveTraceTest"),
                H("The uniform positive trace test"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite reference, complex output joint matrix Y and positive definite input joint Z, bound the infimum of the traced left residual Gram over all complex reference centers by the scaled traced adjoint defect. The endpoint estimate supplies this premise at c/(1-c)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-selected-column-joint-gram"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.selected_column_joint_gram"),
                H("One scalar family for the entire basis Gram"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a and b be finite nonempty types, let Phi be an actual completely positive trace-preserving channel from a to b, and let k be a nonnegative real number. Its canonical normalized Kraus family defines an isometric column J, the representation pi(A)=A tensor I_Env, and the projection e=I-J J adjoint. The universal premise tests every finite reference and complex joint input against general matrix centers.")),
                    Paragraph(Text("A selected matrix-unit column supplies a scalar family whose joint residual Gram is bounded by k times the actual defect Gram, including k=0. This joint bound supplies the rectangular factor used to construct the common state.")),
                    Paragraph(Text("Pack the full matrix-unit basis into one selected column. The packed defect is C C adjoint. A general matrix center supplies the residual P, whose selected column is D. Its remaining columns form R and give P P adjoint=D D adjoint+R R adjoint. Adding the positive remainder yields the joint selected-column inequality without imposing sparsity on the center. The positive Gram remainder preserves the bound on the selected column.")),
                    Paragraph(Text("The positive Kraus compression uses this joint Gram bound. The final all-finite Umegaki coefficient equality remains open."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-positive-state-compression"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/PositiveKrausCompression.common_positive_state_compression"),
                H("Positive trace-one Kraus compression"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The universal trace test supplies a rectangular Douglas factor supported on the Kraus complement. The singular polar factor and finite trace-norm bound give a normalized positive state and a replacement compression with the same supported Gram bound. UniversalPositiveScalarizer uses this fixed compression on every reference."))),
                DescribeRole.Theorem))));
}
