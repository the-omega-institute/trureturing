using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class ForwardDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual charged residue comparison.",
        H("Forward"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-residue-arbitrary-input-forward"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/Forward.chargedPhysicalResidueRow_forward"),
                H("The complete arbitrary-input forward formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For all original lattices, charges, projected signs, both matching integer lifts, residue indices and actual inputs, R_l is the sum for k<L-l of choose(gamma/2,k) times C_(l+k), where L=(K-r).toNat and K is any natural bound on the absolute pairing. The two whole ordered sums are normalized together before applying the scalar residue substitution and four reflected kernels. Finite-support additivity extends the tensor calculation to arbitrary actual inputs. The independently proved unweighted tail handles every l>=L, including the zero cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-residue-actual-source-inverse"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/Forward.chargedPhysicalSourceRow_inverse"),
                H("The actual finite inverse and all-N source composition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("The finite Vandermonde inverse is instantiated with the proved full forward law and independent collision tail. The public all-N source-to-collision theorem then identifies the original source row at zero with the sum for l<L of choose(-gamma/2,l) times the complete residue row. This identity includes L=0 and is used to identify the actual Q field."))),
                DescribeRole.Theorem))));
}
