using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDiscriminantChargeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original charge sectors in the doubled Gram quotient",
        H("Representatives and rational shifts"), Blocks(
        Paragraph(Text("Let G be the unimodular integral Gram matrix. Doubling the Gram keeps the same integer coordinates and replaces the lattice of representatives of zero by the image of 2G.")),
        Describe.Lean(DescribeId.Create("original-fourm-doubled-gram-quotient"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.classOf_gram_eq_iff"),
            H("Equality in the literal quotient"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The classes of Ga and Gb in the actual cokernel of 2G agree exactly when a and b reduce to the same mod-two charge."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-doubled-gram-sector-equivalence"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.sectorEquiv_reduceCharge"),
            H("The additive sector equivalence"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The equivalence sends the original reduction of a to the class of Ga. Since G is invertible over the integers, every class has a representative of this form."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-doubled-gram-dual-shift"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.dualVector_gram_image"),
            H("The rational dual shift"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Applying the existing dual-vector map for 2G to Ga gives a/2 in every original coordinate."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-fourm-doubled-gram-dual-sector"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.dual_sector_iff"),
            H("All half-charges in a sector"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A rational point whose doubled Gram image is integral and of the specified discriminant class is exactly a half-charge whose reduction is the given original charge sector."))),
            DescribeRole.Theorem))));
}
