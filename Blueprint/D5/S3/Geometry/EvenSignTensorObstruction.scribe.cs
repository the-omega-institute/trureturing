using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class EvenSignTensorObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/EvenSignTensorObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dimension obstruction for antisymmetric bilinear operations under all rotations.",
        H("Special orthogonal bilinear dimension obstruction"),
        Blocks(
            Paragraph(Text(
                "Let I be an arbitrary finite coordinate set. The carrier is the standard "
                    + "real vector space of functions on I, and the symmetry group is the "
                    + "entire special orthogonal matrix group. A nonzero antisymmetric "
                    + "bilinear operation from two vectors to one vector, equivariant "
                    + "under every element of that group, requires exactly three coordinates.")),
            Paragraph(Text(
                "The proof uses half-turns changing the signs of exactly two coordinates. "
                    + "Repeated input coordinates give zero coefficients. Repeated output "
                    + "coordinates are excluded by a half-turn in the input plane. For "
                    + "three distinct coordinates outside dimension three, a fourth coordinate "
                    + "allows a half-turn fixing both inputs and negating the output coefficient.")),
            Paragraph(Text(
                "This is a necessary dimension condition. It does not construct or classify "
                    + "the operations in dimension three, identify an arbitrary inner product "
                    + "space with this coordinate model, or assert any physical space dimension. "
                    + "Replacing the full group by a smaller symmetry group changes the hypotheses.")),
            Describe.Lean(
                DescribeId.Create("even-sign-coordinate-sign"),
                DeclarationHandle.Create(Prefix + "coordinateSign"),
                H("Coordinate signs of a half-turn"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The selected two coordinates have sign minus one; every other coordinate "
                        + "has sign one. Distinct selected coordinates yield determinant one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("even-sign-third-order-tensor-obstruction"),
                DeclarationHandle.Create(Prefix + "tensor_eq_zero_of_card_ne_three"),
                H("Third-order tensor obstruction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A real coefficient array c indexed by three coordinates vanishes if "
                        + "c(i,i,k) is always zero, every pair-coordinate sign flip preserves "
                        + "the array, and the number of coordinates differs from three. "
                        + "The empty coordinate set is included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("special-orthogonal-bilinear-dimension-three"),
                DeclarationHandle.Create(Prefix + "special_orthogonal_equivariant_bilinear_card_eq_three"),
                H("Nonzero equivariant bilinearity requires three coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For B(u,v) = -B(v,u), real bilinearity and equivariance "
                        + "B(Ru,Rv) = R B(u,v) for every special orthogonal R imply "
                        + "that nonzero B is possible only when the cardinality of I is three. "
                        + "Diagonal half-turns are genuine elements of the full group; "
                        + "the tensor conclusion forces B to vanish on every basis pair."))),
                DescribeRole.Theorem)),
        []));
}
