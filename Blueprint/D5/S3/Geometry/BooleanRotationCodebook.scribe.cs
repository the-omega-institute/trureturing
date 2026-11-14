using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class BooleanRotationCodebookDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Boolean rotation error fibers", H("Exact Boolean rotation error fibers"), Blocks(
        Describe.Lean(DescribeId.Create("boolean-rotation-circular-error"),
            DeclarationHandle.Create("D5/S3/Geometry/BooleanRotationCodebook.circularError"),
            H("Circular error with a prescribed period"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For real L and t, circularError L t is the norm of the class of t in AddCircle L. For positive L this is the infimum of the absolute values of t minus kL over all integers k. The period is retained as L; for planar rotation matrices the prescribed period is 2 pi. This scalar error does not identify matrices up to global phase."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("boolean-rotation-no-wrap"),
            DeclarationHandle.Create("D5/S3/Geometry/BooleanRotationCodebook.nonnegative_sum_no_wrap"),
            H("Finite first crossing"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Let s be any finite set of indices and a a real family. Suppose epsilon is nonnegative, three times epsilon is strictly less than L, and every a indexed by s lies between zero and epsilon. If the circular error of every subset sum is at most epsilon, the entire sum is at most epsilon. Induction removes one coordinate. The smaller sum is at most epsilon, so reinserting the coordinate gives a value between zero and twice epsilon. A nonzero multiple of L cannot be within epsilon of that interval. Thus its nearest multiple is zero and the entire sum remains at most epsilon.")))),
        Describe.Lean(DescribeId.Create("boolean-rotation-all-queries"),
            DeclarationHandle.Create("D5/S3/Geometry/BooleanRotationCodebook.booleanError"),
            H("One residual vector for every Boolean query"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For one fixed residual vector a on a finite index type, booleanError L epsilon a requires circularError L of the sum over s to be at most epsilon for every finite subset s. Subsets are exactly the Boolean queries. The vector is chosen before quantifying over queries."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("boolean-rotation-signed-body"),
            DeclarationHandle.Create("D5/S3/Geometry/BooleanRotationCodebook.signedBody"),
            H("The signed simplex difference"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The signed body consists of vectors for which the sum of the positive parts and the sum of the negative parts are each at most epsilon. For positive epsilon this is epsilon times the difference of two standard coordinate simplices: split a into its positive and negative parts, and conversely bound those parts by the two nonnegative summands."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("boolean-rotation-exact-fiber"),
            DeclarationHandle.Create("D5/S3/Geometry/BooleanRotationCodebook.exact_error_fiber"),
            H("Exact principal error fiber"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For every finite index type, nonnegative epsilon and L greater than three times epsilon, let a have all coordinates of absolute value at most L divided by two. Then all Boolean subset sums have circular error at most epsilon if and only if a belongs to the signed body. Singleton queries first bound each coordinate by epsilon. Apply the finite first crossing theorem to the nonnegative coordinates and then to the negated nonpositive coordinates. Conversely every subset sum lies between minus the total negative mass and the total positive mass; projection to the circle cannot increase its absolute value.")),
            Paragraph(Text("For L equal to 2 pi, the strict range is epsilon less than 2 pi divided by three. The fiber characterization covers every finite dimension, including zero. It concerns a fixed residual vector and supplies no arbitrary-decoder, computational-time, finite-hardware, learning or empirical conclusion. The finite-codebook cardinality bounds additionally require the exact volume of this body, its measure-preserving passage to the torus, a finite covering inequality and a simultaneous grid construction; those statements are not conclusions of the fiber characterization."))))) ));
}
