using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourZhuAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Norm-Four Zhu Algebra and Monic Cubic Presentation.",
        H("Actual Norm-Four Zhu Algebra and Monic Cubic Presentation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normfourzhualgebra-quotientproduct"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientProduct"),
                H("Actual descended star product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every lattice D with invertible determinant, norm-four charge a and complex s with s squared equal to one, the product on the original additive quotient S/O descends from the actual bilinear star on S. On a homogeneous left state of weight n, star is the full sum of binomial(n,j) times u_(j-1)v for j from zero through n. Canonical finite homogeneous expansion extends it to every left state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourzhualgebra-quotientring"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientRing"),
                H("Actual commutative quotient ring"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D with invertible determinant, norm-four a and s squared equal to one, this commutative ring reuses the original quotient addition, the actual descended star product and the actual vacuum class as unit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourzhualgebra-quotientalgebra"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.quotientAlgebra"),
                H("Compatible complex algebra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D with invertible determinant, norm-four a and s squared equal to one, the existing complex module on S/O is compatible with the actual quotient ring. Complex constants map to scalar multiples of the vacuum class."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourzhualgebra-actual-zhu-algebra"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.actual_zhu_algebra"),
                H("Actual star algebra and dimension three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite integral symmetric even-diagonal lattice D with IsUnit D.G.det, charge a with B(a,a)=4, and complex s with s squared equal to one, the original literal Zhu quotient has its actual star algebra structure. The class of star(u,v) equals the product of the classes of u and v for all u,v in S. The quotient is finite dimensional of dimension exactly three. Its actual axis class x satisfies x(x-1/16)(x-1/2)=0, where the constants are supplied by the compatible complex algebra."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normfourzhualgebra-zhupolynomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.zhuPolynomial"),
                H("Monic axis polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex polynomial is P=X(X-C(1/16))(X-C(1/2))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourzhualgebra-actual-zhu-presentation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourZhuAlgebra.actual_zhu_presentation"),
                H("Actual monic cubic presentation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite integral symmetric even-diagonal lattice D with IsUnit D.G.det, charge a with B(a,a)=4, and complex s with s squared equal to one, P is monic and there exists a complex algebra equivalence from AdjoinRoot(P) to the original literal Zhu quotient with its actual star product. The equivalence maps the adjoined root to the actual axis class x. That class also satisfies 64 x cubed minus 36 x squared plus 2 x equals zero, using the original complex scalar action. There is no rank-24 hypothesis."))),
                DescribeRole.Theorem),
            Paragraph(Text("Actual word grading gives a unique finite homogeneous expansion. Mixed ambient Sugawara and axis commutators identify each word grade with its ambient source energy. The theta-fixed source and mode closure apply to the whole descendant space. Actual energy covariance makes high physical modes vanish on the complete first oscillator grade, and preserves that grade under zero modes.")),
            Paragraph(Text("The full production residue law proves that the original literal O annihilates this actual first grade and that star acts by composition. The circle specialization uses both ordered families; the star specialization retains the unique surviving first-family term and annihilates the complete second family. Every fused result grade is shown nonnegative before conversion to a natural number.")),
            Paragraph(Text("The general actual multiplicity equations imply rank at least two and positive dimensions of the zero, one-sixteenth and one-half eigenspaces. Their scalar readouts separate the images of the same three representatives: identity, the actual axis zero mode L, and L squared plus 2L. Actual filtered spanning then proves that the kernel of the actual action is exactly literal O. Both argument kernels of star follow. The descended faithful action proves associativity, the vacuum unit and commutativity.")),
            Paragraph(Text("The additive finite-dimensional upper bound is consumed from NormFourZhuFinite; the three actual spectral fibers give the reverse bound. The actual first-grade polynomial supplies the cubic relation. Representative multiplication and the circle relation identify the second representative class with x squared plus 2x. These classes make the AdjoinRoot map surjective; equality of the two dimensions makes it injective.")),
            Paragraph(Text("This realizes the classical Zhu construction and the central-charge-one-half Virasoro cubic presentation in the actual lattice carrier. It adds no assumed basis, ideal, associative product, abstract representation, positive form or rank specialization. Rationality, fusion, a full Monster construction, analytic CFT and string realization are not established here.")))));
}
