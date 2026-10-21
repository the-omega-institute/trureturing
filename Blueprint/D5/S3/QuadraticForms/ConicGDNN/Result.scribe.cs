using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.ConicGDNN;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generalized doubly nonnegative cone inclusion for orthant and Lorentz products.",
        H("The product-cone inclusion"), Blocks(
            Describe.Lean(DescribeId.Create("conic-gdnn-inclusion-result"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/ConicGDNN/Result.result"),
                H("The dual approximation preserves extreme rays"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every nonnegative orthant dimension p, every finite number r of Lorentz blocks, and every family of positive spatial block dimensions, the dual of the zeroth homogeneous sum of squares approximation is contained in the positive semidefinite cone whose matrices send every extreme ray generator of the dual product cone into the product cone.")),
                    Paragraph(Text("Every symmetric rank-one matrix supplies a single-square quartic test, forcing positive semidefiniteness of a matrix in the dual approximation. For two product-cone vectors u and v, the two pullbacks along the Jordan square are sums of squares of homogeneous linear polynomials. Multiplying the certificates gives a homogeneous quartic sum of squares for half the sum of uv-transpose and vu-transpose. Dual trace positivity therefore gives a nonnegative pairing of u with Xv. Product-cone self-duality gives Xv in the cone for every cone vector v. Every extreme ray generator of the dual cone is a cone vector by this same self-duality.")),
                    Paragraph(Text("The cone-preservation proof applies to the entire dual cone and also allows zero spatial dimensions. The stated inclusion retains the positive spatial dimensions in the fixed claim. Symmetry, the Euclidean coordinate pairing, and the homogeneous quartic convex-hull definition are used exactly as specified."))),
                DescribeRole.Theorem))));
}
