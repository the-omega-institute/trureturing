using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class PolynomialLocalFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A polynomial certificate for maximal derivative rank and actual local fibers.",
        H("Real polynomial maps: maximal rank and local fibers"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-rank-fiber-polynomial"),
            DeclarationHandle.Create("D5/S3/Geometry/PolynomialLocalFiber.exists_rank_fiber_polynomial"),
            H("A normalized polynomial certifies its nonvanishing locus"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For all natural source and target dimensions n and m, and every m-tuple p of real multivariate polynomials in n variables, let f(x) be their tuple of evaluations. There is a literal real multivariate polynomial D, a proof D is nonzero, and a source point a0 with D(a0)=1. At every a with D(a) nonzero, the derivative rank at a bounds the derivative rank at every source point. The statement includes zero dimensions, constant maps and rank zero.")),
                Paragraph(Text("The certificate is constructed from a maximum of the bounded integer-valued derivative rank. At a maximizing point a0, put R=range(Df(a0)), choose a projection P onto R and a section I with P composed with Df(a0) composed with I equal to the identity on R. In a finite basis of R, D(x) is the determinant of P composed with Df(x) composed with I. Its matrix entries are real polynomials: polynomial induction gives each derivative along a fixed vector, and a finite real linear combination gives each projected coordinate. Thus D(a0)=1. Whenever D(a) is nonzero, the compressed derivative is surjective and its range dimension forces rank(Df(a)) to be at least dim(R); global maximality supplies the reverse inequality. For rank zero this is the empty determinant, with value one.")),
                Paragraph(Text("For each such a and each specified open neighborhood U containing a, the theorem reuses C1LocalFiber.exists_local_fiber to produce a subspace K, a continuous linear map q, a parametrization k and a positive radius epsilon. The dimension of K plus rank(Df(a)) is n. On the K-ball, k is C1, k(0)=a, k(z) belongs to U, every polynomial value equals its value at a, and q(k(z)-a)=z. This last identity makes the parametrization injective on the ball. When m<n, K has positive dimension. A parameter of norm epsilon/2 then produces b in U, distinct from a, with all polynomial values unchanged. The result concerns an actual local fiber through the specified point, beyond a tangent kernel or a collision somewhere in U.")),
                Paragraph(Text("The analytic evaluation and determinant invertibility interfaces are supplied by pinned Mathlib. The real C1 local-fiber theorem is reused directly; its source credits BochaoKong's Apache-2.0 LeanPool constant-rank argument at commit 2b1ec889365345f19a45fa94b6457a4d92c96295. This is a reusable prerequisite in real polynomial geometry, with no claim of mathematical novelty or external open-problem settlement.")),
                Paragraph(Text("The certificate is a fixed projection determinant and need not be a coordinate minor. This theorem does not assert density in a quotient or in an actual matrix-product-state image. A rational quotient inverse, polynomial descent and the bridge to actual MPS states and phase equivalence remain separate obligations. The static differential and polynomial statements introduce no dynamics, time group, energy, physical clock or thermodynamic law."))),
            DescribeRole.Theorem))));
}
