using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class IntegerNegativeFamilyQuadraticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous integerization of negative subspaces",
        H("Simultaneous integerization of negative subspaces"),
        Blocks(Describe.Lean(
                DescribeId.Create("exists-integer-negative-family-quadratic-of-gap"),
                DeclarationHandle.Create("D5/S3/Constants/Moments/IntegerNegativeFamilyQuadratic.exists_integer_negative_family_quadratic_of_gap"),
                H("One integer matrix preserves a uniform negative gap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural k,d, real matrix M on Fin d by Fin d, real row matrix A on Fin k by Fin d, and positive real gamma, suppose that for every real vector t on Fin k the form sum_ab (sum_j t(j) A(j,a)) (sum_l t(l) A(l,b)) M(a,b) is at most minus gamma times sum_j t(j) squared. There exists one integer row matrix U such that the same form using U after real casts is strictly negative for every nonzero real t. No symmetry of M is assumed. Empty row and column index sets are included.")),
                    Paragraph(Text("The pullback Gram entries are finite polynomials in the whole row matrix. With eta equal to gamma divided by 2(k+1), a finite open intersection constrains every Gram-entry perturbation by eta. Nested componentwise rational density selects one rational matrix. The absolute change of the form is at most eta times (sum_j abs(t(j))) squared, at most gamma/2 times sum_j t(j) squared by finite Cauchy-Schwarz. Matrix.den and Matrix.num clear one nonzero denominator for all entries, multiplying the form by its positive square. Rows are never integerized separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-integer-negative-family-quadratic"),
                DeclarationHandle.Create("D5/S3/Constants/Moments/IntegerNegativeFamilyQuadratic.exists_integer_negative_family_quadratic"),
                H("Strict negativity on every direction can be integerized simultaneously"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural k,d, arbitrary real matrix M on Fin d by Fin d, and real row matrix A on Fin k by Fin d, assume the pullback form sum_ab (sum_j t(j) A(j,a)) (sum_l t(l) A(l,b)) M(a,b) is strictly negative for every nonzero real t on Fin k. There exists one integer matrix U with that same strict inequality for every nonzero real t. Neither symmetry nor a supplied quantitative gap is assumed; k=0 is included.")),
                    Paragraph(Text("On the compact unit sphere in the finite real Pi space, minus the pullback form divided by sum_j t(j) squared is continuous and positive. Compactness supplies a positive lower bound even when the sphere is empty. Normalize a nonzero vector and use degree-two homogeneity to obtain a uniform gap on all vectors. The preceding entrywise perturbation and common-denominator theorem then constructs U. This is finite-dimensional approximation of a supplied real negative subspace, not a statement that a particular spectral matrix has one."))),
                DescribeRole.Theorem))));
}
