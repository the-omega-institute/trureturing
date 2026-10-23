using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MultivariateEnergy;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/bilykferizovicglazyrinmatzkeparkvlasiuk2022multivariate");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multivariate spherical energies and their averaged pair kernels.",
        H("Spherical energy definitions"), Blocks(
            Describe.Lean(DescribeId.Create("multivariate-energy-sigma"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.sigma"),
                H("Normalized surface measure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The unit sphere is the subtype of real Euclidean space consisting of vectors of norm one. Normalized surface measure is the radial spherical measure of volume, scaled by the inverse of its total mass."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multivariate-energy-energy"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.energy"),
                H("Multivariate energy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The energy of a kernel at a Borel measure is its integral against the product measure with that same measure in every input."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multivariate-energy-avgkernel"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.avgKernel"),
                H("The averaged pair kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("All inputs except the last two are integrated against normalized surface measure. The last two inputs remain free."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multivariate-energy-iscondposdef"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.IsCondPosDef"),
                H("Conditional positive definiteness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The quadratic expression is nonnegative for the difference of any two finite positive Borel measures of equal mass. By Jordan decomposition this is exactly the condition for finite signed measures of total mass zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multivariate-energy-isadmissible"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.IsAdmissible"),
                H("Admissible kernels"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A kernel is continuous, invariant under permutations of the inputs, and invariant under every orthogonal transformation of the sphere. The counterexample satisfies this stronger invariance, hence also invariance under rotations."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multivariate-energy-isminimizer"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.IsMinimizer"),
                H("Energy minimization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A minimizing measure has energy no greater than that of every Borel probability measure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multivariate-energy-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.claim"),
                H("The averaged pair characterization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every dimension at least two and every arity at least three, normalized surface measure minimizes an admissible kernel exactly when the averaged pair kernel is conditionally positive definite. The orthogonally invariant class contains the counterexample to the source assertion, whether rotations are interpreted as the special or full orthogonal group."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multivariate-energy-surface-probability"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.sigma_isProbabilityMeasure"),
                H("Surface measure is a probability measure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive dimension the spherical measure has finite nonzero total mass, so inverse-mass scaling gives total mass one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("multivariate-energy-centered-family"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.familyKernel"),
                H("The three-input centered family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Put A(x)=xx transpose minus I/d, L(x,y)=tr(A(x)A(y)), and T(x,y,z)=tr(A(x)A(y)A(z)). The three-input kernel is beta divided by three times the sum of its three pair traces, minus its triple trace."))), DescribeRole.Definition))));
}
