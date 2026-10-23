using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MultivariateEnergy;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multivariate spherical energies and their averaged pair kernels.",
        H("Spherical energy definitions"), Blocks(
            Describe.Lean(DescribeId.Create("multivariate-energy-surface-probability"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.sigma_isProbabilityMeasure"),
                H("Normalized surface measure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unit sphere is the subtype of real Euclidean space of dimension d consisting of vectors of norm one. Surface measure is the spherical measure from radial disintegration of volume, multiplied by the inverse of its total mass. For positive d it is a Borel probability measure."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("multivariate-energy-characterization-claim"),
                DeclarationHandle.Create("D5/S3/Analytic/MultivariateEnergy/Defs.claim"),
                H("The averaged pair characterization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The characterization quantifies over every dimension at least two and every arity at least three. A continuous symmetric kernel invariant under orthogonal transformations is minimized by normalized surface measure exactly when its averaged pair kernel is conditionally positive definite. The latter property tests the quadratic energy of differences of two finite positive measures with equal total mass, which is the Jordan formulation for finite signed measures of mass zero.")),
                    Paragraph(Text("The matrix feature is A(x)=xx transpose minus I/d. Its pair and triple traces define a symmetric family by averaging over all unordered pairs and triples of inputs. Increasing enumeration selects the indices in each subset. The energy uses the product of the same measure in every input; the averaged pair kernel integrates all inputs except the last two against normalized surface measure."))),
                DescribeRole.Definition))));
}
