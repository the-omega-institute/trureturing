using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Distances;

internal sealed class FanCircleCapacityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Distances/FanCircleCapacity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/fan2026riesz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact measure-theoretic definitions in Fan's moving three-point circle capacity "
            + "conjecture.",
        H("Fan's moving three-point circle capacity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fan-circle-points"),
                DeclarationHandle.Create(Prefix + "points"),
                H("The moving three-point set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "points(phi,psi) is the actual set of the three complex unit-circle "
                        + "points at polar angles psi, phi, and minus phi."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fan-circle-energy"),
                DeclarationHandle.Create(Prefix + "energy"),
                H("Positive-order energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "energy(r,K,mu) is the double integral of dist(x,y)^r against a "
                        + "ProbabilityMeasure on the actual subtype K. Zero singleton masses "
                        + "are not excluded."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fan-circle-capacity"),
                DeclarationHandle.Create(Prefix + "capacity"),
                H("Negative-exponent Riesz capacity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "capacity(r,K) is the reciprocal-r power of the supremum of energy over "
                        + "all probability measures on K, matching Fan's convention for "
                        + "negative exponent minus r."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fan-circle-capacity-conjecture"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The moving three-point capacity is maximal at the isosceles endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every real r at least two and pi/2 < phi <= 2*pi/3, "
                            + "the capacity of the points at angles psi, phi and -phi is "
                            + "at most its value at psi = 2*pi - 3*phi whenever "
                            + "0 <= psi <= 2*pi - 3*phi.")),
                    Paragraph(Text(
                        "The proof represents every probability measure by all three "
                            + "singleton masses, including zero masses, and identifies the "
                            + "attained energy supremum with the classical three-point "
                            + "quadratic maximum. A unified positive-part formula is "
                            + "differentiable when the optimizer changes branch. Chord and "
                            + "cotangent identities, together with the real-power displacement "
                            + "inequality, make its derivative nonnegative throughout the "
                            + "motion. Monotonicity of the reciprocal-r power then gives the "
                            + "capacity inequality."))),
                DescribeRole.Theorem)),
        []));
}
