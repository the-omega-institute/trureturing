using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class RationalGramOddPrimeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/AURICOmega/RationalGramOddPrime";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd-prime obstruction to rational Gram realization in six coordinates.",
        H("Seven coordinates for a rank-four unit Gram matrix"),
        Blocks(
            Describe.Lean(DescribeId.Create("has-unit-gram"),
                DeclarationHandle.Create(Module + ".hasUnitGram"),
                H("The prescribed Gram entries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The diagonal entries are one. The upper-triangular entries in row order "
                    + "are −1/3, −1/2, −1/2, 1/6, 1/6, and 1/4."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("realizable-iff"),
                DeclarationHandle.Create(Module + ".realizable_iff"),
                H("Exactly seven coordinates are necessary and sufficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Four rational unit vectors with the prescribed Gram entries "
                        + "exist in n coordinates exactly when n is at least seven.")),
                    Paragraph(Text("An invertible rational change of basis makes their Gram form "
                        + "diagonal with entries 1, 2, 3, and 3. In six coordinates, rational "
                        + "reflections align the first three vectors with an explicit frame. The "
                        + "last vector must then express three as six times a rational square "
                        + "plus two rational squares. After denominators are cleared, reduction "
                        + "modulo three forces both unweighted coordinates to be divisible by "
                        + "three. Divide the equation by three and reduce again to force the "
                        + "same divisibility for the remaining coordinate and the denominator. "
                        + "Descent rules out a positive denominator.")),
                    Paragraph(Text("In seven coordinates, four orthogonal vectors with squared "
                        + "lengths 1, 2, 3, and 3 give an explicit realization after the inverse "
                        + "change of basis. Padding with zero coordinates preserves the Gram "
                        + "entries in every larger dimension."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex"))]));
}
