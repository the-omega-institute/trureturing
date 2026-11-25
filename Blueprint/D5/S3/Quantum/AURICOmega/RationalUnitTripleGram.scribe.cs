using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class RationalUnitTripleGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational realization of a three-point unit Gram matrix in five coordinates.",
        H("Three unit vectors in five rational coordinates"),
        Blocks(Describe.Lean(DescribeId.Create("rational-five-coordinate-unit-triple"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/AURICOmega/RationalUnitTripleGram.rationalFiveCoordinateUnitTriple"),
            H("A three-square criterion"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let a and b be rational numbers with squares at most one, "
                    + "and let c be rational. The three prescribed inner products a, b and c "
                    + "are realizable by unit vectors in five rational coordinates exactly "
                    + "when their unit-diagonal Gram determinant is a sum of three rational squares.")),
                Paragraph(Text("Align the first unit vector with a coordinate axis by a rational "
                    + "isometry. The remaining four coordinates of the two other vectors form a "
                    + "pair of quaternions. The Gram determinant is the sum of the three squared "
                    + "imaginary coordinates of their relative product. Conversely, four squares "
                    + "construct the first quaternion and the three-square decomposition specifies "
                    + "the imaginary coordinates of the relative product. Inverting the first "
                    + "quaternion reconstructs the second. When the first residual vanishes, "
                    + "the determinant condition forces the residual inner product to vanish."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex"))]));
}
