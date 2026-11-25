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
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/ArithUnits/hunsucker1971binaryfoursquares")),
            Blocks(
                Paragraph(Text("Let a and b be rational numbers with squares at most one, "
                    + "and let c be rational. The three prescribed inner products a, b and c "
                    + "are realizable by unit vectors in five rational coordinates exactly "
                    + "when their unit-diagonal Gram determinant is a sum of three rational squares. "
                    + "Both bounds are needed. At (a,b,c) = (2,1,2) or (1,2,2) the determinant "
                    + "is zero, yet two unit vectors cannot have inner product two.")),
                Paragraph(Text("Align the first unit vector with a coordinate axis by a rational "
                    + "isometry. The remaining four coordinates of the two other vectors form a "
                    + "pair of quaternions. Clear their denominators and use the OmegaMath integer "
                    + "Gram identity. Dividing its three imaginary coordinates by the product of "
                    + "the two denominators gives the three rational squares. Conversely, four "
                    + "squares construct the first quaternion and the three-square decomposition "
                    + "specifies the imaginary coordinates of the relative product. Inverting "
                    + "the conjugate of the first quaternion reconstructs the second. When the "
                    + "first residual vanishes, the determinant condition forces the residual "
                    + "inner product to vanish.")),
                Paragraph(Text("For positive determinant the residual binary quadratic form is "
                    + "the rational version of the four-linear-square criterion attributed to "
                    + "Mordell in Hunsucker, Section 1. The rational proof also treats determinant zero."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Geometry/EuclideanSimplex/RationalUnitSimplex")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Quantum/AURICOmega/OmegaShadowBridge")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Quantum/Entanglement/Marginals/FibRationalBoundary")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Quantum/Entanglement/Marginals/RationalQubitMixedEndpoint"))]));
}
