using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class RationalBlochTetrahedronDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The tetrahedral inner product on the rational Bloch sphere.",
        H("A rational coordinate obstruction for tetrahedral Bloch readings"),
        Blocks(Describe.Lean(DescribeId.Create("rational-bloch-tetrahedral-triangle"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/AURICOmega/RationalBlochTetrahedron."
                + "no_rational_bloch_tetrahedral_triangle"),
            H("Three rational Bloch unit vectors cannot have the tetrahedral inner product"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Suppose three unit vectors have rational coordinates in the three-dimensional "
                    + "pure-imaginary quaternion subspace. Multiply each vector by a common positive "
                    + "denominator d. The integer vectors have squared lengths d squared. "
                    + "An inner product of minus one third would make three times each off-diagonal "
                    + "inner product equal to minus d squared. The theorem excludes this system.")),
                Paragraph(Text(
                    "In three coordinates the Gram determinant is the square of the determinant "
                    + "of the coordinate matrix. Equating it to the tetrahedral Gram determinant "
                    + "would give a rational square root of three."))),
            DescribeRole.Theorem))));
}
