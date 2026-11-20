using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class BooleanDeletionParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mass differences on a finite Boolean cube with equal deletion marginals.",
        H("A parity formula for the mass difference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boolean-deletion-mass-difference"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/BooleanDeletionParity.boolean_deletion_mass_difference"),
                H("Agreement after deleting each coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take two real mass functions on a finite indexed Boolean cube. For each "
                        + "coordinate and assignment of the other bits, assume the two functions "
                        + "have equal sums over the two values of the omitted bit. Write d for "
                        + "the full parity sign moment of the first function minus that of the "
                        + "second. At each vector, the mass difference is d divided by the size "
                        + "of the cube, times the vector's parity sign. Total variation is half "
                        + "the absolute value of d.")),
                    Paragraph(Text(
                        "Equal deletion marginals force the mass difference to change sign at "
                        + "each single-bit flip. Flipping the coordinates in the support of a "
                        + "vector recovers its difference from the value at the all-zero vector. "
                        + "Summation against the parity sign fixes the coefficient. For a "
                        + "minimal dependent group of binary outputs, the joint law and the "
                        + "product of its marginals agree after every deletion, so this "
                        + "identity gives the distance between those two laws."))),
                DescribeRole.Theorem))));
}
