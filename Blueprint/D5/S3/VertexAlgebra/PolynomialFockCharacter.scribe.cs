using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/PolynomialFockCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete polynomial Fock zero-mode character is the partition Euler product.",
        H("Polynomial Fock Character"),
        Blocks(
            Paragraph(Text("The theorem uses the actual Sugawara L_0 eigenspaces from "
                + "Polynomial Fock LZero Spectrum. The shared PositiveEnergyPartition "
                + "module supplies the pure energy fibre and ordinary partition "
                + "equivalence under the original public namespace. An exponent vector "
                + "of energy N is converted to a multiset of positive parts by replacing "
                + "index i with part i + 1 and repeating it d i times. The resulting "
                + "formal graded dimension is the unshifted partition Euler product.")),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-zero-mode-euler-character"),
                DeclarationHandle.Create(Prefix + "lZero_character_euler_product"),
                H("The concrete zero-mode formal character is the Euler product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The power series whose N-th coefficient is the "
                    + "complex finrank of the actual lZeroEigenspace N equals the "
                    + "infinite product over j >= 1 of (1 - X^j)^(-1). This result is "
                    + "the unshifted graded dimension identity; it does not construct "
                    + "state fields, a Virasoro center, Monster action, fusion data, "
                    + "or a vacuum-energy shift."))),
                DescribeRole.Theorem))));
}
