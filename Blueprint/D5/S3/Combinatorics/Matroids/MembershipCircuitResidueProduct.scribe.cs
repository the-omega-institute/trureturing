using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class MembershipCircuitResidueProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/MembershipCircuitResidueProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficient exchange product at a common pivot.",
        H("Residue Product for Separated Petals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("membership-residue-product"),
                DeclarationHandle.Create(Module + ".membership_residue_product"),
                H("Exchange of separated coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let an omitted family consist of a previous family and one new member."
                    + " All omissions have the same size and contain a common pivot."
                    + " Suppose each pair differs on a membership class of size at least two."
                    + " In the associated parallel expansions, the product of the uniform and joint residue modules is integrally linearly equivalent to the product of the previous and single-omission residue modules."
                    + " The basis concentrates weights within classes and separates the coefficient of the new petal from those of the previous petals."))),
                DescribeRole.Theorem))));
}
