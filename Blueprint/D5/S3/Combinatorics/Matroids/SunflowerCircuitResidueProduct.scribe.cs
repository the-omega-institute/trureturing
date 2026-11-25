using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SunflowerCircuitResidueProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SunflowerCircuitResidueProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The uniform, previously punctured, singly punctured and jointly punctured cores share a common coordinate model.",
        H("The Sunflower Residue Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sunflower-residue-product"),
                DeclarationHandle.Create(Module + ".sunflower_residue_product"),
                H("The Sunflower Residue Product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a rank of at least three below the ground size, and use cores on the same "
                    + "finite ordered ground set. Their bases are the rank-sized sets after the "
                    + "respective omissions. The prior omissions and the new omission all contain "
                    + "a common element and their petals are pairwise disjoint. A surjection from the "
                    + "finite expanded ground set gives the weights. Use the common element as the "
                    + "pivot. Each omission imposes the vanishing of its petal coefficient in "
                    + "difference coordinates. Sector exchange identifies the integral product of "
                    + "the uniform and jointly punctured residue modules with the product of the "
                    + "two separately punctured modules."))),
                DescribeRole.Theorem))));
}
