using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PrivatePairCircuitResidueProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PrivatePairCircuitResidueProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common pivot compares simultaneous restrictions for overlapping omissions.",
        H("The Residue Product for Private Pairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("private-pair-residue-product"),
                DeclarationHandle.Create(Module + ".private_pair_residue_product"),
                H("Adding an omission with private pairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a finite ordered ground set of size K and a rank r with 3 <= r < K."
                    + " Take a family consisting of a fresh omission and finitely many prior omissions, all of the specified rank size and containing a common element."
                    + " Each omission has two private elements."
                    + " Consider four cores whose bases are exactly the rank-sized sets with neither, both, just the prior family, or just the fresh omission removed."
                    + " Use the same surjection from a finite expanded ground set for the weights in all four cases."
                    + " In difference coordinates at the common element each omitted basis imposes zero at its petal coefficient."
                    + " The product of the uniform and jointly restricted weighted residue modules is integrally linearly isomorphic to the product of the two separately restricted modules."))),
                DescribeRole.Theorem))));
}
