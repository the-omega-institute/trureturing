using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SparsePavingCircuitProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SparsePavingCircuitProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four residue modules for the two omissions.",
        H("The Product Identity for Sparse Paving Residues"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sparse-paving-residue-product"),
                DeclarationHandle.Create(Module + ".sparse_paving_residue_product"),
                H("Independent restrictions from two omitted bases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The uniform core and the three cores obtained by omitting either or both bases have the "
                    + "same weighted insertion equations after choosing a pivot. For each omitted basis, its "
                    + "coefficient vanishes on the associated tuple of differences. An integral basis puts both "
                    + "tuples along separate intersections with the zero-weight indices. The unrestricted and "
                    + "doubly restricted modules then have the same product as the two singly restricted modules."))),
                DescribeRole.Theorem))));
}
