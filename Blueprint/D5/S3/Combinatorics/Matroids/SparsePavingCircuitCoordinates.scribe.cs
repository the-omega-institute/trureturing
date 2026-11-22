using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SparsePavingCircuitCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed circuit equations for a family of omitted bases.",
        H("Circuit Coordinates for Sparse Paving Cores"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mem-weighted-circuit-residues-iff"),
                DeclarationHandle.Create(Module + ".mem_weightedCircuitResidues_iff"),
                H("Omitted coefficients and uniform deletion rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All bases have the stated rank, and the excluded sets of that rank have pairwise "
                    + "intersection at most two below the rank. The weighted residue group comprises "
                    + "the chains supported on the rank-sized subsets that vanish on the excluded "
                    + "sets, have zero weighted boundary, and satisfy every signed deletion row "
                    + "on a subset of size one greater than the rank. At most one excluded set "
                    + "lies in such a subset. Its contraction row replaces the corresponding "
                    + "uniform row up to an overall sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-paving-weighted-forms-equiv"),
                DeclarationHandle.Create(Module + ".sparse_paving_weighted_forms_equiv"),
                H("The alternating-form description"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a basis on which the covector takes the value one, the uniform deletion "
                    + "rows give covector multiplication and the weighted boundary gives vector "
                    + "insertion. Both operations vanish, and each omitted basis sets the "
                    + "corresponding alternating coefficient to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wedge-coordinate-zero-iff-differences"),
                DeclarationHandle.Create(Module + ".wedge_coordinate_zero_iff_differences"),
                H("The face coefficient as a form on differences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a basis where the covector takes value one, choose any representative "
                    + "vertex of the face. Subtract it from the other vertices to obtain vectors "
                    + "in the kernel of the covector. The face coefficient of the covector product "
                    + "vanishes exactly when the lower-degree alternating form vanishes on these "
                    + "differences."))),
                DescribeRole.Theorem))));
}
