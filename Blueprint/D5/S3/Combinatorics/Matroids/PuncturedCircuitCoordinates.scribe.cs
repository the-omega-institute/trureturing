using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PuncturedCircuitCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The residue equations for a uniform core with one omitted basis.",
        H("Circuit Coordinates with One Omitted Basis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mem-weighted-circuit-residues-iff"),
                DeclarationHandle.Create(Module + ".mem_weightedCircuitResidues_iff"),
                H("The missing basis imposes one vanishing coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let the bases on the full finite ordered ground be the subsets of the given rank "
                    + "except for the omitted set H. A residue chain satisfies the weighted circuit "
                    + "equations exactly when it vanishes off the given rank and on H, its weighted "
                    + "boundary vanishes, and each signed deletion sum on a set of size one greater "
                    + "than the rank vanishes. The circuit H yields one signed row for each singleton "
                    + "basis after contraction. That row agrees up to an overall sign with the "
                    + "deletion row on H joined with the singleton, since the H coordinate vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("punctured-weighted-forms-equiv"),
                DeclarationHandle.Create(Module + ".punctured_weighted_forms_equiv"),
                H("Alternating forms for the punctured core"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The residue equations are the uniform alternating-form equations together "
                    + "with vanishing on the omitted basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("punctured-pivot-forms-equiv"),
                DeclarationHandle.Create(Module + ".punctured_pivot_forms_equiv"),
                H("The omitted coordinate after pivoting"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose the pivot in the omitted basis. The residue module is isomorphic to "
                    + "the forms of one lower degree killed by insertion of the pivot, insertion "
                    + "of the weighted vector, and multiplication by the total size. The "
                    + "coefficient on the omitted basis with the pivot removed must vanish. It "
                    + "agrees with the original omitted coefficient up to its deletion sign."))),
                DescribeRole.Theorem))));
}
