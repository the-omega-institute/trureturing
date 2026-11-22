using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PuncturedCircuitWeightBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PuncturedCircuitWeightBasis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral basis adapted to the omitted basis.",
        H("Weight Directions for a Punctured Core"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-punctured-weight-basis"),
                DeclarationHandle.Create(Module + ".exists_punctured_weight_basis"),
                H("An integral basis for the two blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Keep the pivot and choose a basis separately inside the omitted set with the pivot "
                    + "removed and outside the omitted set. The weights in each block lie on one basis vector "
                    + "with scalar the gcd of that block's weights. The alternating coefficient in the "
                    + "omitted block vanishes in the original basis exactly when it vanishes in the new "
                    + "basis."))),
                DescribeRole.Theorem))));
}
