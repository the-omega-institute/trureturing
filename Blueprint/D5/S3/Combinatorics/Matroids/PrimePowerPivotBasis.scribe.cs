using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PrimePowerPivotBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PrimePowerPivotBasis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral basis concentrates a weight vector modulo a prime power.",
        H("Weight Concentration at a Prime Power"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("primary-pivot-basis"),
                DeclarationHandle.Create(Module + ".primary_pivot_basis"),
                H("Concentrating the insertion weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite basis with natural weights, at least one of which is nonzero, and a positive prime power, choose an index of nonzero weight."
                    + " Change only that basis vector."
                    + " Its weighted value agrees with the original weighted vector modulo a multiple of the prime power."
                    + " The proof extracts the weight gcd and uses a coordinate whose normalized weight is a unit in the residue ring."))),
                DescribeRole.Theorem))));
}
