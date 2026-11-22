using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PuncturedCircuitResiduePairsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PuncturedCircuitResiduePairs";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The effect of a vanishing coordinate on a weighted pair of residues.",
        H("Weighted Residue Pairs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-pair-equiv"),
                DeclarationHandle.Create(Module + ".weighted_pair_equiv"),
                H("Two weighted coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A pair of residues is killed by the total size. Imposing a vanishing weighted "
                    + "sum of its two coordinates gives one factor of the common gcd of the total "
                    + "size and the two weights, and one factor of the total size."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("punctured-pairs-equiv"),
                DeclarationHandle.Create(Module + ".punctured_pairs_equiv"),
                H("A distinguished pair with first coordinate zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In a family of weighted pairs, force the first coordinate of one particular "
                    + "pair to vanish. That pair contributes one factor whose order is the gcd "
                    + "of the total size and the second weight. The other pairs retain both "
                    + "of their factors."))),
                DescribeRole.Theorem))));
}
