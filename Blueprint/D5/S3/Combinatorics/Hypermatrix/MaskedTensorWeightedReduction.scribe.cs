using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypermatrix;

internal sealed class MaskedTensorWeightedReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypermatrix/MaskedTensorWeightedReduction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/koprowski2026enumeration");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual tensor count and the weighted cell sum", H("Actual tensor count and the weighted cell sum"),
        Blocks(
            Describe.Lean(DescribeId.Create("masked-tensor-weighted-reduction"),
                DeclarationHandle.Create(Prefix + "masked_tensor_weighted_reduction"), H("Actual tensor count and the weighted cell sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite field F and k at least one, with the two original antitone masks and their full bounds, the cardinality of ActualCarrier equals q to k squared times (q minus one) to 2k times the actual eligible-permutation weight sum. Constructive pencil factors have scalar fibers of size q minus one. Unique triangular and cell coordinates identify the masked parameter set; the two triangular group orders multiply to q to k squared times (q minus one) to 2k plus one. Literal masked-cell elimination supplies the eligible weights, and cancellation of the strictly positive scalar factor yields the tensor count. All equivalences are constructed for these actual matrices; the statement assumes no orbit classification, bijection or count."))), DescribeRole.Theorem)
        ), []));
}
