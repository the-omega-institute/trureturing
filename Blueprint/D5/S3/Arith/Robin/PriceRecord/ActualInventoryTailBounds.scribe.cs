using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualInventoryTailBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform tail and adjacent-layer reductions support the exact own-clock Robin separator.",
        H("Uniform tail and adjacent-layer reductions"),
        Blocks(Describe.Lean(
            DescribeId.Create("actualinventorytailbounds"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualInventoryTailBounds.layer_pair_of_clock_product"),
            H("Uniform tail and adjacent-layer reductions"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The source supplies the corresponding real-clock estimates at primes 17,19,23,29,31, the 37 tail and the 34/35 cutoff endpoints, and the literal barrier tests at 32 and 36.9. The adjacent-layer theorem converts a clock-product interval and two exact gain identities into strict included/excluded price comparisons for arbitrary p,k and real clock L. It is applied to all supported rows of the actual integer witness. All numeric endpoints are proved using the existing RobinRationalBasis suppliers; no external interval certificate or new checker is trusted.")),
                Paragraph(Text("The concrete original integer clock is proved and instantiated in ActualInventoryCollectiveSeparation; it is not replaced by a freely chosen real clock. These suppliers are in the live proof of its finite-product refutation. No RH, global original Robin minimum, or originality claim is made. Four-slot registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/27332; mathematical compilation does not assert declared_validated."))),
            DescribeRole.Theorem))));
}
