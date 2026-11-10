using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;
internal sealed class BoundedPowerCorrectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded corrections on prime-power chains", H("Bounded corrections on prime-power chains"), Blocks(
            Describe.Lean(DescribeId.Create("boundedpowercorrection-bounded-power-corrections"),
                DeclarationHandle.Create("D5/S3/Arith/Congruence/BoundedPowerCorrection.bounded_power_corrections"), H("Bounded corrections on prime-power chains"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural exponent s at least two and every bounded integer correction sequence, divisibility of the corrected-weight differences at successive powers of every prime forces a(p^r)=p-1 for all positive r. The base step uses a(1)=0 and the residue at p. Higher steps use s*(r-1)>=r and uniqueness of the bounded residue. The original square proof and the uniform integer-weight family use this same induction. The known square result is due to Su; no literature novelty is inferred."))), DescribeRole.Theorem))));
}
