using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteCriticalTraceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalTrace";
    private const string Title = "Trace recurrence and raw marginal for the seven-site chart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensitecriticaltrace-wordtrace-eq-matrixtrace"),
                DeclarationHandle.Create(Module + ".wordTrace_eq_matrixTrace"),
                H("Trace recurrence on aligned matrix pairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two bond matrices over a commutative ring whose traces are one and zero respectively, the recurrence using their determinants and mixed trace computes the matrix trace of any binary word. The proof reduces words in the basis formed by the identity, the two matrices, and their ordered product."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sevensitecriticaltrace-rawgram-eq-rawtwo"),
                DeclarationHandle.Create(Module + ".rawGram_eq_rawTwo"),
                H("Raw two-site marginal on the aligned chart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an aligned complex core, every entry of the split Gram with conjugated second invariants agrees with the raw two-site marginal of the seven-letter periodic trace-word amplitudes. The contraction sums over the five omitted binary sites."))),
                DescribeRole.Theorem))));
}
