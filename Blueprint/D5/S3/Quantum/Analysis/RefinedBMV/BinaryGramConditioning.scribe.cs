using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class BinaryGramConditioningDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp conditioning of the binary four-copy Gram blocks",
        H("Sharp conditioning of the binary four-copy Gram blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-binary-gram-conditioning"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/BinaryGramConditioning.spectralDefect_binary_conditioning"),
                H("Strict bound for every degree and positive pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a positive integer first degree and two distinct positive spectral values, " +
                    "the square of the two-and-two deficit is strictly less than twice the product of " +
                    "the two three-and-one deficits. The proof uses the finite geometric sums and an " +
                    "exact exponential certificate with a strictly positive remainder."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-binary-gram-conditioning-sharp"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/BinaryGramConditioning.gapDefect_binary_conditioning_sharp"),
                H("Optimal uniform constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Every real constant smaller than two fails for some positive integer degree " +
                    "and some pair of distinct strictly positive values. The larger value can be " +
                    "fixed at one. A limit at the singular endpoint and continuity yield the witness."))),
                DescribeRole.Theorem))));
}
