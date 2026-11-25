using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVThreeSpectrumReductionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV comparison from a scalar discriminant",
        H("The refined BMV comparison from a scalar discriminant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-three-spectrum-log-gap-product"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumReduction.product_bound_of_log_gaps"),
                H("The product bound from scalar positivity in two log gaps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any first degree and any finite dimension, the product bound with three copies of the " +
                    "second factor follows from nonnegativity of the displayed quartic in two nonnegative log gaps. " +
                    "The first positive semidefinite matrix may have up to three distinct eigenvalues, with arbitrary " +
                    "multiplicities. Continuity includes repeated and zero roots. Cyclic word counting and the " +
                    "three-center trace pairing give the matrix inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-three-spectrum-log-gap-exponential"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumReduction.exponential_bound_of_log_gaps"),
                H("The exponential bound from the same scalar positivity condition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Under the same scalar hypothesis, the exponential lower bound holds for Hermitian inputs " +
                    "when the first matrix has at most three distinct eigenvalues. The dyadic trace comparison " +
                    "takes the product inequality to the exponential inequality."))),
                DescribeRole.Theorem))));
}
