using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class MultisetRookEulerianNonrealCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/MultisetRookEulerianNonrealCertificate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The degree-nine factor and its full X-squared multiple do not split over the real field.", H("An exact Newton obstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("Q"),
                DeclarationHandle.Create(Prefix + "Q"), H("Q"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The degree-nine factor has ascending coefficients 1, 261, 21704, 591814, 5372605, 18550680, 27147806, 17137014, 4318325, 352440."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("P"),
                DeclarationHandle.Create(Prefix + "P"), H("P"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact rational translation of Q by minus 9/1000."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("translate-eq"),
                DeclarationHandle.Create(Prefix + "translate_eq"), H("translate_eq"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All ten coefficients of the exact translation are checked."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("translated-not-splits"),
                DeclarationHandle.Create(Prefix + "translated_not_splits"), H("translated_not_splits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Vieta and the existing real-root Newton inequality contradict the exact first three translated coefficients."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("factor-not-splits"),
                DeclarationHandle.Create(Prefix + "factor_not_splits"), H("factor_not_splits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translation preserves splitting; the degree-nine factor does not split over the real field."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-explicit-not-splits"),
                DeclarationHandle.Create(Prefix + "full_explicit_not_splits"), H("full_explicit_not_splits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Splitting of X squared times Q would imply splitting of Q. The full explicit polynomial does not split."))), DescribeRole.Theorem))));
}
