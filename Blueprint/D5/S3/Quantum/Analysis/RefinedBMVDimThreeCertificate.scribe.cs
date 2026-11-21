using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVDimThreeCertificateDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered scalar certificate for the refined BMV bounds",
        H("The ordered scalar certificate for the refined BMV bounds"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-ordered-criterion"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVDimThreeCertificate.criterion_nonneg_ordered"),
            H("Nonnegativity of the quartic in ordered scalar deficits"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "Writing the three ordered cube roots as a common base and two successive nonnegative increments yields a polynomial with nonnegative integer coefficients. Lean checks their signs for word counts five, six, and seven by packing the coefficients into an integer and testing one bit per coefficient. A coefficient bound prevents carries from changing the signs."))),
            DescribeRole.Theorem))));
}
