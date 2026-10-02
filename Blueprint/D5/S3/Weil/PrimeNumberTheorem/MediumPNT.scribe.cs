using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeNumberTheorem;

internal sealed class MediumPNTDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/primenumbertheoremand2026medium");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Chebyshev psi error decays by an exponential power of logarithm.",
        H("MediumPNT"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("medium-p-n-t"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/MediumPNT.MediumPNT"),
                H("MediumPNT"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("There exists a positive real c such that the second Chebyshev function minus the identity is bounded asymptotically by a constant times x times exp of minus c times the one-tenth power of log x. Neither c nor the eventual multiplicative bound is asserted to be explicit."))),
                DescribeRole.Theorem))));
}
