using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MultiplierRootPolynomialSelectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MultiplierRootPolynomialSelection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplier invariance restricts the degrees present in a finite root polynomial.",
        H("Multiplier Root-Polynomial Selection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coeff-zero-of-mul-invariant"),
                DeclarationHandle.Create(Prefix + "coeff_zero_of_mul_invariant"),
                H("Nonresonant root-polynomial coefficients vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite subset of a field invariant under a nonzero multiplier, "
                        + "a coefficient of its monic root polynomial vanishes when the "
                        + "multiplier acts nontrivially on the corresponding elementary "
                        + "symmetric function. The proof uses the multiplier permutation, "
                        + "Mathlib's symmetric scaling identity, and Vieta's formula. "
                        + "It does not require characteristic zero."))),
                DescribeRole.Theorem))));
}
