using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class WuTransferReflectionBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/HilbertOperators/WuTransferReflectionBound.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A matrix-valued reflection estimate for the normalized signed-transfer polynomial.",
        H("Rank-one transfer reflection bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transfer-evaluation"),
                DeclarationHandle.Create(Owner + "transferEval"),
                H("Polynomial evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text(
                    "The coefficient sequence is evaluated at a complex argument through the finite "
                    + "matrix polynomial sum from degree zero through N in a finite complex matrix algebra."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("first-coefficient-reflection-bound"),
                DeclarationHandle.Create(Owner + "firstCoeff_le_of_reflection"),
                H("First coefficient bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text(
                        "Let N be positive. Assume a normalized matrix polynomial has Hermitian "
                        + "coefficients, constant coefficient I, and reflection product "
                        + "equal to the scalar product of 1 − aᵢ²z² with nonnegative real parameters "
                        + "aᵢ, allowing repetitions and zeros. Then its linear coefficient is at "
                        + "most (sumᵢ aᵢ)I in the Loewner order.")),
                    Paragraph(Text(
                        "The proof first bounds the normalized matrix function on the imaginary axis, "
                        + "extends the bound to the closed right half-plane by the maximum-modulus "
                        + "argument, and differentiates the real ray at zero. The complex matrix "
                        + "norm and C-star order are handled by the imported Mathlib analysis."))),
                DescribeRole.Theorem))));
}
