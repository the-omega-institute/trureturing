using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class FiniteAtomicHankelVandermondeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/FiniteAtomicHankelVandermonde.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite atomic Hankel moment matrices, their one-step shift, and their pencil "
            + "factor through one shared Vandermonde feature matrix with diagonal atomic weights.",
        H("Finite Atomic Hankel-Vandermonde Factorization"),
        Blocks(
            DefinitionNode(
                "finite-atomic-moment",
                "atomicMoment",
                "Finite atomic moment",
                "The weighted finite power sum of the atomic nodes."),
            DefinitionNode(
                "vandermonde-feature-matrix",
                "vandermondeFeatureMatrix",
                "Vandermonde feature matrix",
                "Rows are moment degrees and columns are atomic nodes."),
            DefinitionNode(
                "hankel-moment-matrix",
                "hankelMomentMatrix",
                "Hankel moment matrix",
                "Entry i,j is the atomic moment of degree i plus j."),
            DefinitionNode(
                "shifted-hankel-moment-matrix",
                "shiftedHankelMomentMatrix",
                "Shifted Hankel moment matrix",
                "Entry i,j is the atomic moment of degree i plus j plus one."),
            DefinitionNode(
                "hankel-moment-pencil",
                "hankelMomentPencil",
                "Hankel moment pencil",
                "The finite atomic pencil with diagonal weight w(a)(x(a)-lambda)."),
            Describe.Lean(
                DescribeId.Create("hankel-matrix-has-vandermonde-factorization"),
                DeclarationHandle.Create(
                    Prefix + "hankel_moment_matrix_factorization"),
                H("The Hankel matrix has a Vandermonde factorization"),
                StatementSource.FromAuthor(HankelFactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Expanding matrix multiplication and the diagonal weight matrix leaves one "
                        + "finite atomic sum; multiplication of node powers adds the two degrees."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shifted-hankel-matrix-has-the-same-features"),
                DeclarationHandle.Create(
                    Prefix + "shifted_hankel_moment_matrix_factorization"),
                H("The shifted Hankel matrix has the same features"),
                StatementSource.FromAuthor(ShiftedFactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The one-step moment shift is absorbed entirely into the diagonal atomic "
                        + "weight by multiplication with the node."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pencil-is-shifted-minus-lambda-times-unshifted"),
                DeclarationHandle.Create(
                    Prefix + "hankel_moment_pencil_eq_shifted_sub"),
                H("The pencil is shifted minus lambda times unshifted"),
                StatementSource.FromAuthor(PencilDifferenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity is entrywise and requires no rank or distinctness hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hankel-pencil-has-a-shifted-diagonal-factorization"),
                DeclarationHandle.Create(
                    Prefix + "hankel_moment_pencil_factorization"),
                H("The Hankel pencil has a shifted diagonal factorization"),
                StatementSource.FromAuthor(PencilFactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The factorization exposes the same localizing coordinate x minus lambda "
                        + "that appears in the finite Stieltjes mass-support pencil."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe DefinitionNode(
        string id,
        string declaration,
        string heading,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula HankelFactorizationFormula() =>
        F.Disp(F.Id("hankelEqualsVandermondeWeightTranspose"));

    private static Formula ShiftedFactorizationFormula() =>
        F.Disp(F.Id("shiftedHankelEqualsVandermondeNodeWeightTranspose"));

    private static Formula PencilDifferenceFormula() =>
        F.Disp(F.Id("pencilEqualsShiftedSubLambdaHankel"));

    private static Formula PencilFactorizationFormula() =>
        F.Disp(F.Id("pencilEqualsVandermondeShiftWeightTranspose"));
}
