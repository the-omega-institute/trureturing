using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Dynamics.Koopman;

internal sealed class FiniteKoopmanUnitaryDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Dynamics/Koopman/FiniteKoopmanUnitary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pullback by a finite permutation preserves observable norm, has inverse pullback, and periodic eigenvalues are roots of unity.",
        H("Finite Permutation Koopman Unitarity"),
        Blocks(
            Def("norm", "finiteObservableNormSq", "Finite observable norm",
                "The unnormalized squared l2 norm is the finite sum of squared pointwise complex norms."),
            Thm("isometry", "finiteObservableNormSq_koopman", "Permutation pullback preserves norm",
                "A finite permutation reindexes the norm sum without changing its value."),
            Thm("left-inverse", "koopman_inverse_left", "Inverse pullback cancels on the left",
                "Pullback along the inverse permutation recovers every observable after forward pullback."),
            Thm("right-inverse", "koopman_inverse_right", "Inverse pullback cancels on the right",
                "Forward pullback recovers every observable after pullback along the inverse permutation."),
            Thm("injective", "permutationKoopman_injective", "Permutation Koopman pullback is injective",
                "The explicit inverse makes the finite pullback one-to-one."),
            Thm("period", "koopman_eigenvalue_pow_period_eq_one", "Periodic eigenvalues are roots of unity",
                "A nonzero eigenfunction for a period-m permutation has eigenvalue whose mth power is one."),
            Thm("nonzero", "koopman_eigenvalue_ne_zero_of_positive_period", "Positive-period eigenvalues are nonzero",
                "A positive-period root-of-unity equation rules out zero eigenvalue for a nonzero eigenfunction."),
            Thm("identity", "identity_permutation_koopman", "Identity permutation gives identity pullback",
                "The identity finite state permutation fixes every observable.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator")),
        ]));

    private static DocumentBlock.Describe Def(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
