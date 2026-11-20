using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class GramDeterminantCauchySchwarzDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Schatten/GramDeterminantCauchySchwarz.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/mazhang2026mo512579");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For complex m×k matrices U and V, |det(U*V)|² ≤ det(U*U) det(V*V).",
        H("The Gram-determinant Cauchy–Schwarz inequality"),
        Blocks(
            Describe.Lean(DescribeId.Create("gram-cauchy-schwarz"),
                DeclarationHandle.Create(Prefix + "gram_cauchy_schwarz"),
                H("Gram determinants satisfy Cauchy–Schwarz"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For complex m×k matrices U and V, with U* the conjugate transpose, "
                    + "|det(U*V)|² ≤ det(U*U) det(V*V); the inequality is stated in the complex "
                    + "order, so it also says that the right side is real and nonnegative. Every "
                    + "m and k is allowed: for k = 0 both sides are 1, and for k > m both Gram "
                    + "determinants vanish. For a k-element set T of rows, listed in increasing "
                    + "order, put u_T = det U[T,:] and v_T = det V[T,:]. By the Cauchy–Binet "
                    + "formula det(U*V) = Σ conj(u_T) v_T, det(U*U) = Σ |u_T|² and det(V*V) = "
                    + "Σ |v_T|². The triangle inequality gives |det(U*V)| ≤ Σ |u_T||v_T|, and the "
                    + "Cauchy–Schwarz inequality for finite sums bounds the square of that sum by "
                    + "(Σ |u_T|²)(Σ |v_T|²). This is Lemma 2 of H. Ma and W. Zhang's note on "
                    + "MathOverflow 512579."))),
                DescribeRole.Theorem))));
}
