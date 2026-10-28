using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class ClassicalQuantumGramDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/ClassicalQuantumGram.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-root Gram realization of canonical classical-quantum record states.",
        H("Classical-quantum Gram realization"),
        Blocks(
            Paragraph(Text("The label and fragment coordinate types are arbitrary finite types. Zero probabilities, singular conditional states, repeated eigenvalues and different row and column dimensions are permitted. For Y_x=p_x rho_x, form the rectangular matrix V whose x-th column block is the positive square root of Y_x. Its two Gram products are used without identifying their ambient spaces.")),
            Item("blockPinch", "Coordinate block pinching", "The map retains a matrix entry precisely when its two classical labels agree.", DescribeRole.Definition),
            Item("cqRowSqrt", "Rectangular row of square roots", "The row block indexed by x is the positive square root of p_x rho_x.", DescribeRole.Definition),
            Item("row_mul_adjoint", "Row Gram product is the mixture", "For nonnegative ensemble weights, cqRowSqrt times its adjoint equals the sum of the weighted density matrices. Normalization of the weights is not required. This identity supplies both the conditional pinching-gap identification and the labelled POVM decomposition.", DescribeRole.Theorem),
            Item("conditionalSubentropy", "Canonical conditional subentropy", "Conditional subentropy is subentropy(recordState) minus subentropy(mixtureState).", DescribeRole.Definition),
            Item("cq_conditional_eq_pinchingGap", "Conditional subentropy is a Gram pinching gap", "For the canonical recordState and mixtureState, conditional subentropy equals the block-pinching gap of V*V, where V=cqRowSqrt. The two rectangular Gram products have equal determinant-integral subentropy. The positive square-root identities identify the pinched Gram matrix with the record state and the row Gram matrix with the mixture state, including zero ensemble weights and singular fragments.", DescribeRole.Theorem),
            Item("pure_block_pinching", "Pure-state block gap and labelled upper bound", "For every normalized vector v on the label-fragment product, the pinching gap equals classical subentropy of the block squared norms. For every label x, the same gap is bounded above by one minus that block norm. The equality follows by rectangular Gram invariance and pure-state subentropy zero. The labelled bound integrates the existing classical determinant-kernel estimate with its integrable inverse-square majorant.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Item(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(text))), role);
}
