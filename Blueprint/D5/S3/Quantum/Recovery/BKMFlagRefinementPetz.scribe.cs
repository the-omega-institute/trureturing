using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMFlagRefinementPetzDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMFlagRefinementPetz.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common classical flag refinement preserves binary testing and the actual partial-trace Petz error and entropy loss.",
        H("Binary testing and ordinary Petz under classical flag refinement"),
        Blocks(
            Paragraph(Text(
                "For each parent flag, choose a finite child set and weights summing to one. " +
                "Apply the same weights to both block families. The joint matrices are block " +
                "diagonal on the retained space and the flag space. Taking the right partial " +
                "trace sums the blocks, so each retained marginal is unchanged.")),
            Entry("binary-testing", "refine_binary_testing", "The weighted testing norm is preserved",
                "For any two block families, any real coefficient p, and nonnegative normalized " +
                "weights, the trace norm of p times the first joint matrix minus (1 − p) times " +
                "the second is unchanged by refinement. The weighted difference refines block " +
                "by block. The trace norm adds over direct sums, and each child contributes its " +
                "weight times its parent's norm. For density matrices and p in [0, 1], the " +
                "Helstrom formula gives equality of the optimal binary Bayes risks."),
            Entry("partial-trace-petz", "partialTracePetz", "Ordinary Petz for the right partial trace",
                "Given a joint reference, sandwich the retained input by the inverse square root " +
                "of the reference marginal. Tensor the result with the flag identity, then " +
                "sandwich by the square root of the joint reference. The lift is the adjoint of " +
                "the right partial trace for the Hilbert–Schmidt pairing. The formula gives the " +
                "ordinary Petz map when the reference and its marginal are faithful. For " +
                "positive definite reference blocks, a nonempty parent flag set ensures " +
                "faithfulness of the retained marginal.",
                DescribeRole.Definition),
            Entry("petz-blocks", "petzBlocks", "Petz recovery in each reference block",
                "For a block diagonal reference, every output block uses the same retained " +
                "inverse-square-root sandwich. Its outer factors are the square root of that " +
                "block of the reference. Assembling these blocks gives the ordinary Petz output.",
                DescribeRole.Definition),
            Entry("joint-trace-norm", "traceNorm_joint", "Trace norm adds over flag blocks",
                "For any finite family of square complex matrices S indexed by the flags, "
                + "the trace norm of joint(S) equals the sum of the trace norms of its blocks.",
                DescribeRole.Lemma),
            Entry("joint-petz", "partialTracePetz_joint", "Petz recovery respects the flag blocks",
                "For positive definite reference blocks T and any retained input matrix X, "
                + "partialTracePetz(joint(T), X) equals the joint matrix of petzBlocks(T, X).",
                DescribeRole.Lemma),
            Entry("petz-intertwines", "refine_ordinaryPetz", "Petz recovery intertwines with refinement",
                "For positive definite reference blocks and strictly positive normalized weights, " +
                "every retained input matrix has the same refined output whether one recovers " +
                "against the refined reference or refines the recovered blocks. The marginal " +
                "inverse square root is unchanged, while each of the two outer square roots " +
                "contributes a factor equal to the square root of the child weight. The " +
                "matrix identity also holds for empty flag sets."),
            Entry("petz-trace-error", "refine_petz_error", "The actual trace-norm recovery error is preserved",
                "Recover the actual right marginal of the input using the respective old or " +
                "refined reference. For arbitrary input blocks, positive definite reference " +
                "blocks and strictly positive normalized weights, the trace norm of the input " +
                "joint matrix minus the recovered joint matrix is unchanged. The refined error " +
                "matrix is obtained by applying the same weights to the blocks of the old error."),
            Entry("matrix-relative-entropy", "relativeEntropyOfMatrices", "The finite trace-log expression",
                "Take the real trace of the input multiplied by its matrix logarithm minus the " +
                "reference logarithm, with the difference formed before multiplying. For a " +
                "positive semidefinite input and a faithful reference this is the Umegaki " +
                "trace expression. Zero eigenvalues of the input contribute zero to its " +
                "own logarithm term.", DescribeRole.Definition),
            Entry("partial-trace-entropy-loss", "partialTraceEntropyLoss", "Loss across the actual right partial trace",
                "Subtract the trace-log expression for the two retained marginals from the " +
                "trace-log expression for the two joint matrices.", DescribeRole.Definition),
            Entry("entropy-loss", "refine_entropy_loss", "Both joint relative entropy and its partial-trace loss are preserved",
                "Assume positive semidefinite input blocks, positive definite reference blocks " +
                "and strictly positive normalized weights. The joint trace-log expression is " +
                "unchanged, and the actual partial-trace loss is unchanged. On a child block, " +
                "scaling both arguments by the same weight adds a logarithmic shift on their " +
                "respective supports. Multiplication by the input kills its kernel, so these " +
                "shifts cancel in the trace even for singular input blocks. The remaining term " +
                "scales by the weight and sums to the original joint expression. Both " +
                "marginal matrices agree before and after refinement."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
