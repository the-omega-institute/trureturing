using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class CorrelationMinorNormQubitBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormQubitBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp unrestricted separable qubit fourth-order maximum", H("Sharp unrestricted separable qubit fourth-order maximum"), Blocks(
            Entry("qubit-scaling-definition", "qubitScaling", "qubitScaling",
                "The actual qubit coordinate scaling is diag(1,sqrt(3),sqrt(3),sqrt(3)).", DescribeRole.Definition),
            Entry("scaled-correlation-trace-norm", "scaled_correlation_traceNorm", "scaled correlation traceNorm",
                "For an arbitrary actual finite separable decomposition and every finite D, the existing real rectangular CFC trace norm of the transposed scaled correlation is at most sqrt(2). Hermitian Parseval and actual local density purity bounds justify the coordinate estimates.", DescribeRole.Theorem),
            Entry("qubit-fourth-bound-definition", "qubitFourthBound", "qubitFourthBound",
                "The universal fourth-order constant is 1/(192 sqrt(3)).", DescribeRole.Definition),
            Entry("qubit-fourth-bound-alice", "qubit_fourth_bound_alice", "qubit fourth bound alice",
                "For arbitrary finite Bob dimension and arbitrary complete normalized Bob basis, every actual finite p≥1 and infinity fourth-order quantity is bounded by the universal constant in the normalized Pauli Alice basis. Zero and rank-deficient cases are included.", DescribeRole.Theorem),
            Entry("qubit-fourth-bound", "qubit_fourth_bound", "qubit fourth bound",
                "For every D≥2, every actual separable qubit-by-D state and arbitrary complete normalized local Hermitian bases, every actual finite p≥1 and infinity fourth-order quantity is at most 1/(192 sqrt(3)). No FNF, decomposition-size or purity restriction is introduced.", DescribeRole.Theorem),
            Entry("qubit-sharp-maximum", "qubit_sharp_maximum", "qubit sharp maximum",
                "For every D≥4, the bound is the exact maximum over all separable states, and the actual tetrahedral zero-noise density state attains it simultaneously for every finite p≥1 and infinity. No sharpness at D=2,3 or classification of all maximizers is asserted.", DescribeRole.Theorem),
            Entry("coherent-pair-obstruction-with-attainment", "coherent_pair_obstruction_with_attainment", "coherent pair obstruction with attainment",
                "For every D≥5, no common-size pair of the precisely defined regular coherent degree-one pure designs exists in dimensions two and D; nevertheless the actual tetrahedral state attains the unrestricted full-order maximum. This does not refute every reading of the broad design hypothesis or classify maximizers.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
            Blocks(Paragraph(Text(text))), role);
}
