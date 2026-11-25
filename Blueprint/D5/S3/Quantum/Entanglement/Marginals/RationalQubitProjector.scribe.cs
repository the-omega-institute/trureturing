using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class RationalQubitProjectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational rank-two qubit completion from a quadratic-form witness.",
        H("Joint qubit states from rational quadratic witnesses"),
        Blocks(Describe.Lean(DescribeId.Create("rational-qubit-projector"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Entanglement/Marginals/RationalQubitProjector."
                + "rational_rank_two_of_quadratic_witness"),
            H("A rank-two completion for two prescribed Bloch marginals"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take rational three-vectors a and b with squared lengths satisfying "
                    + "|a|² < |b|². Let y and v be rational three-vectors with y nonzero. Suppose "
                    + "a · y = b · v and |y|² = (1 − |b|²)|v|² + (b · v)². Then "
                    + "the two trace-one Bloch matrices for a and b are the partial traces "
                    + "of a positive semidefinite joint matrix with rational coordinates and "
                    + "rank exactly two.")),
                Paragraph(Text(
                    "The quadratic equation forces v to be nonzero. Divide y by |v|² to get u. Set k = b − (a · u)v and split a into its "
                    + "components parallel and perpendicular to u. The witness equations give "
                    + "k · v = 0 and |k|² + |u|²|v|² = 1. The corresponding sum of Pauli tensor "
                    + "terms is a traceless Hermitian involution. Its positive eigenspace has "
                    + "dimension two.")),
                Paragraph(Text(
                    "On this eigenspace the two components of a determine a Hermitian correction. "
                    + "Its square is a scalar times the identity and the scalar is less than one "
                    + "by the squared-length comparison. The identity plus the correction is "
                    + "positive definite, so the compression has rank two. One partial trace recovers both components of a. "
                    + "The other recovers b as the sum of k and (a · u)v."))),
            DescribeRole.Theorem))));
}
