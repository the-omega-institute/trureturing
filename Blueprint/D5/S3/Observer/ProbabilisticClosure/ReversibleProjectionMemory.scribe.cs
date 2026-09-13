using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class ReversibleProjectionMemoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a self-adjoint finite transfer operator and an orthogonal projection, the two-step compression defect is the Gram matrix of hidden leakage.",
        H("Reversible Projection Memory and Two-Step Closure"),
        Blocks(
            Paragraph(Text("K acts on a finite-dimensional real observable space. P is an orthogonal projection when it is both idempotent and self-adjoint. To interpret this as a Markov state quotient, the range of P must be the whole algebra of functions of the proposed observation, not merely an arbitrary selection of slow eigenfunctions.")),
            Describe.Lean(
                DescribeId.Create("defect-eq-hidden-roundtrip"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleProjectionMemory.defect_eq_hidden_roundtrip"),
                H("The exact missing hidden round trip"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every idempotent P, the difference P K squared P minus (P K P) squared is P K (I-P) K P. This algebraic identity does not require stochasticity or reversibility and displays precisely the work removed by projecting again between the two steps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("defect-eq-leakage-gram"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleProjectionMemory.defect_eq_leakage_gram"),
                H("Self-adjoint dynamics make the defect noncancelling"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If K and P are self-adjoint, the defect equals the conjugate-transpose product of leakage (I-P) K P with itself. Thus opposite hidden channels cannot cancel the discrepancy. Reversible chains with nonuniform equilibrium require a separate transport to orthonormal L2(pi) coordinates; that transport is not assumed proved here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-step-closure-iff"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleProjectionMemory.two_step_closure_iff"),
                H("Exact two-step agreement characterizes the invariant observation space"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defect vanishes if and only if K P equals P K P, by the pinned matrix Gram-zero theorem. The reverse implication is not asserted for non-self-adjoint K. Exact invariance is stronger than small empirical error at a chosen lag."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compressed-positive-powers"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleProjectionMemory.compressed_positive_powers"),
                H("Closed one-step propagation extends to every positive time"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the actual invariance equation, induction identifies P K^(t+1) P with (P K P)^(t+1) for every natural t. Only positive powers are stated: the identity on the projected subspace is P, not the ambient identity matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-steps-iff-all-positive-times"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleProjectionMemory.two_steps_iff_all_positive_times"),
                H("Two-step and all-positive-time exactness are equivalent here"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the reversible orthogonal setting, zero two-step defect is equivalent to the full positive-integer compression identity. This is an exact finite-dimensional operator statement. It does not infer physical kinetics from equilibrium sampling or assert that a learned neural operator satisfies the assumptions."))),
                DescribeRole.Theorem)),
        [
        ]));
}
