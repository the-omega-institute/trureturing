using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class TwinedTraceMemoryObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identical symmetry-twined spectral data need not fix memory relative to an observation.",
        H("Twined Traces and Observer-Relative Memory"),
        Blocks(
            Paragraph(Text(
                "Take two copies of any finite real carrier, with a fixed observation retaining "
                + "the first copy. A group may act in exactly the same way on the two copies. "
                + "The theorem is stronger than the group case: the inserted matrix R may be "
                + "any matrix on that carrier, not only a represented group element.")),
            Describe.Lean(
                DescribeId.Create("all-twined-traces-exact-memory-separation"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TwinedTraceMemoryObstruction.twined_traces_and_exact_memory"),
                H("All power traces agree while the full memory kernels differ"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the two-dimensional multiplicity space use diagonal rates a,b, "
                        + "or the symmetric matrix with diagonal (a+b)/2 and off-diagonal "
                        + "(a-b)/2. Tensor both with the identity. Both commute with every "
                        + "I tensor R and with the same represented group action. Induction "
                        + "computes their entire power sequences. Each twined trace at time k "
                        + "equals (a^k+b^k) trace(R).")),
                    Paragraph(Text(
                        "The diagonal dynamics has zero hidden-return kernel. For the mixed "
                        + "dynamics, the exact kernel after k hidden steps is "
                        + "((a-b)^2/4)*((a+b)/2)^k times the fixed observation projector. "
                        + "The proof computes D C=((a+b)/2) C and then propagates all k. "
                        + "For a nonempty carrier and a different from b the lag-zero kernels "
                        + "differ. The observation is not conjugated along with the dynamics.")),
                    Paragraph(Text(
                        "This is not a construction of the Monster, a Moonshine module or a "
                        + "new Moonshine identity. A specific real representation can be substituted "
                        + "only after its actual carrier and action are supplied. Graded trace "
                        + "or character information does not automatically encode the alignment "
                        + "of a physical observation with multiplicity-space dynamics. No Markov "
                        + "stochasticity or physiological interpretation is asserted."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleProjectionMemory"))]));
}
