using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class ThreeStateMemoryKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-dimensional hidden mode yields an exact geometric memory and a sharp recovery obstruction.",
        H("All-Lag Memory of the Reversible Three-State Chain"),
        Blocks(
            Paragraph(Text(
                "This module uses the existing kernel(a,b) and the existing conditional-expectation "
                + "projection merging states zero and one. It does not invent a new hidden carrier. "
                + "The hidden block has multiplier lambda=1-2a-b/2; this is not asserted to be "
                + "an eigenvalue of the full chain.")),
            Describe.Lean(
                DescribeId.Create("actual-three-state-geometric-memory"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/ThreeStateMemoryKernel.feedback_geometric"),
                H("Every memory lag is determined by the actual hidden block"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source first computes D C=lambda C on the actual matrices, then proves "
                    + "D^k C=lambda^k C for every natural k. The resulting return operator is "
                    + "lambda^k times the already defined two-step defect. Its (2,2) entry is "
                    + "therefore (b^2/2)lambda^k. For valid parameters with b>0, |lambda|<1; "
                    + "a nonzero lambda gives infinitely many nonzero coefficients despite "
                    + "the single hidden coordinate. Kernel support length is not a claim "
                    + "about the minimal autoregressive order or the full stochastic Markov order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonuniform-hidden-recovery-valid-probabilities"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/ThreeStateMemoryKernel.no_uniform_hidden_recovery"),
                H("Exact recovery is not uniformly stable as the coupling disappears"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any positive amplification C0, choose a=1/4 and b=1/(4(C0+1)). "
                    + "The normalized nonnegative vectors (1/2,0,1/2) and (0,1/2,1/2) have "
                    + "identical current observations and a fixed hidden contrast of one. "
                    + "Their complete projected one-step vectors differ in l1 by b, so this "
                    + "observed datum has C0 times its gap less than one. The future "
                    + "third-coordinate gap is nonzero. This is a parameter-uniform "
                    + "conditioning obstruction on a genuine stochastic family, not a "
                    + "failure of exact identifiability at a fixed nonzero coupling."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleThreeStateWitness"))]));
}
