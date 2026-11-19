using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveKuperbergBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kuperberg bounds for smoothed intervals.",
        H("Kuperberg bounds for smoothed intervals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kuperberg-raw-implies-smoothed"),
                DeclarationHandle.Create(Prefix + "kuperberg_raw_implies_smoothed"),
                H("Kuperberg bounds for smoothed intervals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume KuperbergRaw, the real-weight third- and fourth-order specialization of Kuperberg, arXiv:2301.06095v1, Theorem 1.3. Every fixed shifted smoothed interval with positive smoothing parameter and nonnegative ordered endpoints belongs to the smooth positive-support weight class and has quadratic Fourier decay, by smooth_interval_admissible. The weighted moment identity converts the raw third moment and each of the three bilinear fourth-moment pairings into the finite-sieve expectation coordinates. Complex norms of real casts equal absolute values, so the same nonnegative constants give KuperbergSmoothed, uniformly in squarefree Q and natural h at least three, with exactly the stated density powers and error exponents."))),
                DescribeRole.Theorem))));
}
