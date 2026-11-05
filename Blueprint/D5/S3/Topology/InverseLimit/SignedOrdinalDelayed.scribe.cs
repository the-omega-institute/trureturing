using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalDelayedDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalDelayed.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual delayed ordinal successor on one prepared whole birth pack",
        H("Delayed successor with permanent reservoirs"), Blocks(
            Paragraph(Text("The input is the existing partial Predecessor through a proper ordinal a and the same Prepared Q used by ordinary execution. A DelayedTask specifies one old row theta<a, two distinct old whole-sequence labels source<a and target<a, disjoint clopen source and target supports, and target points in the original support clopens. The target is exactly Q.measure(theta,target,n)=dirac(y(n)); the source is exactly Q.measure(theta,source,n), supported on the disjoint source clopen. No subsequence is renamed as a whole sequence and no signed measure is normalized. The task supplies no new F, successor, history, final object or cofinality premise.")),
            Describe.Lean(DescribeId.Create("actual-delayed-result"),
                DeclarationHandle.Create(Owner + "exists_delayed_result"), H("One executed delayed Result"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("SignedDelayedSplit.exists_internal_delayed_split is executed once. Its source F is obtained from the actual predecessor F through Q.oldNu. Ordinary norm-preserving lifts, ordinaryPool and ordinaryReference provide the unaffected rows and old labels; genuine new-row references are chosen by signed weak-star compactness. The returned Y, Z, ordered column and coordinate insertion fill the existing SignedOrdinalSuccessor.Result without changing its field types.")),
                    Paragraph(Text("The source J is M(0) union M(1), and this union is added to the auxiliary I of the source row. Each M(e) is infinite and lies in the original source J intersect the permanent birth reservoir N(e). Every other old-label J is its actual constant-rho auxiliary column fibre. All old N values are read from the predecessor's unique birth entry, while the new-row old-label reservoirs use the actual column parity. Residual label a is constructed after final I by norm-preserving lifts and signed compactness, including the doubly new pair. These constructions prove A, B, C, infinitude, old I/J refinement, whole-support E and common every-choice regular bounded F for every pair.")),
                    Paragraph(Text("The source F chooses one regular signed measure of total variation at most one before every arbitrary lift on M(0) union M(1). Auxiliary F retains the same common-reference quantifier order; residual F uses whole-support locally constant tests on final I. The existing Result.literal_f, Result.literal_e, Result.birth_readback, Result.arrival_retains and Result.quantitative_g apply to this identical Result.")),
                    Paragraph(Text("DelayedCertificate is additional to the common A-F/G interface. On the same fixed M, its clopen separates every point of each original target fibre. It is transported through that Result's inverse coordinate equivalence and exact restrict_inverse equation to the literal successor cube. The original target whole sequence at the same strictly increasing column index has literal clopen value greater than thirteen forty-eighths on even columns and zero on odd columns; Result.G also retains the one-sixth bound. The auxiliary I contains precisely its column values, with the source M union added; target column membership in I is not asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("once-prepared-ordinary-delayed"),
                DeclarationHandle.Create(Owner + "exists_prepared_step"), H("Prepare once before treatment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under CH, choose Q once before ordinary or delayed semantics. This same Q admits every ordinary treatment and every locally eligible DelayedTask, with the full Result and same-event delayed certificate. The arrival API preserves N only; it does not constitute a canonical whole-label historical birth pack.")),
                    Paragraph(Text("This unit proves a local successor, not unified nextPredecessor, well-founded recursion, coherent global history, stable intrinsic scheduling, a final omega-one object or the full CH theorem."))), DescribeRole.Theorem))));
}
