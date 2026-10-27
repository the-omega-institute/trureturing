using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedBallHistoryEndpointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All signed analytic endpoints on the actual CH limit, without a supplied history or oscillation premise.",
        H("Signed endpoints of the actual ordinal history"), Blocks(
            Describe.Lean(DescribeId.Create("actual-signed-ball-history-endpoints"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/SignedBallHistoryEndpoints.actual_signed_ball_history_endpoints"),
                H("Oscillation, the whole signed ball, Grothendieck convergence and point sequences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "The only premise is continuum = aleph-one. Every conclusion uses exactly K = (SignedOrdinalRealization.finalPrefix hCH).LimitSpace. "
                        + "For arbitrary regular signed t(n) with totalVariation.real(univ)=1, positive Jordan mass at least one half, and variation carried by pairwise disjoint nonempty clopens W(n), there is one clopen Z with infinitely many evaluations at least one sixth and infinitely many exact zeros.")),
                    Paragraph(Text(
                        "Countable signed reflection and original whole-birth enumeration capture the entire sequence at one original birth and label. Actual treatment cofinality supplies the same selected successor Result. Exact projection and measure identities transport its arbitrary signed G law without changing labels or natural indices. "
                        + "SignedBallHistoryCapture.signed_clopen_collision applies the same actual RawHistory and proper F laws to obtain two distinct free ultrafilters agreeing under every weak-dual evaluation. SignedBallReduction then excludes an injective continuous map from all of StoneCech Nat into the entire real weak-star dual unit ball.")),
                    Paragraph(Text(
                        "The remaining clauses quantify over arbitrary dual sequences F(n), a dual limit FInf, and all continuous bidual tests Phi: pointwise convergence on C(K,Real) implies convergence under Phi, with no supplied uniform bound. "
                        + "For every point sequence x(n) converging to p in this same K, eventually x(n)=p. Both follow from the proved full regular signed oscillation through SignedGrothendieckCriterion. The joint construction theorem consumes all four clauses."))),
                DescribeRole.Theorem))));
}
