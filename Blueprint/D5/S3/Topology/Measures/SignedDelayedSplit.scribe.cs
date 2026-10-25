using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedDelayedSplitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/SignedDelayedSplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Delayed whole-fibre signed splitting",
        H("Delayed whole-fibre signed splitting"),
        Blocks(
            Describe.Lean(DescribeId.Create("delayed-fibre-pools"),
                DeclarationHandle.Create(Owner + "exists_delayed_fibre_pools"),
                H("Two original source reservoirs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A continuous onto map from a compact first-countable space, a separating family of Boolean coordinates and eventual whole-support fibre constancy are given. Each of the two original source intersections J with N(e) is infinite and J is contained in I. Target points y(n) lie in their original supports and in a fixed clopen Q. The conclusion chooses actual points f(n) over y(n), infinite subsets S(e) of those exact intersections and points z(e) over Q. Along each S(e), f converges to z(e). For every clopen neighborhood A of z(e), the entire fibre over y(n) eventually lies in A along S(e).")),
                    Paragraph(Text("Compactness is applied to chosen points of the original fibres. Eventual coordinate constancy implies eventual constancy of any fixed clopen on each whole support. Thus convergence of the chosen points controls the full fibres; it does not assert that an old fibre is a singleton."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parity-ordered-split"),
                DeclarationHandle.Create(Owner + "exists_parity_ordered_split"),
                H("One split for the two pools and signed estimates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two infinite target pools have a common positive-variation reference limit on each fixed clopen. The target is the actual Dirac-labelled signed sequence, with its original supports, norm and regularity certificates. At column q the target index is chosen in pool q modulo two. The target slice lies over V(n) intersect Q; all finite auxiliary tests are fixed after that slice and before the auxiliary indices. The auxiliary rows have actual signed references, infinite pools and whole-support coordinate constancy. Their uniform every-lift signed marginal estimates are retained without replacing signed measures by positive measures.")),
                    Paragraph(Text("The ordered columns construct one closed Boolean split with onto old projection. Its true sheet lies over Q. On every selected original target support, including the portion outside Q, the new coordinate is constant on each whole old fibre. On the entire fibre over y(n(q)), it is true exactly for even q. Every norm-preserving signed target lift has mass greater than one sixth on the true sheet at even columns and zero at odd columns. Along any increasing auxiliary column selection with a fixed label, all norm-preserving signed lifts converge to one common regular signed measure of variation at most one.")),
                    Paragraph(Text("The two selected parity ranges remain infinite subsets of the original source-J and N(e). Their union is the chosen target-index range, which supplies the replacement source-J. Every successor source lift converges along that range by applying old signed F to its projection and using the absence of the true sheet above P. No singleton old fibre or new source reference limit is assumed. The pool theorem alone permits distinct cluster points. This split theorem requires a common positive-variation limit. Neither statement supplies the distinct-cluster delayed branch, residual-label initialization after a final enlarged I, literal ordinal successor coordinates or a well-founded raw history. These are additional obligations for the complete CH construction.")),
                    Paragraph(Text("The exact source telescopes are mirrored in Reg. The full four-slot information audit is unfinished; issue 21750 identifies the missing realization, lawful readout and whole-family variation and sensitivity evidence. No declared_validated registration is asserted."))),
                DescribeRole.Theorem))));
}
