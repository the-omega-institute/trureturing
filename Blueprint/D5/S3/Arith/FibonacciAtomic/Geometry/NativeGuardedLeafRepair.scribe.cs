using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeGuardedLeafRepairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact guarded original-leaf repair frontiers for actual material trees.",
        H("Native guarded leaf repair frontiers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-guarded-leaf-repair-result"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair.result"),
                H("Exact F/R cost frontiers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A source term is the repository's ordered Bool free magma. "
                        + "Material cells are the actual address roster, including retained "
                        + "beta markers, and adjacency is the native parent-child graph. "
                        + "A successful history is a finite list of guarded promote and split "
                        + "calls; its trace is the actual subtree replacement computation and "
                        + "its final domain is the original D predicate.")),
                    Paragraph(Text(
                        "F is an actual perfect matching of every material cell. R is an "
                        + "actual matching of every nonroot material cell while the existing "
                        + "root remains present and unmatched. Each promote adds one material "
                        + "cell and each split adds two, so the history cardinality identity "
                        + "gives the promotion parity lower bound. The beta right-rootless "
                        + "lower bound also uses the actual rootless cardinality and the "
                        + "guarded fact that no promotion can precede the first root split.")),
                    Paragraph(Text(
                        "The four witnesses are the empty alpha and beta histories, one root "
                        + "promotion from alpha, and the legal beta sequence split-at-root "
                        + "followed by promotion at the right child. Their matching edges are "
                        + "constructed on the actual address graph. Material addresses from "
                        + "the original term persist through every successful replacement; "
                        + "zero extension preserves every old rational value and assigns zero "
                        + "to fresh addresses.")),
                    Paragraph(Text(
                        "This result concerns only the four leaf frontiers and their source "
                        + "specific witnesses and lower bounds. It does not settle the global "
                        + "recursive frontier, rational determinant claims, acquisition, "
                        + "field operations, storage, traffic, or joint resource optima."))),
                DescribeRole.Theorem))));
}
