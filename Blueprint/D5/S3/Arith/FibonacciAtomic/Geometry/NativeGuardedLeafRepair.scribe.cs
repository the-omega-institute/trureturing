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
                        + "its final domain is the original D predicate. Minimality is componentwise undominated cost, over every finite successful history at every depth.")),
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
                        "Every history lifts to an arbitrary native context by prefixing "
                        + "its actual call addresses with the hole address. The source "
                        + "replacement identity gives its literal final context. Guarded "
                        + "growth preserves D, old material addresses and the induced old "
                        + "edges; those unchanged addresses retain their root depths. "
                        + "The native execution carries arbitrary rational values through "
                        + "each zero extension, moves an alpha's raw binding to its new "
                        + "marker, and on a split moves the old beta-terminal binding "
                        + "to the new left marker while assigning the next raw integer "
                        + "to the right alpha. These computations presume the originally "
                        + "earned raw/canonical correspondence and do not acquire it.")),
                    Paragraph(Text(
                        "This result concerns only the four leaf frontiers and their source "
                        + "specific witnesses and lower bounds. It does not settle the global "
                        + "recursive frontier, rational determinant claims, acquisition, "
                        + "field operations, storage, traffic, or joint resource optima."))),
                DescribeRole.Theorem))));
}
