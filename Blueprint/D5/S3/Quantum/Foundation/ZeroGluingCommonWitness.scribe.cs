using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ZeroGluingCommonWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact convex zero fibers and one common confirmer.",
        H("Compact convex zero fibers and one common confirmer"),
        Blocks(
            Paragraph(Text("Work on the original finite-dimensional real carrier with a closed pointed generating cone C, a unit u strictly positive on nonzero cone points, the full normalized base K, every native pure point p, and the full original proper-effect interval. For each p, zeroFiber C u p contains exactly the x in K for which some proper confirmer of p vanishes at x.")),
            Describe.Lean(
                DescribeId.Create("zero-fiber-compact-convex-common-witness"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/ZeroGluingCommonWitness.zeroFiber_compact_convex_common_witness"),
                H("Zero gluing gives compact convex fibers and one common confirmer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every native pure p, the full-base zero fiber is compact and convex. The proof projects the compact relation of confirming effects and normalized states, then uses original zeroGluing for midpoint closure and closed dyadic approximation for arbitrary real convex combinations.")),
                    Paragraph(Text("If the zero fiber is nonempty, one original proper confirmer f confirms p and has {x in K | f(x)=0} equal to the entire zero fiber. A relative interior point and a small affine extrapolation force f to vanish at every fiber point by proper nonnegativity. The empty fiber is retained by the implication without selecting an interior point. No finite-pure, reciprocity, least-confirmation, or additional hypothesis is assumed."))),
                DescribeRole.Theorem))));
}
