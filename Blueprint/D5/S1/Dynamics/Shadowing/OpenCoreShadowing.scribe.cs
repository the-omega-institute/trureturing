using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class OpenCoreShadowingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Dynamics/Shadowing/OpenCoreShadowing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/peng2026shadowing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Open pullbacks and an open compact shadowing core yield a forward-shadowing one-step extension.",
        H("Pullbacks and open-core shadowing"),
        Blocks(
            Node("open-pullback", "An open map remains open under pullback", "fibrePullbackSecond_isOpenMap",
                "If p:T to B is open and rho:S to B is continuous, the second projection from the fibre pullback of p and rho onto S is open. The proof uses neighborhoods in the product and subspace topologies and does not assume rho is open. The projection is continuous; compact Hausdorff factors give a compact Hausdorff pullback.", DescribeRole.Theorem),
            Node("binary-shift-shadowing", "Forward shadowing for the binary full shift", "coreShift_uniformHasShadowing",
                "Finite-prefix entourages are cofinal in the uniformity of binary names. Diagonal splicing of a controlled forward pseudo-orbit supplies one name tracing all times, including time zero.", DescribeRole.Theorem),
            Node("open-core-extension", "Shadowing for an open one-step extension", "open_core_extension_hasShadowing",
                "Let P and S be compact Hausdorff uniform spaces. Suppose h:P plus S to S is continuous, open, and onto, restricts on S to a continuous map g, and g has finite-open-cover shadowing. Then x maps to inr(h(x)) on the disjoint sum has shadowing. Finite shrinking controls are chosen before the pseudo-orbit. One core tracer controls all later times, while openness and surjectivity of h supply the separate lift at time zero.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);
}
