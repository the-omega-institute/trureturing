using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalPureCompactnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalPureCompactness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compactness of the entire original pure carrier under PR",
        H("Compactness of the entire original pure carrier under PR"), Blocks(
            Paragraph(Text("V is an arbitrary finite dimensional real normed space, C a pointed cone, and u its original linear unit. Where stated, C is closed and generating and u is strictly positive on nonzero C. K is the entire normalized base and P its entire extreme locus. All original linear effects between zero and u are retained; the full confirming family F(p) includes u. Pure reciprocity exchanges only two pure endpoints. No mixed reciprocity, matrix specialization, weakPair, unit-width assumption or global uniform-fiber premise is used.")),
            Describe.Lean(DescribeId.Create("original-pr-pure-compact"), DeclarationHandle.Create(Owner + "original_pr_pure_compact"),
                H("PR pure compactness without Inj or weakPair"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume V nonzero finite dimensional, C closed, pointed and generating, u strictly positive on nonzero C, EB and pure PR. Then the entire original pure locus P is compact. A nonpure normalized state has a strict convex decomposition with a pure endpoint: at an intrinsic interior point extend a ray through that point; at a boundary point use the existing frontier cover and the lawfully exposed original radial decomposition in its actual exclusion chart. Uniform mixed-input comparison continuity and PR force T(r,x)=1 at any putative nonpure limit x of pure labels. The exact original endpoint-exposure theorem has an original confirmer taking one only at r, contradicting x different from r. No Inj, supplied pure compactness, weakPair, unit widths, P0 restriction or matrix model is used. The proof here retains EB for the decomposition; it does not claim the EB-free generalization in IX114.4."))), DescribeRole.Theorem))));
}
