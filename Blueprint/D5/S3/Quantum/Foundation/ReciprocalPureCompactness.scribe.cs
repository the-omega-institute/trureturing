using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;
internal sealed class ReciprocalPureCompactnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pure reciprocity closes the entire original pure locus.",
        H("Compactness of the original pure locus"), Blocks(
                Describe.Lean(DescribeId.Create("reciprocal-pure-compactness"),
                    DeclarationHandle.Create("D5/S3/Quantum/Foundation/ReciprocalPureCompactness.reciprocal_pure_compact"),
                    H("Pure reciprocity closes the entire extreme locus"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("On the same arbitrary finite dimensional original closed generating pointed cone and strictly positive original unit, assume full comparison reciprocity only on pairs of original pure endpoints. Then all of P=ext(K) is compact. No EB3, weakPair, label injectivity, closedness of P, least effect or finite pure decomposition is assumed. This proves the compactness conclusion of IX114.4 without using a finite-dimensional strengthening of Krein-Milman.")),
                        Paragraph(Text("For a sequence of original pure points tending to x in the compact full K, intersect the value-one faces of every original effect confirming x. This common face H contains x, is compact, and is extreme in K. A pinned compact extreme-point existence theorem supplies r extreme in H; extreme-face transfer makes r an original pure point. Select actual full-fiber minimizers at r along the sequence and take an effect subsequence limit. Joint evaluation shows the limit confirms x, so membership of r in H makes its value at r equal one. Pure PR compares those same minimizer values with any original confirmer of r along the labels. The pre-existing reciprocal endpoint exposure theorem supplies a confirmer whose whole value-one face is {r}. Taking limits forces this confirmer to equal one at x and hence x=r. Thus every ambient sequence limit is pure, closing P inside compact K.")),
                        Paragraph(Text("The common complete-fiber face and its moving-minimizer limit are the live cross-label bridge. Pinned Krein-Milman is used only for existence of an extreme point in a nonempty compact face, never as an unproved finite pure decomposition theorem. Compactness and exposedness alone carry no physical or literature-priority assertion."))), DescribeRole.Theorem))));
}
