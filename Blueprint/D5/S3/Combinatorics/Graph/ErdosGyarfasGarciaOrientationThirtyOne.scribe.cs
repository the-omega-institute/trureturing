using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ErdosGyarfasGarciaOrientationThirtyOneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Garcia's four normalized AGL(1,31) orientation instances cannot avoid a cycle of length 64 after H15 vertex replacement.",
        H("The p = 31 orientation instances have no solution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Some orientation of Garcia's p = 31 instance avoids 64-cycles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each multiplier a in {11,17,22,24}, take the right Cayley graph of the affine group over ZMod(31), with generators t=(-1,0), g=(a,1), and r=inverse(g). An orientation sigma chooses one of these three incident edge types at each base vertex. A bijection tau at each vertex sends that chosen type to port u and sends the remaining types to v and w in either order. The literal replacement has a copy of the fifteen-vertex gadget at every base vertex, its listed internal edges, and one external edge joining the assigned attachment vertices for each Cayley edge. The claim asserts that some multiplier a, some orientation sigma, and some compatible family tau give a replacement with no simple cycle of length 64."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The solvability assertion is false"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Neg, F.Sp, F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The p = 31 module supplies the four private certificate pairs tgtrrtrrrtgggg/tgtgtgtgtrtrrr, tgtggggtrrrtrr/tgtgtgtgtrrrtr, tgtgtrrrrrtggg/tgtgtrtggtrrtr, and tgtgtgggtrrrrr/tgtgtrtrrtggtr. The shared affine replacement theorem accepts their kernel-checked closure, prefix distinctness, incident-type partition and histograms.")),
                    Paragraph(Text("Translated-visit averaging forces at least ten compatible visits in one certificate cycle. The explicit gadget paths and cyclic external edges expand those visits to a simple 64-cycle, contradicting the universal avoidance clause."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("garcia-2026-erdos64-agl31-orientation"),
                    ResolutionKind.Refuted)))));
}
