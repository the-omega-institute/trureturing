using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ErdosGyarfasGarciaOrientationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Garcia's four normalized AGL(1,29) orientation instances cannot avoid a cycle of length 64 after H15 vertex replacement.",
        H("The p = 29 orientation instances have no solution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Some orientation of Garcia's p = 29 instance avoids 64-cycles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each multiplier a in {3,8,10,11}, take the right Cayley graph of the affine group over ZMod(29), with generators t=(-1,0), g=(a,1), and r=inverse(g). An orientation sigma chooses one of these three incident edge types at each base vertex. A bijection tau at each vertex sends that chosen type to port u and sends the remaining types to v and w in either order. The literal replacement has a copy of the fifteen-vertex gadget at every base vertex, its listed internal edges, and one external edge joining the assigned attachment vertices for each Cayley edge. The claim asserts that some multiplier a in {3,8,10,11}, some orientation sigma, and some compatible family tau give a replacement with no simple cycle of length 64. Thus it is the solvability assertion for Garcia's p = 29 instance."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The solvability assertion is false"),
                StatementSource.FromAuthor(F.Disp(F.Seq(F.Neg, F.Sp, F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The shared ErdosGyarfasGarciaOrientationBase module supplies the affine words interface, literal H15 gadget, path checks and generic certificate theorem. This module keeps the p = 29 certificate words private; its public declarations are claim and result. ErdosGyarfasGarciaOrientationAveraging supplies the general finite-sum argument; ErdosGyarfasGarciaOrientationExpansion supplies the general disjoint-block cycle construction. The two certified simple fourteen-cycles have unused-edge multiplicities (6,4,4) and (2,6,6). Bijective left translation and the weighted averaging identity force a translate of one of these cycles with at least ten visits whose two cycle edges include the chosen u-edge. Select exactly ten such visits. In their gadget copies use the explicit simple three-edge path; in the four remaining copies use the explicit simple five-edge path.")),
                    Paragraph(Text("The fourteen translated base vertices are distinct, so their internal path blocks are disjoint. The literal external attachment edges join their endpoints in cyclic order. The generic disjoint-block expansion lemma gives a simple cycle. Its length is fourteen external edges plus ten times three and four times five internal edges, which is 64. This refutes the solvability assertion for the paper's undecided normalized p=29 orientation cases; it does not settle the unrestricted Erdős-Gyárfás conjecture."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("garcia-2026-erdos64-agl29-orientation"),
                    ResolutionKind.Refuted)))));
}
