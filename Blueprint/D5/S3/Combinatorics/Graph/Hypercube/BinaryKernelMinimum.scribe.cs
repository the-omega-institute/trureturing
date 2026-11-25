using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class BinaryKernelMinimumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelMinimum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum binary adjacency-kernel supports of an even cube",
        H("Minimum binary adjacency-kernel supports of an even cube"),
        Blocks(
            Paragraph(Text("Write a vertex of the n-cube as a subset of its coordinate set. Its neighbors are the n singleton flips. A binary support S is in the adjacency kernel if each vertex has an even number of neighbors in S.")),
            Paragraph(Text("The crossing-pair bound and the dimension lower bound for nonempty supports are established in BinaryKernelCrossing. In particular, every nonzero kernel word in even dimension n ≥ 2 has weight at least n.")),
            Describe.Lean(
                DescribeId.Create("cube-minimum-support-iff-neighbor-shell"),
                DeclarationHandle.Create(Module + ".minimum_support_iff"),
                H("Minimum supports are neighbor shells"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For even n ≥ 6, a support S has size n and every vertex has an even number of neighbors in S if and only if S is the set of all singleton flips of some center.")),
                    Paragraph(Text("At a row with positive selected degree d, the crossing bound gives 2|S| ≥ 2d + d(n − d) = 2n + (d − 2)(n − d). At weight n, a positive degree is therefore either two or n. A row of degree n is a center whose shell exhausts S.")),
                    Paragraph(Text("If all positive degrees are two, translate a positive row to the empty set. There are two selected axes. Each pair consisting of a selected and an unselected axis lies in exactly one selected triple, since the pair already has one selected singleton neighbor. Each triple covers at most two crossing pairs. Counting the incidences by both fibers exhausts the weight budget, so every selected vertex is a singleton or a triple and each selected triple covers two crossing pairs.")),
                    Paragraph(Text("Choose one of those triples containing a selected axis. It cannot contain the other selected axis, since their pair already has two singleton neighbors. Extend the triple to a four-set avoiding the other selected axis. Any selected neighbor must be a triple containing the first selected axis and at least one of the original unselected axes. Uniqueness above that crossing pair forces the original triple to be the only neighbor, contradicting parity. Conversely a shell has even row counts n, two or zero, at distances zero, two or any other distance from its center.")),
                    Paragraph(Text("In the 114+144 fold of Hong–Wu–Xia Problem 2 the binary adjacency condition is on Q8. Taking n = 8, every weight-eight support in the two K₄,₄ arguments is the set of singleton flips of a center. Symmetric difference by that center sends the support to the eight singleton vertices, so these minimum supports form a single orbit under cube translations. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
