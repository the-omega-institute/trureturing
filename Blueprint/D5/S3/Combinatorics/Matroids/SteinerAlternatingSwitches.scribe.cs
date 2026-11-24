using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerAlternatingSwitchesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerAlternatingSwitches";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Large alternating components identify all successful starts in a point-deleted Steiner system.",
        H("Alternating Components and Maximal Steiner Switches"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pivot-graph"),
                DeclarationHandle.Create(Module + ".pivotGraph"),
                H("The graph of the two pivot matchings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write e(a) for the inclusion of the retained label a, skipping the deleted point and then adjoining an extra point to the carrier. Join each vertex to its partners under the translations through the deleted point and through e(v) for the fixed retained pivot v."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("successful-start"),
                DeclarationHandle.Create(Module + ".SuccessfulStart"),
                H("A successful starting label"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a retained packing P and a partner map m on its labels, a start a is successful at pivot v if v differs from a and from m(a), and there exist labels b and d such that both {a,v,b} and {m(a),v,d} lie in P and d differs from m(b)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("successful-starts"),
                DeclarationHandle.Create(Module + ".point_deleted_successful_starts"),
                H("All successful starting labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Delete any point q from a finite complete Steiner triple system on r+1 points and pull back the blocks avoiding q to the r retained labels. This is a partial Steiner system. One map m on the retained labels works for all pivots, with the pair a,b uncovered exactly when m(a)=b. Embed each retained label by first skipping q in the original point set and then including that point into the carrier with an adjoined point. For every retained pivot v, the component of the adjoined point is exactly that point, q, the embedded v, and the embedded m(v). The image of the successful starts under this embedding is exactly the set of vertices in components with at least six vertices in the union of the translations through q and the embedded v. If four divides r, the set of successful starts has at least six elements for every v.")),
                    Paragraph(Text("The square containing the adjoined point also contains the deleted point, the retained pivot, and its leave partner. All vertices outside the square are eligible retained starts. Pair completion gives the two switch blocks. Their switch is successful exactly where the translations disagree in the two orders. Such a disagreement yields six distinct vertices reached by alternating steps. At a commuting vertex the four corners close under both matching steps. The enlarged carrier has r+2 points, so divisibility of r by four forces a large component."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-deficit"),
                DeclarationHandle.Create(Module + ".point_deleted_first_deficit_of_four_dvd"),
                H("The first deficit without a switch hypothesis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix positive row dimension d and nonzero residue modulus 3r. Suppose every pair (x,a),(y,b) from distinct rows occurs in a listed triple with specified third point (−(x+y),−(a+b)). Every listed triple has three distinct rows and product sum zero. A given pair of distinct points occurs in at most one indexed triple. If a complete Steiner system exists on r+1 points and four divides r, write N for 3^d r^2 plus 3^(d+1) times floor(r(r−2)/6). Internal extensions add distinct-point triples within rows, preserve pair uniqueness and keep the dimension of the normalized potential space equal to d+1. They are saturated when inclusion maximal among such extensions. There are saturated extensions with N and N−1 added triples, and every internal extension adds at most N triples.")),
                    Paragraph(Text("Choose a successful start at any retained pivot and apply the one-class switch construction. The matching packing supplies the upper bound in every class."))),
                DescribeRole.Theorem))));
}
