using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal sealed class MazorchukXuFamiliesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shifting every upper coordinate by one gives an exact counted equivalence between the literal triangular family and bounded ordered-edge closure.",
        H("The counted point-to-edge bridge"),
        Blocks(
            Node("Families", "edgeTriangle", "The strict edge triangle", EdgeTriangle(),
                "The vertex set is zero through n+1, and every selected edge has strictly increasing endpoints.", DescribeRole.Definition),
            Node("Families", "edgeSet", "Points become edges", Shift(true),
                "Shift the second coordinate up by one. This map is injective on all natural pairs and preserves the zero first coordinate.", DescribeRole.Definition),
            Node("Families", "pointSet", "Edges become points", Shift(false),
                "Shift the second coordinate down by one. On strict natural edges this is inverse to edgeSet.", DescribeRole.Definition),
            Node("Families", "edgeFamily", "The bounded ordered-edge family", EdgeFamily(),
                "The notation pairMembership(A)(a,b) means (a,b) belongs to A. Every subset of the strict edge triangle is tested against both rules and the exact first-column statistic.", DescribeRole.Definition),
            Node("Families", "count_eq_edgeFamily_card", "Equality of the finite counts", Many("n k", N,
                Eq(Call("count",V("n"),V("k")),Call("card",Call("edgeFamily",V("n"),V("k"))))),
                "The two coordinate shifts are inverse on their bounded domains, preserve closure in both directions and preserve the first-column count. A finite-set bijection therefore gives the equality for all natural n and k. This includes empty subsets, zero first-column counts, n=0 and every valid deficit. It introduces no representation-theoretic assumption.", DescribeRole.Theorem)), []));

    private static Formula EdgeTriangle() => All("n",N,Eq(Call("edgeTriangle",V("n")),
        Set("p",Pairs,And(Lt(Call("fst",V("p")),Call("snd",V("p"))),Le(Call("snd",V("p")),Add(V("n"),D(1)))))));
    private static Formula Shift(bool up)
    {
        var p=V("p");var q=V("q");
        return All(up?"Y":"A",Points,Eq(Call(up?"edgeSet":"pointSet",V(up?"Y":"A")),
            Set("q",Pairs,Ex("p",V(up?"Y":"A"),Eq(q,Pair(Call("fst",p),
                up?Add(Call("snd",p),D(1)):Sub(Call("snd",p),D(1))))))));
    }
    private static Formula EdgeFamily() => Many("n k",N,Eq(Call("edgeFamily",V("n"),V("k")),
        Set("A",Points,And(Subset(V("A"),Call("edgeTriangle",V("n"))),
            Call("Rules",Call("pairMembership",V("A"))),Eq(Call("firstColumnCard",V("A")),V("k")))));
}
