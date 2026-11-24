using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9TetrahedronElevenDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEleven";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eleven-facet gap for capped tetrahedral supports",
        H("The eleven-facet gap for capped tetrahedral supports"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-eleven-tetrahedron-gap"),
                DeclarationHandle.Create(Module + ".tetrahedra_card_ne_eleven"),
                H("The eleven-facet gap for capped tetrahedral supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If there were eleven tetrahedra, the vertex-link incidence bound would confine the "
                        + "support to six or seven vertices. On six vertices, every tetrahedron is in two "
                        + "five-sets. The six five-sets can accommodate only eighteen incidences, "
                        + "whereas eleven tetrahedra would require twenty-two.")),
                    Paragraph(Text(
                        "On seven vertices, double counting finds a vertex occurring at least seven times. "
                        + "A coordinate permutation moves it to the chosen pivot. After taking complements, "
                        + "the pairs through that pivot form a graph with at most four edges. The pair cap "
                        + "forces a three-spoke star or a four-cycle. Its isolated vertices force all "
                        + "remaining triples, giving nine or twelve facets.")),
                    Paragraph(Text(
                        "The argument applies to the support of an oriented real cycle since a singleton "
                        + "coface cannot cancel in its boundary. For sharp contact blocks in the Q9 question, "
                        + "the shell is obtained by XOR translation on the transverse coordinates, followed "
                        + "by complementation. Hong, Wu and Xia's Problem 2 asks about the full 258-point "
                        + "candidate. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-twelve-triple-pivot-normal-form"),
                DeclarationHandle.Create(Module + ".card_eq_nine_or_twelve_with_pivot"),
                H("The twelve-triple normal form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A pivot with at most four incident triples determines the whole "
                        + "twelve-triple family. Every triple consists of an edge of a "
                        + "four-cycle and one of the three vertices off the cycle, "
                        + "including the pivot. Complementation on seven vertices "
                        + "gives the join of a triangle boundary and a four-cycle."))),
                DescribeRole.Theorem)),
        []));
}
