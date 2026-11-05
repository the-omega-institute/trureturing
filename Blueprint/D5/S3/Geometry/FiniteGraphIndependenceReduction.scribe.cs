using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteGraphIndependenceReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphIndependenceReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous domination in the actual finite-coordinate independence realization.",
        H("Native independence-complex domination folds"),
        Blocks(
            Paragraph(Text(
                "Throughout, V is any finite type with decidable equality, G is a simple graph on V, "
                + "a is a vertex, and D is any finite set of vertices. Write N(b) for the open "
                + "neighborhood of b. For the retraction assume a is not in D and N(a) is contained "
                + "in N(d) for every d in D. There is no acyclicity, connectedness or dimension hypothesis.")),
            Node("retained", "Retained", "Original retained labels",
                "For every finite decidable type V and D : Finset V, Retained(D) is the subtype "
                + "of vertices b of V with b not in D. The target graph is G induced on that actual subtype.",
                DescribeRole.Definition),
            Node("transfer", "transfer", "Simultaneous linear mass transfer",
                "For every V, a, D, real vector x on V and vertex b, transfer(a,D,x)(b) is "
                + "x(b) plus the sum of x(d) over d in D when b=a, minus x(b) when b is in D. "
                + "Under a not in D it is x(a)+sum(D,x) at a, zero on D, and x(b) elsewhere. "
                + "This is defined on all real vectors, with no division or normalization.", DescribeRole.Definition),
            Node("common-zero", "transfer_common_zero", "A zero endpoint shared by both vectors",
                "For every finite decidable V, simple graph G, a : V, D : Finset V with "
                + "N(a) contained in N(d) for every d in D, and real vector x satisfying Avoid(G,x), "
                + "every edge p-q satisfies (x(p)=0 and transfer(a,D,x)(p)=0) or "
                + "(x(q)=0 and transfer(a,D,x)(q)=0). This lemma requires neither probability "
                + "coordinates nor a not in D. For an edge a-q with x(q) nonzero, avoidance "
                + "and domination force x(a) and every deleted coordinate to be zero. "
                + "The same endpoint therefore vanishes after transfer. On edges away from a, "
                + "a formerly zero endpoint remains zero.", DescribeRole.Theorem),
            Node("inclusion", "inclusion", "Native inclusion",
                "For every finite decidable V, simple graph G and D : Finset V, inclusion(G,D) "
                + "is a continuous map from Ispace(G induced on Retained(D)) to Ispace(G). "
                + "It extends the actual retained coordinates by zero on D, using the native "
                + "embedding homeomorphism and the inclusion of the mapped independent faces.", DescribeRole.Definition),
            Node("retraction", "retraction", "Native retraction",
                "For every V,G,a,D with a not in D and N(a) contained in N(d) for every d in D, "
                + "retraction(G,a,D) is a continuous map from Ispace(G) to Ispace(G induced on "
                + "Retained(D)). Its coordinate at a retained b is transfer(a,D,x)(b). "
                + "The new vector is nonnegative with sum one; deleting its zero coordinates "
                + "preserves that sum, and the common-zero lemma proves independent support.", DescribeRole.Definition),
            Node("retraction-inclusion", "retraction_inclusion", "Retraction identity",
                "For every finite decidable V, simple graph G, a : V, D : Finset V with a not in D "
                + "and N(a) contained in N(d) for every d in D, and every y in Ispace(G induced "
                + "on Retained(D)), retraction(G,a,D)(inclusion(G,D)(y))=y. Zero extension gives "
                + "zero deleted mass, so the transfer fixes every coordinate.", DescribeRole.Theorem),
            Node("relative-homotopy", "foldHomotopy", "Strong deformation on the actual realization",
                "For every V,G,a,D under the stated retraction hypotheses, foldHomotopy is a "
                + "HomotopyRel from the identity of Ispace(G) to inclusion(G,D) after "
                + "retraction(G,a,D), relative to the full subspace of x with x(d)=0 for every d in D. "
                + "For every t in the closed unit interval and x in Ispace(G), its coordinates "
                + "are (1-t)x+t transfer(a,D,x). Probability is preserved along the segment. "
                + "Each edge has a common zero endpoint, so avoidance holds at every time, "
                + "even if x(a)=0 and deleted positive mass makes the survivor positive. "
                + "At t=0 it is x, at t=1 it is inclusion after retraction; at every time "
                + "it fixes each included point. Empty D is included.", DescribeRole.Definition),
            Node("fold-equivalence", "foldEquiv", "Native homotopy equivalence",
                "For every finite decidable V, simple graph G, a : V and D : Finset V with "
                + "a not in D and N(a) contained in N(d) for every d in D, foldEquiv gives "
                + "Ispace(G) homotopy equivalent to Ispace(G induced on Retained(D)). "
                + "The forward map is retraction and its inverse is inclusion. The inverse "
                + "laws are the actual relative homotopy and the retraction identity.", DescribeRole.Definition),
            Paragraph(Text(
                "The direction of open-neighborhood containment matters. In P4 with edges "
                + "0-1-2-3, N(0) is contained in N(2), allowing deletion of 2 toward 0; "
                + "deleting 0 toward 2 would create the forbidden support {2,3} from {0,3}. "
                + "Closed-neighborhood containment cannot replace it: the two closed "
                + "neighborhoods of K2 agree, but its independence realization is S0 and "
                + "does not retract by this segment to one vertex. Nonforest twin vertices, "
                + "such as opposite vertices of C4 or vertices in one part of a complete "
                + "bipartite graph, satisfy the open-neighborhood condition.")),
            Paragraph(Text(
                "This is the classical domination fold, with an explicit native coordinate "
                + "deformation; no novelty is claimed. The full forest classification is "
                + "Ehrenborg and Hetyei, The topology of the independence complex, European "
                + "Journal of Combinatorics 27 (2006), 906-923, Corollary 6.1, "
                + "DOI 10.1016/j.ejc.2005.04.010. The leaf-to-join bridge and the forest "
                + "classification are separate conclusions and are not asserted here.")))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
