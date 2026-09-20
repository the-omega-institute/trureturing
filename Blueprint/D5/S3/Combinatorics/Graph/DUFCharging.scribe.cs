using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFChargingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFCharging.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let V be a finite vertex type and H a finite family of subsets of V. The DUF condition says that an unordered pair of disjoint members of H is uniquely determined by its union. Write N(p) for the vertices outside p that extend p to a member of H, and K(q) for the family of ground pairs p with q contained in N(p). The cap-four hypothesis requires card(N(p))<=4 for every ground pair p, including absent pairs.",
        H("Charging saturated link components"),
        Blocks(
            Paragraph(Text("A complete block (c,A,S) consists of disjoint four-sets A and S, neither containing c, with every triple {c,a,b}, a in A and b in S, belonging to H. Under the cap, its support A union S is an entire connected component of the link at c. B counts blocks by center and eight-vertex support, independently of the order of the two sides. Write m=card(H), n=card(V), P=binom(n,2), hi for the number of ground pairs with i neighbors, and qi for the number with i common-link edges.")),
            Describe.Lean(
                DescribeId.Create("singleton-common-link"),
                DeclarationHandle.Create(Prefix + "singleton_common_link"),
                H("The common link of a center and an additional neighbor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume H is DUF and satisfies the cap-four hypothesis. For every complete block (c,A,S), every a in A, every b in S, and every x in N({a,b}) distinct from c, the actual common link K({c,x}) is exactly the singleton family whose sole edge is {a,b}. This statement does not require a uniformity assumption on other members of H.")),
                    Paragraph(Text("The cross pair {a,b} belongs to K({c,x}). Any second edge must meet it, since DUF makes every common link intersecting. After interchanging the block sides if necessary, that edge is {a,y} with y distinct from b. Saturation forces y into S. Then {a,x} belongs to K({b,y}), as does {c,a'} for every a' in A. A four-set A contains an a' distinct from both a and x. These two edges are disjoint because c is outside A and x is distinct from c, contradicting the intersecting property."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mixed-incidence-bound"),
                DeclarationHandle.Create(Prefix + "mixed_incidence_bound"),
                H("The global charge and cap-four bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every three-uniform DUF family H satisfying the cap-four hypothesis, 16B<=h1+2q1 and m+2B<=P. There is no restriction on the number of components or on triples outside the complete blocks.")),
                    Paragraph(Text("For a block z=(c,U), let C(z) consist of the two-element subsets p of U for which p union {c} belongs to H. Saturation identifies C(z) with the sixteen cross pairs of its bipartition. Count the incidences (z,p) with p in C(z). If two such incidences have the same center and cross pair, their link components share a vertex, hence have the same support and are equal.")),
                    Paragraph(Text("Partition the 16B incidences by whether card(N(p)) is one. In that case the unique neighbor is the block center, so projection to p is injective and there are at most h1 incidences. Otherwise choose another neighbor x. The pair q={c,x} has singleton common link by the preceding theorem. Relate each incidence to all such q. Every remaining incidence has at least one related q; for a fixed singleton common link q, its sole edge determines p and the chosen endpoint c of q determines the block. Thus q has at most two related incidences. Double counting gives at most 2q1 incidences in this part, proving the charge.")),
                    Paragraph(Text("The component counting identity is 6m+a+q2+2q1+3q0+h1+3h0=6P+4B, where a counts exact four-neighborhood fibers with one or two edges. Its nonnegative correction is at least h1+2q1, hence at least 16B. Substitution gives 6m+12B<=6P and therefore m+2B<=P. The cap-four hypothesis is essential to the saturation argument; the unrestricted high-codegree case of Erdős 643 is not asserted."))),
                DescribeRole.Theorem)),
        []));
}
