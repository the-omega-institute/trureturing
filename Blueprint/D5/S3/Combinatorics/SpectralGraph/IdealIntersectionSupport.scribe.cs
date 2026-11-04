using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class IdealIntersectionSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.";
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.",
        H("IdealIntersectionSupport"),Blocks(
            Paragraph(Text("The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.")),
            Node("actualSupportIso","Actual ideals and the support graph","Each ideal of ZMod n corresponds to a divisor of n, then to its prime-exponent vector. Removing the bottom and top ideals removes precisely the zero and full divisor endpoints. The support of an exponent vector records the coordinates below their maximal exponents. Intersection of two ideals is nonzero exactly when the corresponding supports intersect; distinctness is included. This proves the graph isomorphism used by every spectral conclusion.",DescribeRole.Definition),
            Node("adj_iff_lcm","Ideal intersection and divisor lcm","The divisor of an intersection is the least common multiple. The zero ideal corresponds to n. Thus distinct nonzero proper ideals are adjacent exactly when their divisor lcm differs from n.",DescribeRole.Theorem),
            Node("actual_vertex_card","Exact actual vertex count","For every nonempty finite family of distinct primes and every positive exponent vector, the actual graph has product of (k_i+1) minus two vertices. The subtraction removes the two actual ideal endpoints.",DescribeRole.Theorem),
            Node("vertex_support_fiber_card","Positive proper support-cell multiplicities","A nonempty proper support S has product of k_i over S vertices. These fibers supply the exact weights of the quotient and ensure a nonzero support value has a nonzero graph lift.",DescribeRole.Theorem),
            Node("universal_vertex_count","Universal vertices, including zero count","The full-support cell has product of k_i minus one vertices. The omitted element is the zero-exponent endpoint. This count may be zero, including every squarefree exponent vector. No proof assumes a positive universal-vertex count.",DescribeRole.Theorem),
            Node("universal_iff_full_support","The universal join","Full support is equivalent to being adjacent to every other vertex. Thus the actual graph is the join of its induced nonuniversal part with the complete graph on the full-support fiber, allowing the latter fiber to be empty.",DescribeRole.Theorem),
            Node("activeComplement_connected","Connected active complement","A proper nonempty support omits a coordinate and is disjoint from that coordinate singleton. Distinct singleton supports are mutually adjacent in the complement. These paths prove that deleting the universal vertices leaves a connected complement, with all exponents arbitrary.",DescribeRole.Theorem),
            Node("support_lift_sum","Exact weighted sum","Grouping actual exponent vertices by support gives the weighted sum formula when the support function vanishes on the two removed endpoints. The equal paired weights later give total vertex sum zero.",DescribeRole.Theorem),
            Node("support_complement_intertwining","Actual complement action","Complement adjacency is disjointness of nonempty supports. Grouping the degree-minus-adjacency action by support gives the displayed support operator with the removed endpoint cells excluded. This proves the bridge rather than assuming a matrix model.",DescribeRole.Theorem),
            Node("support_lift_nonzero","Nonzero support lifts","Every nonempty proper cell has positive cardinality for positive exponents. A nonzero support value is therefore realized at a genuine graph vertex.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,string prose,DescribeRole role)=>
        Describe.Lean(DescribeId.Create("nik-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),Blocks(Paragraph(Text(prose))),role);
}
