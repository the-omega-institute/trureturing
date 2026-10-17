using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypergraphs;

internal sealed class AlonTarsiRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypergraphs/AlonTarsiRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/anholcer2026alontarsi");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One fully unbalanced F3 multihypergraph refutes the two printed fixed-polynomial AT bounds.",
        H("A characteristic-three hypergraph Alon-Tarsi counterexample"),
        Blocks(
            Node("edges", "Three edge occurrences", "edge",
                "Each of the three distinct occurrence indices maps to the full set Fin 3. Equal vertex sets retain separate multiplicities.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("density", "Induced occurrence density", "density",
                "For each nonempty vertex subset S, count occurrence indices e with H(e) contained in S and divide by the number of vertices of S; take the maximum. This is the source density, with no trace or simple-edge replacement.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("at", "The top-degree AT bound", "ATAtMost",
                "ATAtMost(p,k) means that some exponent vector has nonzero coefficient, exponent sum equal to the total degree of p, and every exponent strictly below k. For nonzero p in finitely many variables this is exactly AT(p) ≤ k under the source convention: maximum individual exponent plus one, minimized over nonzero monomials of maximum total degree. Formal polynomials are used throughout.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("product", "The occurrence-indexed edge product", "edgePolynomial",
                "The product ranges over edge occurrences. Its factor at occurrence e is the sum of a(e,v) times X(v) over incident vertices. The coefficient array may depend on both e and v.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture4", "Printed Conjecture 4", "Conjecture4",
                "Anholcer et al., Conjecture 4, journal pp. 5 and 23, asserts AT(p) ≤ 2 ceil(ed(H)) + 1 for every hypergraph polynomial p. The predicate quantifies over arbitrary fields, all finite numbers of vertices and occurrences, all indexed edge sets with edge sizes at least two, and all nonzero incident coefficients. Fin n enumerates the finite vertex set; n is positive so the maximum over nonempty subsets is defined. The supplied polynomial is fixed, with no coefficient permutations.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture28", "Printed Conjecture 28", "Conjecture28",
                "Conjecture 28, journal p. 23, adds that every edge is unbalanced: there are two incident vertices with unequal coefficients. This means the coefficients are not all equal, and does not impose pairwise distinctness or a zero sum. The remaining parameters and bound are those of Conjecture 4.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("polynomial", "The polynomial over F3", "polynomial",
                "Take p = (X(0) + X(1) − X(2))³ over the genuine field ZMod 3. The source vertices 1,2,3 correspond to indices 0,1,2.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("edge-product", "Agreement with the actual edge product", "polynomial_from_edges",
                "The polynomial is exactly the product of the three indexed linear factors, with coefficients (1,1,−1) on each occurrence. This identical assignment is a choice of witness; the universal predicates permit arbitrary occurrence-dependent coefficients.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("frobenius", "Characteristic-three cancellation", "frobenius_identity",
                "The characteristic-three Frobenius identities give p = X(0)³ + X(1)³ − X(2)³. The proof directly applies the pinned Mathlib characteristic-power identities.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("density-one", "Exact density", "density_one",
                "Every proper vertex subset induces zero occurrences. The full set induces three edges on three vertices, so ed(H) = 1.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("threshold", "Exact AT threshold", "exact_AT_bound",
                "For every natural k, ATAtMost(p,k) holds if and only if 4 ≤ k. All coefficient vectors with every exponent at most two have zero coefficient, while X(0)³ has coefficient one and total degree three. Thus AT(p) = 4.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("joint-certificate", "One jointly admissible source witness", "source_counterexample",
                "This closed certificate joins edge size at least two, nonzero coefficients, full unbalance, the actual occurrence-indexed product, density one, total degree three, the exact AT threshold for every k, and failure at the conjectured bound. The incident coefficients 1 and −1 differ in F3. Every premise belongs to the same witness.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The two source statements as one family", "claim",
                "The claim is the disjunction Conjecture4 or Conjecture28. Negating it refutes both printed universal statements using the same fully unbalanced witness.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("hypergraph-alon-tarsi-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Both universal statements are false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The joint certificate specializes each universal statement to this same witness. "
                    + "Its AT number is four, exceeding 2 ceil(1) + 1 = 3. "
                    + "The source is Anholcer et al., Alon-Tarsi for Hypergraphs, "
                    + "arXiv:2501.00157v2; Electronic Journal of Combinatorics 33(3), P3.74, "
                    + "DOI 10.37236/15173. Conjectures 4 and 28 form one related family. "
                    + "Characteristic-zero and simple-hypergraph variants are outside this refutation, "
                    + "as is Theorem 1 allowing separate coefficient permutations. "
                    + "Prior publication and global priority remain ASSUMED-UNVERIFIED; no priority claim is made."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("anholcer-hypergraph-alon-tarsi"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("hypergraph-alon-tarsi-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
