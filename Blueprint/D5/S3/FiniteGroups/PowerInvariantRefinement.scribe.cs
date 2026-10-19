using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class PowerInvariantRefinementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/PowerInvariantRefinement.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/fernandes2026invariants");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common refinement strictly between isomorphism and simultaneous power equivalence on all finite groups.",
        H("An intermediate finite-group invariant"),
        Blocks(
            Node("PowerEquivalent", "One bijection for all integer powers",
                "Definition 1.5(2) and Remark 1.6 of Fernandes–Qureshi–Reis–Ribas require one equivalence of underlying carriers f such that f(g^n)=(f g)^n for every g and every integer n. The existential quantifier for f precedes both universal quantifiers. Separate bijections for separate exponents would be a different relation.", DescribeRole.Definition, true),
            Node("Abelian", "Abelianity",
                "Abelian G means that every pair x,y in the actual group satisfies x*y=y*x. It uses the multiplication of the supplied Group instance.", DescribeRole.Definition),
            Node("Refined", "The common refinement",
                "Refined G H is PowerEquivalent G H together with agreement on abelianity. Identity, inverse and composition of the same power bijections prove its equivalence laws. A group isomorphism preserves integer powers and commutativity. The common-refinement operation is elementary; it is not claimed as a newly discovered general construction.", DescribeRole.Definition),
            Node("Iso", "The finest source relation",
                "FG bundles an arbitrary carrier type, an actual Group structure and a Finite instance. Every finite group in the carrier universe can be supplied directly, with no order, exponent, commutativity or catalog restriction. Iso is nonempty group isomorphism between these actual carriers. This is Definition 1.5(1), and the trivial group is included.", DescribeRole.Definition, true),
            Node("Pow", "The simultaneous power partition",
                "Pow applies PowerEquivalent to the bundled carriers, retaining a single bijection for all integer powers. It is the source's second partition relation.", DescribeRole.Definition, true),
            Node("R", "The intermediate partition",
                "R applies Refined to the bundled carriers. Although three finite groups witness its strict position, its definition ranges over all FG values. Equivalence and invariance under isomorphism make it a partition on the source's isomorphism classes.", DescribeRole.Definition),
            Node("StrictRefines", "Finer-to-coarser strict refinement",
                "StrictRefines r s means every r-related pair is s-related, and there is an s-related pair that is not r-related. This matches the source's finer-to-coarser order. Thus StrictRefines Iso R means P1<P, and StrictRefines R Pow means P<P2.", DescribeRole.Definition, true),
            Node("finite_source_endpoint", "The complete first alternative of Problem 6.2",
                "The theorem asserts Equivalence R, StrictRefines Iso R and StrictRefines R Pow on every actual finite group. The first strictness pair is B=T(1,0), C=T(1,1): both groups are nonabelian and are R-related, but cannot be isomorphic. The second is A=T(0,0), B=T(1,0): they are power equivalent but disagree on abelianity. These existential pairs establish strictness globally.", DescribeRole.Theorem, false,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("fernandes-2026-intermediate-group-invariant"), ResolutionKind.Proved)),
            Node("isomorphism_invariant", "Independence of group labels",
                "For arbitrary group isomorphisms e:G≃*G′ and f:H≃*H′, the theorem proves R(G,H) iff R(G′,H′). The proof composes the R-relations induced by e and f with the given R-relation. Hence the global equivalence descends to isomorphism classes in both arguments.", DescribeRole.Theorem),
            Paragraph(Text("Write an element of T(u,v) as (a,b,c,d,z) in F3^5. Multiplication adds the first four coordinates and has last coordinate z+z′+u(a b′−b a′)+v(c d′−d c′). The bilinear alternating cocycle proves associativity; zero is the identity and coordinate negation is the inverse. The native groupInst contains proofs of the group laws. Induction proves that natural powers multiply each coordinate by the exponent; inverses give the same statement for negative integer powers. The one coordinate bijection recoord therefore preserves every integer power simultaneously.")),
            Paragraph(Text("For T(0,0), the product is commutative. For T(1,v), the elements (1,0,0,0,0) and (0,1,0,0,0) have products with last coordinates 1 and −1, which differ in F3. Thus B and C are nonabelian. In B, testing commutation against the first two coordinate basis elements forces a=b=0; conversely those two equations imply commutation with every group element. In C, the four basis tests force a=b=c=d=0, and the converse again holds. The factor 2 is nonzero in F3. Explicit equivalences identify the actual centers with F3^3 and F3, giving orders 27 and 3. Mathlib's Subgroup.centerCongr transports centers under an actual group isomorphism, contradicting these distinct orders. The witnesses use the classical alternating-form central extension; no numeric substitute for group multiplication or centers is assumed.")),
            Paragraph(Text("The source is Arthur Fernandes, Claudio Qureshi, Lucas Reis and Sávio Ribas, On a class of combinatorial group invariants, arXiv:2609.20516v1, Problem 6.2, Definition 1.5 and Remark 1.6. Its displayed question uses OR, so this first interval is a complete qualifying alternative. The other two intervals and Problems 6.1, 6.3 and 6.4 are unclaimed. Source Lemma 3.1(i) and its section 6 discussion already supply prime-exponent power-equivalence ingredients. Larson, Power maps in finite groups, Integers 19 (2019), A58, section 5, page 14, discusses the abelian/nonabelian order-27 example. The common refinement, bilinear extensions and center obstruction are classical ingredients. Mathlib supplies ZMod arithmetic, equivalences, powers and center transport. The result is an elementary combination with two explicit strictness pairs. Worldwide priority and completeness of the current correction/solution search remain ASSUMED-UNVERIFIED."))), []));

    private static StatementSource Statement(string name) => name == "finite_source_endpoint"
        ? StatementSource.FromAuthor(FormulaDsl.Disp(new Formula.Logic(
            Call("Equivalence", Id("R")), FormulaLogicOperator.And,
            new Formula.Logic(Call("StrictRefines", Id("Iso"), Id("R")), FormulaLogicOperator.And,
                Call("StrictRefines", Id("R"), Id("Pow"))))))
        : StatementSource.WithoutFormula();

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role,
        bool fromSource = false, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("power-invariant-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), Statement(name),
            fromSource ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
