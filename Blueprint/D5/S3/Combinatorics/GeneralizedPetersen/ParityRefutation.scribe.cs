using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ParityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pandey2026parity");
    private static readonly LibraryNoteRef PriorRefutationSource =
        LibraryNoteRef.Create("D5/L/Combinatorics/demonstrandum2026pandeyrefutation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Lean formalization of the earlier public refutation: the triangular prism has "
            + "real-rooted independence polynomial 1+6X+6X^2 and odd step size.",
        H("The Triangular Prism Refutes Pandey's Parity Conjecture"),
        Blocks(
            Paragraph(Text(
                "Conjecture 4.1 (Parity Conjecture), page 4 of arXiv:2601.03293v1, states: "
                    + "\"For all integers n ≥ 2k+1, the independence polynomial I(GP(n,k),x) "
                    + "has only real roots if and only if k is even.\" Definition 2.1 supplies "
                    + "n >= 3 and 1 <= k < n/2. The separate computational range 20 <= n <= 30 "
                    + "does not restrict that conjecture.")),
            Describe.Lean(DescribeId.Create("pandey-parity-graph"),
                DeclarationHandle.Create(Prefix + "gp"), H("Generalized Petersen graphs"),
                StatementSource.FromAuthor(Disp(Equal(Call("gp", F.Id("n"), F.Id("k")),
                    Call("fromRel", Call("R", F.Id("n"), F.Id("k")))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The vertex type is Bool x Fin n. The false layer represents u and the true "
                        + "layer represents v. The relation R consists of u_i to u_(i+1), "
                        + "v_i to v_(i+k), and u_i to v_i, with indices modulo n. The fromRel "
                        + "construction makes these edges undirected and removes loops. The "
                        + "parameter domain below is exactly the source graph domain."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pandey-parity-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The full parity assertion"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Here I(G,z) denotes complex evaluation, by the integer cast ring homomorphism, "
                        + "of IndependentPartitionDeletion.independencePolynomial on all vertices "
                        + "of G. That polynomial is the sum of X to the cardinality of S over "
                        + "all actual independent vertex sets S. Real-rootedness means that every "
                        + "complex zero has imaginary part zero. The strict natural-number "
                        + "inequality 2k < n is equivalent to n >= 2k+1 and avoids truncated division."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pandey-parity-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("An odd-step real-rooted graph"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromLiterature(PriorRefutationSource),
                Blocks(Paragraph(Text(
                    "For n=3 and k=1 the graph is the triangular prism. Its independent sets "
                        + "are the empty set, six singletons, and six pairs u_i,v_j with i different "
                        + "from j. There are no larger independent sets. Thus its actual polynomial "
                        + "evaluates to 1+6z+6z^2. If z=a+bi is a zero, its imaginary part "
                        + "gives 6b(1+2a)=0. If b is nonzero then a=-1/2, and the real part gives "
                        + "-1/2-6b^2=0, contradicting nonnegativity of b^2. Every zero "
                        + "is real, but k=1 is not even, contradicting the forward direction of "
                        + "the asserted biconditional.")),
                    Paragraph(Text(
                        "The earlier public refutation in demonstrandum-research/artifacts, "
                            + "commit 94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3, "
                            + "problems/p2-factory/kills/pandey-parity/WRITEUP.md, already gives "
                            + "this exact counterexample. Its provider commit timestamp is "
                            + "2026-06-13T01:23:03Z; its internal June 11 date is unverified. "
                            + "The separate prior-refutation Library note pins that source. "
                            + "That note also explains the published map u_j to v'_(3j mod 7), "
                            + "v_j to u'_(3j mod 7), an isomorphism GP(7,2) to GP(7,3). "
                            + "Equal independence polynomials and opposite step parity contradict "
                            + "the full biconditional without computing roots. No external "
                            + "enumeration, Sturm, checker, or audit claims are adopted here.")),
                    Paragraph(Text(
                        "This Lean theorem formalizes the already published refutation; it is "
                            + "not a newly resolved open problem. The graph and conjecture are "
                            + "due to Pandey; the refutation is due to the distinct earlier "
                            + "public note cited above."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pandey-parity-conjecture-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var z = F.Id("z");
        var realRoots = Universal("z", Named("Complex"), Implies(
            Equal(Call("I", Call("gp", n, k), z), D(0)),
            Equal(Call("im", z), D(0))));
        var body = Universal("n", Named("Nat"), Universal("k", Named("Nat"),
            Implies(Relation(D(3), FormulaRelationOperator.LessThanOrEqual, n),
            Implies(Relation(D(1), FormulaRelationOperator.LessThanOrEqual, k),
            Implies(Relation(Seq(D(2), Cdot, Sp, k), FormulaRelationOperator.LessThan, n),
                Logic(realRoots, FormulaLogicOperator.Iff, Call("Even", k)))))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, body));
    }

    private static Formula Named(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Universal(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Relation(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);
    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
    private static Formula Implies(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
}
