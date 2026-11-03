using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoDirectedPathCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual shortest directed paths in the finite Jaco truncations.",
        H("Directed paths and their cardinality"),
        Blocks(
            Definition("directed", "The source directed graph",
                "The vertices are the positive natural labels. There is exactly one arrow from a to b when a < b and b is at most jacoRight a, and no arrow otherwise. The imported endpoint_recurrence identifies jacoRight with twice the label minus the number of earlier positive endpoints reaching it. Thus these are the original directed arcs, with no symmetrization."),
            Definition("TruncatedPath", "Paths in an induced truncation",
                "TruncatedPath r a b consists of actual Quiver.Path objects from a to b whose entire vertex list lies at labels at most r. This is the induced truncation on labels 1 through r: every edge is an original directed edge and every intermediate vertex remains in the truncation. Path length counts edges; the path of length zero at label one is included."),
            Definition("Shortest", "The actual shortest paths",
                "Shortest n is the subtype of TruncatedPath n 1 n with edge length no larger than every other such path. Distinctness is equality of directed edge sequences. There is at most one arrow per pair of labels, so this agrees with distinct vertex sequences."),
            Definition("psi", "Minimum-path cardinality",
                "For a positive natural n, psi n is Nat.card of Shortest n; psi zero is only an unused extension. No recurrence defines this count. The theorem below proves finiteness and positivity rather than assuming either property of Nat.card."),
            Definition("outdegree", "Infinite directed outdegree",
                "outdegree n is jacoRight n minus n. The imported endpoint_eq_beatty identifies it with beattyOut n. It counts the full outgoing interval in the infinite graph, even when a shortest path is counted in its own finite truncation."),
            Describe.Lean(DescribeId.Create("directed-path-count-original-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The original all-index question"),
                StatementSource.FromAuthor(Disp(Bound("k", Nat(), Implies(Le(D(7), K),
                    Bound("i", Nat(), Implies(And(Lt(Call("fib", I), K), Le(K, Call("fib", Add(I, D(1))))),
                        Iff(Adjacent("outdegree"), Adjacent("psi")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is Proposition 4.4 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, Characteristics of Jaco Graphs, arXiv:1404.1714v1, Section 4. Both chains mean the conjunction of the two adjacent inequalities. Every k at least seven and every Fibonacci bracket index remain quantified. The cardinality foundations below do not establish this equivalence. The original Proposition 4.3 converse is not used; an unconditional suffix-count identity, distance layers and Fibonacci boundary comparisons are required to complete the question."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("directed-path-count-foundations"),
                DeclarationHandle.Create(Prefix + "path_count_foundations"), H("Finite positive cardinality and truncation invariance"),
                StatementSource.FromAuthor(Disp(Bound("n", Named("PNat"),
                    And(Call("Finite", Call("Shortest", N)),
                        And(Call("Nonempty", Call("Shortest", N)),
                            And(Lt(D(0), Call("psi", Call("val", N))),
                                Bound("r", Nat(), Implies(Le(Call("val", N), R),
                                    Exists("e", Call("Equiv", T(R), T(Call("val", N))),
                                        Bound("p", T(R), Equal(Call("length", Call("underlying", Call("e", F.Id("p")))),
                                            Call("length", Call("underlying", F.Id("p")))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An induction on the terminal positive label decomposes each nonempty directed path into its last predecessor and its prefix. Every predecessor has strictly smaller label, and the outgoing edge is unique, giving a finite set of paths. Consecutive forward arcs supply a path to each positive label; the least attained edge length therefore exists. Every vertex of a forward path is between its endpoints. Erasing or inserting the truncation proof gives inverse maps on paths in any truncation ending beyond the target, and preserves edge length exactly. These arguments concern actual path objects and their cardinality, without a recurrence replacement for psi."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("directed-path-count-fibonacci-distance"),
                DeclarationHandle.Create(Prefix + "fibonacci_distance"), H("The exact Fibonacci distance threshold"),
                StatementSource.FromAuthor(DistanceFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nonnegative edge budget l and every positive target n, a path in the target's own truncation has at most l edges exactly when n is at most Fibonacci(l+2). Every shortest path has the same threshold. Strict increase of the original endpoint sequence and beatty_threshold give beattyOut(jacoRight m)=m. Induction then gives jacoRight(Fibonacci(l+2))=Fibonacci(l+3). Another induction proves that the reachable set at edge budget l is precisely that positive prefix: one more edge cannot pass the endpoint of the prefix, and every new label in the next prefix is reached directly from the previous endpoint. No compressed distance claim from the source is assumed."))), DescribeRole.Theorem))));

    private static Formula DistanceFormula()
    {
        Formula l = F.Id("l");
        Formula threshold = Le(Call("val", N), Call("fib", Add(l, D(2))));
        Formula shortPath = Le(Call("length", Call("underlying", F.Id("p"))), l);
        Formula minimum = Le(Call("length", Call("underlying", Call("underlying", F.Id("p")))), l);
        return Disp(Bound("l", Nat(), Bound("n", Named("PNat"),
            And(Iff(Exists("p", T(Call("val", N)), shortPath), threshold),
                Bound("p", Call("Shortest", N), Iff(minimum, threshold))))));
    }

    private static Formula N => F.Id("n");
    private static Formula K => F.Id("k");
    private static Formula I => F.Id("i");
    private static Formula R => F.Id("r");
    private static Formula Named(string x) => new Formula.NamedConstant(FormulaIdentifier.Create(x));
    private static Formula Nat() => Named("Nat");
    private static Formula T(Formula r) => Call("TruncatedPath", r, D(1), N);
    private static Formula Bound(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Exists(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Adjacent(string f) => And(Ne(Call(f, Subtract(K, D(1))), Call(f, K)), Ne(Call(f, K), Call(f, Add(K, D(1)))));
    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("directed-path-count-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
