using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoDirectedPathCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/kok2014jaco");

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
                StatementSource.FromAuthor(OriginalFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("This is Proposition 4.4 of Kok, Fisher, Wilkens, Mabula and Mukungunugwa, Characteristics of Jaco Graphs, arXiv:1404.1714v1, Section 4. Both chains mean the conjunction of the two adjacent inequalities. Every k at least seven and every Fibonacci bracket index remain quantified. The result below establishes this complete equivalence from actual directed path cardinalities. The original Proposition 4.3 converse is not used."))), DescribeRole.Definition),
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
                Blocks(Paragraph(Text("For every nonnegative edge budget l and every positive target n, a path in the target's own truncation has at most l edges exactly when n is at most Fibonacci(l+2). Every shortest path has the same threshold. Strict increase of the original endpoint sequence and beatty_threshold give beattyOut(jacoRight m)=m. Induction then gives jacoRight(Fibonacci(l+2))=Fibonacci(l+3). Another induction proves that the reachable set at edge budget l is precisely that positive prefix: one more edge cannot pass the endpoint of the prefix, and every new label in the next prefix is reached directly from the previous endpoint. No compressed distance claim from the source is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("directed-path-count-original-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Complete original Proposition 4.4"),
                StatementSource.FromAuthor(OriginalFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every j at least three and every target n with Fibonacci(j) < n <= Fibonacci(j+1), removing the final edge of an actual shortest directed path gives precisely a predecessor h in the interval [beattyOut n, Fibonacci(j)] together with an actual shortest path to h. A shorter prefix would shorten the original path. The distance threshold excludes later predecessors, while the endpoint threshold excludes earlier ones. Appending the unique final edge is the inverse, including both proof-carrying truncations. The resulting dependent-sum equivalence gives psi n as the sum of the positive actual cardinalities psi h over that interval.")),
                    Paragraph(Text("The endpoint threshold and consecutive endpoint growth show that beattyOut(n+1) is either beattyOut n or beattyOut n plus one. Within one Fibonacci distance layer the suffix sums therefore agree exactly in the first case. In the second case the lower summand psi(beattyOut n), which is positive by the cardinality foundations, is removed, so the counts differ strictly.")),
                    Paragraph(Text("The endpoint identities also give beattyOut(Fibonacci(t+1))=Fibonacci(t) for every t at least two. The shortest path to label two is unique. The singleton suffix at successive Fibonacci endpoints then gives psi(Fibonacci(t))=1 for every t at least three. At every boundary Fibonacci(t), t at least five, the next lower predecessor is Fibonacci(t-1)+1. Its suffix contains at least two labels, and each has positive actual shortest-path cardinality. Consequently psi(Fibonacci(t)+1) is at least two, while both the infinite outdegree and the path count differ across the boundary.")),
                    Paragraph(Text("Every label n at least five lies in a Fibonacci bracket. Combining the within-layer and boundary cases gives outdegree n = outdegree(n+1) exactly when psi n = psi(n+1). Applying this at k-1 and k, negating the two equality equivalences and conjoining proves the stated iff for every k at least seven. The original universal Fibonacci-bracket index is retained; no bracket, upper cutoff, converse from Proposition 4.3 or unproved reachability premise is added.")),
                    Paragraph(Text("The source is arXiv:1404.1714v1, Section 4, with its original forward directed arc convention and each target counted in its own induced truncation. This result is the mathematical event stated there. It does not certify worldwide literature coverage, priority or a physical interpretation."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kok-jaco-directed-path-count"),
                    ResolutionKind.Proved)))));

    private static Formula OriginalFormula() => Disp(Bound("k", Nat(), Implies(Le(D(7), K),
                    Bound("i", Nat(), Implies(And(Lt(Call("fib", I), K), Le(K, Call("fib", Add(I, D(1))))),
                        Iff(Adjacent("outdegree"), Adjacent("psi")))))));

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
