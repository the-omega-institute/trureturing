using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class ZeckendorfGreedyPermutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.";
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Id(string s) => F.Id(s);
    private static Formula Name(string s) => Seq(Operatorname, Grp(Id(s)));
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Name(s), [.. xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Rel(Formula x, Formula token, Formula y) => Seq(x, Sp, token, Sp, y);
    private static Formula Eqn(Formula x, Formula y) => Rel(x, Eq, y);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula And(params Formula[] xs) => Seq([.. xs.SelectMany((x, i) =>
        i == 0 ? new Formula[] { Par(x) } : new Formula[] { Sp, Land, Sp, Par(x) })]);
    private static Formula All(string s, Formula type, Formula body) => Par(
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body));
    private static Formula Some(string s, Formula type, Formula body) => Par(
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), type, body));
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula SType => Seq(N, Sp, To, Sp, N);
    private static Formula Plus(Formula n) => Call("add", n, D(1));
    private static Formula At(Formula s, Formula n) => App(s, n);
    private static Formula Positive(Formula x) => Rel(D(0), Lt, x);
    private static Formula Index(Formula x) => Rel(D(1), Le, x);
    private static Formula Eligible(Formula s, Formula n, Formula m) => And(
        Positive(m),
        All("k", N, Imp(And(Index(Id("k")), Rel(Id("k"), Le, n)),
            Rel(At(s, Id("k")), Neq, m))),
        Call("Adjacent", At(s, n), m));
    private static Formula Whole(Formula s) => And(
        Eqn(At(s, D(1)), D(1)),
        All("n", N, Imp(Index(Id("n")), Positive(At(s, Id("n"))))),
        All("n", N, Imp(Index(Id("n")), And(
            Call("Eligible", s, Id("n"), At(s, Plus(Id("n")))),
            All("m", N, Imp(Call("Eligible", s, Id("n"), Id("m")),
                Rel(At(s, Plus(Id("n"))), Le, Id("m"))))))),
        All("i", N, All("j", N, Imp(
            And(Index(Id("i")), Index(Id("j")), Eqn(At(s, Id("i")), At(s, Id("j")))),
            Eqn(Id("i"), Id("j"))))),
        All("m", N, Imp(Index(Id("m")), Some("n", N,
            And(Index(Id("n")), Eqn(At(s, Id("n")), Id("m")))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least-unused one-common-Zeckendorf-term sequence is total and enumerates every positive integer exactly once.",
        H("The One-Common-Zeckendorf-Term Greedy Permutation"),
        Blocks(
            Paragraph(Text("OEIS A370630 asks whether the lexicographically earliest sequence of distinct positive integers "
                + "whose consecutive canonical Zeckendorf expansions have exactly one common term is a permutation. "
                + "The record is https://oeis.org/A370630/internal and its explicit selection rule is "
                + "https://oeis.org/A370630/a370630.gp.txt. The source title is ‘Lexicographically earliest sequence "
                + "of distinct positive integers such that the Zeckendorf expansions of two consecutive terms have exactly one common term.’ "
                + "Its conjecture is ‘this sequence is a permutation of the positive integers.’ The record author is Rémy Sigrist; "
                + "the conjecture comment has no separately signed attribution.")),
            Paragraph(Text("Fibonacci weights use F(0)=0, F(1)=1 and the usual additive recurrence. "
                + "Only indices at least two occur in the canonical support. Thus the permitted weights are 1, 2, 3, 5, and so on, "
                + "with no consecutive occupied indices. PARI bit position j represents Fibonacci index j+2. "
                + "The comparison is numerical leastness among all unused positive integers. "
                + "The overlap condition is cardinality exactly one.")),
            Node("support", "Canonical Fibonacci support", Disp(All("m", N,
                Eqn(Call("support", Id("m")), Call("toFinset", Call("wdigits", Id("m")))))),
                "The existing canonical W-digit equivalence supplies existence and uniqueness. The list stores Fibonacci indices, "
                + "and passing to its finite set preserves precisely the occupied terms.", DescribeRole.Definition),
            Node("Adjacent", "Exactly one shared canonical term", Disp(All("x", N, All("y", N,
                Rel(Call("Adjacent", Id("x"), Id("y")), Iff,
                    Eqn(Call("card", Call("inter", Call("support", Id("x")), Call("support", Id("y")))), D(1)))))),
                "The finite-set intersection counts common Fibonacci terms in the unique nonadjacent representations.", DescribeRole.Definition),
            Node("a", "The actual one-based sequence", Disp(All("n", N,
                Eqn(Call("a", Id("n")), Call("v", Call("sub", Id("n"), D(1)))))),
                "Subtraction on natural indices is truncated. Internally v(n) is the current value after n transitions from "
                + "the initial history [1]. Each transition minimizes the positive integer absent from the entire history "
                + "and adjacent to its current value, then prepends that integer. Consequently a(n+1)=v(n), and a(1)=1. "
                + "The value at index zero is auxiliary; the assertion quantifies over positive indices.", DescribeRole.Definition),
            Node("Eligible", "The exact unused-successor predicate", Disp(All("s", SType, All("n", N, All("m", N,
                Rel(Call("Eligible", Id("s"), Id("n"), Id("m")), Iff, Eligible(Id("s"), Id("n"), Id("m"))))))),
                "Every positive index from one through the current index belongs to the excluded prefix. "
                + "A candidate must be positive and share exactly one canonical term with the current value.", DescribeRole.Definition),
            Node("IsGreedyPermutation", "Whole totality and permutation", Disp(All("s", SType,
                Rel(Call("IsGreedyPermutation", Id("s")), Iff, Whole(Id("s"))))),
                "The predicate includes the initial term, positivity, an eligible actual successor at every stage, "
                + "leastness against every eligible candidate, injectivity on positive indices, and attainment of every positive integer.",
                DescribeRole.Definition),
            Node("result", "A370630 is a positive-integer permutation", Disp(Whole(Name("a"))),
                "A fresh sufficiently large Fibonacci index pairs with an occupied index of the current term. "
                + "Its weight exceeds the entire used prefix, so an unused eligible successor always exists. "
                + "Well-ordering selects the least one. The full history therefore defines a single total sequence, and choosing outside it proves distinctness. "
                + "For any omitted positive target, every visited neighbor would force the next actual term to be no larger than that target. "
                + "Injectivity makes the sequence eventually larger than every fixed bound, so unbounded visited neighbors force coverage. "
                + "To obtain such neighbors, consider the first stage whose support contains an index above an arbitrary bound. "
                + "Let j be the largest new index and i the unique shared old index. The canonical pair {i,j} is unused and eligible. "
                + "Its value is at most the actual next term, while greedy leastness gives the opposite inequality. "
                + "Hence these arbitrarily large record terms are pairs. "
                + "If a record pair has smaller index i at least four, the canonical pair {2,i}, of value F(i)+1, must be visited. "
                + "If omitted, it bounds the next choice. The weight F(j) is too large to occur there, so the next term contains i "
                + "and has value either F(i) or F(i)+1. The latter covers the target immediately. In the former case F(i) is then used, "
                + "and one more greedy comparison forces F(i)+1. "
                + "Either one smaller record index roots pairs with arbitrarily large second index, or finite cutoffs for each fixed smaller index "
                + "force arbitrarily large distinct smaller indices. The preceding two-step argument then gives arbitrarily large visited pairs rooted at two. "
                + "Thus some index r roots unbounded visited pairs. Any target containing r is adjacent to all sufficiently distant such pairs, "
                + "so every such target occurs. Call this the hub property. "
                + "If s is nonadjacent to a hub r, fresh canonical triples {r,s,t} are visited and provide unbounded neighbors for every target containing s "
                + "but not r; targets containing r are already covered. Hence s is a hub. "
                + "For an arbitrary positive target, choose a hub s beyond its entire support and the first hub, and choose an occupied target index k. "
                + "Fresh triples {s,k,t} are visited and intersect that target in exactly {k}. Unbounded-neighbor coverage finishes the proof. "
                + "The argument uses all stages of the actual history-dependent minimum rule; no finite enumeration is a premise.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a370630-zeckendorf-greedy-permutation"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a370630-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);
}
