using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class UnaryMooreSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSeparation.";
    private static Formula K => F.Id("K");
    private static Formula I => F.Id("i");
    private static Formula A => F.Id("a");
    private static Formula V(string symbol, Formula index) => new Formula.Subscript(F.Id(symbol), index);
    private static Formula Pow(Formula term, Formula power) => new Formula.Power(term, power);
    private static Formula Length => Seq(D(2), K, Minus, D(1));
    private static Formula Count => Seq(new Formula.Subscript(F.Sum, Seq(D(1), Le, Sp, A, Le, Sp, K)), Sp,
        Pow(A, Seq(A, Plus, D(1))), Pow(D(2), A));
    private static Formula Separation => Seq(
        Open, Forall, Sp, I, Lt, Length, Comma, Sp, V("s", I), Eq, V("t", I), Close,
        Sp, Implies, Sp, Open, Forall, Sp, I, Comma, Sp, V("s", I), Eq, V("t", I), Close);
    private static Formula Output => Seq(V("s", I), Eq,
        F.Id("g"), Open, Pow(F.Id("f"), I), Open, V("q", D(0)), Close, Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two autonomous unary Moore sources of at most K states cannot agree for "
        + "the first 2K−1 output observations and then diverge. An authentic prefix "
        + "of that exact length determines an executable generator for its behavior.",
        H("Finite unary Moore separation and effective synthesis"),
        Blocks(Describe.Lean(
            DescribeId.Create("gpo-unary-moore-separation"),
            DeclarationHandle.Create(Prefix + "unary_moore_separation_and_synthesis"),
            H("Separation at 2K−1 observations and first-match synthesis"),
            StatementSource.FromAuthor(Disp(Seq(K, Ge, Sp, D(1), Quad, Sp, Output, Quad, Sp, Separation))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The start is an actual state in a nonempty carrier of cardinality at most K. "
                    + "The binary output of that state counts at index zero; each later index applies "
                    + "one more iteration of the single autonomous transition. Transient paths, "
                    + "singular transitions, unreachable states and constant outputs are allowed.")),
                Paragraph(Text(
                    "In the disjoint union, group states by finite output signatures. Truncation maps "
                    + "each next partition onto the previous one. Equal counts force words with equal "
                    + "truncations to agree. The unary head-and-tail recurrence then gives equality at "
                    + "every later index. Continued strict splitting would exceed the number of states.")),
                Paragraph(Text(
                    "For an authentic word of the stated length, enumerate the labelled transition, "
                    + "output and start tables of sizes 1 through K in a fixed order. The authentic "
                    + "machine is isomorphic to one of these tables, so the search returns a first match. "
                    + "Its whole output stream equals the authentic stream, and all earlier tables fail "
                    + "the prefix test. The exact count of candidates before any deduplication is "),
                    Math(Count), Text(".")),
                Paragraph(Text(
                    "This identifies the output behavior, not a private state naming or presentation. "
                    + "It makes no claim about acquisition cost, running time optimality, "
                    + "or a lower bound on the comparison length."))),
            DescribeRole.Theorem))));
}
