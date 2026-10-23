using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class ValuationStepPermutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/ValuationStepPermutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The valuation-step greedy sequence is a permutation of the positive integers.",
        H("The Valuation-Step Greedy Permutation"),
        Blocks(
            Paragraph(Text("OEIS A382357 starts with 1. The next term is the least unused "
                + "positive integer whose 2-adic valuation differs by exactly one from "
                + "the current valuation. The natural index starts at zero. An unused "
                + "value at the next higher level always exists, so the rule never "
                + "stalls and gives the lexicographically earliest allowed sequence.")),
            Node("Adjacent", "The exact adjacency condition", AdjacentFormula(),
                "Either valuation increases by one or it decreases by one. "
                + "The condition does not impose a distance bound on the integers.",
                DescribeRole.Definition),
            Node("next", "The least positive unused adjacent value", NextFormula(),
                "Nat.find minimizes the positive integer itself. Its predicate "
                + "requires positivity, absence from the full supplied history and "
                + "the literal adjacency condition. A sufficiently large odd "
                + "multiple of the next power of two proves nonemptiness.",
                DescribeRole.Definition),
            Node("terms", "The full reversed history", HistoryFormula(),
                "The history starts at [1]. Each successor prepends the least unused "
                + "adjacent positive integer. No term is discarded or repeated.",
                DescribeRole.Definition),
            Node("a", "OEIS A382357", SequenceFormula(),
                "The sequence value is the head of its nonempty history. Thus a(0)=1 "
                + "is the OEIS term a(1).", DescribeRole.Definition),
            Node("claim", "The permutation conjecture", ResultFormula(),
                "The exact claim combines injectivity and occurrence of every "
                + "positive integer.", DescribeRole.Definition),
            Node("result", "Every positive integer appears exactly once", ResultFormula(),
                "Each level k is a queue of the values 2^k(2r+1), r starting at zero. "
                + "Greedy minimality takes the least unused value of the chosen level. "
                + "A recurrent level forces every value at each neighboring level to "
                + "appear: an omitted value would bound infinitely many distinct "
                + "successor terms. If level zero were not recurrent, no level would "
                + "be recurrent and the height would eventually exceed each fixed bound. "
                + "In a finite prefix ending above a prescribed height, let D_j count "
                + "downward crossings from j to j-1. The visits to any lower level j "
                + "number D_j+D_(j+1)+1. At its last exit, the upper candidate is at "
                + "least 2^(j+1)(2D_(j+1)+1), while the unused lower candidate is at "
                + "most 2^(j-1)(2(D_(j-1)+D_j+1)+1). Greedy comparison gives "
                + "D_(j-1)+D_j >= 4D_(j+1)+1. The potential D_j+2D_(j+1) "
                + "decreases by at least one at every level. Downward crossings to "
                + "zero are bounded after the height stays above one, contradicting "
                + "arbitrarily long potential descent. Level zero is therefore "
                + "recurrent, and propagation covers every positive integer. "
                + "The factor-four comparison is specific to 2-adic valuation; "
                + "the analogous Omega and omega statements remain open.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a382357-valuation-step-permutation"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a382357-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Val(Formula x) => Call("valuation", D(2), x);
    private static Formula AdjacentFormula() => Disp(Seq(
        Call("Adjacent", F.Id("x"), F.Id("y")), Sp, Iff, Sp,
        Equal(Call("add", Val(F.Id("x")), D(1)), Val(F.Id("y"))), Sp, Lor, Sp,
        Equal(Call("add", Val(F.Id("y")), D(1)), Val(F.Id("x")))));
    private static Formula NextFormula() => Disp(Equal(Call("next", F.Id("l"), F.Id("c")),
        Call("find", Call("positiveunusedadjacent", F.Id("l"), F.Id("c")))));
    private static Formula HistoryFormula() => Disp(Seq(
        Equal(Call("terms", D(0)), Call("singleton", D(1))), Sp, Land, Sp,
        Equal(Call("terms", Call("add", F.Id("n"), D(1))),
            Call("cons", Call("next", Call("terms", F.Id("n")),
                Call("headD", Call("terms", F.Id("n")), D(1))), Call("terms", F.Id("n"))))));
    private static Formula SequenceFormula() => Disp(Equal(Call("a", F.Id("n")),
        Call("headD", Call("terms", F.Id("n")), D(1))));
    private static Formula ResultFormula() => Disp(Seq(
        Call("injective", Named("a")), Sp, Land, Sp,
        Forall, Sp, F.Id("m"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
        D(0), Sp, Lt, Sp, F.Id("m"), Sp, Implies, Sp,
        Exists, Sp, F.Id("n"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
        Equal(Call("a", F.Id("n")), F.Id("m"))));
}
