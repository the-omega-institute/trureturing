using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class FactorialHeraclitusTransformDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/FactorialHeraclitusTransform.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every integer occurs in the factorial Heraclitus transform.",
        H("The Factorial Heraclitus Transform"),
        Blocks(
            Paragraph(Text("The natural index starts at zero. Values are integers. "
                + "Factorial distances are k! with k at least one. Ranking enumerates "
                + "0, 1, -1, 2, -2, and so on: smaller absolute value first, positive "
                + "first on ties. The sequence uses its entire actual history, not a "
                + "finite approximation or a substitute recurrence.")),
            Node("unrank", "The exact integer order", RankFormula(),
                "At odd rank r the value is (r+1)/2; at even rank it is -r/2. "
                + "Both quotients are natural floor division. The private inverse "
                + "rank proves bijectivity and the stated absolute-value order.", DescribeRole.Definition),
            Node("IsFactorial", "Allowed distances", FactorialFormula(),
                "The witness k is a natural number at least one. Thus 1 and 2 are "
                + "allowed distances, and zero is excluded.", DescribeRole.Definition),
            Node("next", "The least unused admissible value", NextFormula(),
                "Nat.find minimizes rank among values outside the supplied list at "
                + "factorial distance from the current integer. A sufficiently large "
                + "positive factorial displacement proves that this set is nonempty.", DescribeRole.Definition),
            Node("terms", "The complete reversed history", HistoryFormula(),
                "The initial history is [0]. A successor prepends next(terms(n), "
                + "headD(terms(n),0)). Histories have length n+1 and no repeated value.", DescribeRole.Definition),
            Node("a", "OEIS A393434", SequenceFormula(),
                "The value a(n) is the head of terms(n), with default zero. The "
                + "history is always nonempty, so this default does not alter the rule.", DescribeRole.Definition),
            Node("claim", "The surjectivity conjecture", ResultFormula(),
                "Every integer is the value at some natural index, exactly the "
                + "conjecture quoted in the supplied OEIS A393434 source.", DescribeRole.Definition),
            Node("result", "Every integer appears", ResultFormula(),
                "The 25-term base block covers [-12,12] and ends at -11. "
                + "For k at least four, a complete interval [-k!/2,k!/2] ending "
                + "at 1-k!/2 extends to the next factorial interval. Minimal rank "
                + "forces the jump upward, the consecutive positive ascent, and "
                + "the jump to the negative endpoint. During descent, a distance-2 "
                + "candidate prevents adjacent visited magnitudes except at the "
                + "bottom. The remaining magnitudes can therefore be filled in "
                + "increasing order with steps 1 or 2, ending at 1-(k+1)!/2. "
                + "Factorial growth places each integer in one of these intervals. "
                + "History length, absence of repetitions and interval cardinality "
                + "identify the boundary index as k!, giving the full block invariant. "
                + "No closed formula for the negative-term order is needed.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a393434-factorial-heraclitus"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a393434-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula RankFormula() => Disp(Equal(Call("unrank", F.Id("r")),
        Call("ifodd", F.Id("r"), Call("div", Call("add", F.Id("r"), D(1)), D(2)),
            Call("neg", Call("div", F.Id("r"), D(2))))));
    private static Formula FactorialFormula() => Disp(Seq(Call("IsFactorial", F.Id("d")), Sp, Iff, Sp,
        Exists, Sp, F.Id("k"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
        D(1), Sp, Le, Sp, F.Id("k"), Sp, Land, Sp,
        Equal(F.Id("d"), Call("factorial", F.Id("k")))));
    private static Formula NextFormula() => Disp(Equal(Call("next", F.Id("l"), F.Id("c")),
        Call("unrank", Call("find", Call("admissible", F.Id("l"), F.Id("c"))))));
    private static Formula HistoryFormula() => Disp(Seq(
        Equal(Call("terms", D(0)), Call("singleton", D(0))), Sp, Land, Sp,
        Equal(Call("terms", Call("add", F.Id("n"), D(1))),
            Call("cons", Call("next", Call("terms", F.Id("n")),
                Call("headD", Call("terms", F.Id("n")), D(0))), Call("terms", F.Id("n"))))));
    private static Formula SequenceFormula() => Disp(Equal(Call("a", F.Id("n")),
        Call("headD", Call("terms", F.Id("n")), D(0))));
    private static Formula ResultFormula() => Disp(Seq(
        Forall, Sp, F.Id("z"), Sp, InMacro, Sp, Integers(), Comma, Sp,
        Exists, Sp, F.Id("n"), Sp, InMacro, Sp, Naturals(), Comma, Sp,
        Equal(Call("a", F.Id("n")), F.Id("z"))));
}
