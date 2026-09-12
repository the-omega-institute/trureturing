using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Knapsack;

internal sealed class GreedyFillPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit two-item allocations turn a change of order into a comparison of real expressions.",
        H("Two-item greedy allocation and exchange"),
        Blocks(
            Paragraph(Text(
                "Let I be any type with decidable equality, a and b distinct elements of I, w a real function on I, and B a real budget. Write g with subscript ab for greedyFill(w,[a,b],B), and g with subscript ba for the reversed list. The notation ite(P,x,y) means x when P holds and y otherwise. Define the two quantities L and R below. No sign restriction is imposed for the allocation identities; real division is total, with division by zero equal to zero.")),
            Paragraph(Math(Disp(Seq(F.Id("L"), Sp, Eq, Sp, LeftValue(), Comma, Sp,
                F.Id("R"), Sp, Eq, Sp, RightValue())))),
            Describe.Lean(
                DescribeId.Create("greedy-fill-pair"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair"),
                H("The complete two-item allocation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("i"), Colon, F.Id("I"), Comma, Sp,
                    At(Greedy("ab"), F.Id("i")), Sp, Eq, Sp,
                    Choose(Seq(F.Id("i"), Eq, F.Id("a")), F.Id("L"),
                        Choose(Seq(F.Id("i"), Eq, F.Id("b")), F.Id("R"), D(0)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function equals L at a, R at b, and zero at every other index. Expanding the two recursive steps and evaluating the two function updates gives the identity. The order of the tests preserves the first coordinate even while the second step is evaluated."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("greedy-fill-pair-apply-left"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair_apply_left"),
                H("The first coordinate"),
                StatementSource.FromAuthor(Disp(Seq(
                    At(Greedy("ab"), F.Id("a")), Sp, Eq, Sp, LeftValue()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a the allocation is one if w(a) is at most B, and B/w(a) otherwise. This is evaluation of the complete allocation at its first index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("greedy-fill-pair-apply-right"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair_apply_right"),
                H("The second coordinate"),
                StatementSource.FromAuthor(Disp(Seq(
                    At(Greedy("ab"), F.Id("b")), Sp, Eq, Sp, RightValue()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At b the allocation is zero when the first item does not fit. Otherwise it is one if w(b) is at most B-w(a), and (B-w(a))/w(b) if it is larger. Distinctness of a and b lets the second coordinate pass the first index test."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("objective-greedy-fill-pair"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/GreedyFillPair.objective_greedyFill_pair"),
                H("The return as a real expression"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("V", Greedy("ab")), Sp, Eq, Sp,
                    Choose(Fits(), Seq(Call("v", F.Id("a")), Plus,
                        Choose(SecondFits(), Call("v", F.Id("b")),
                            Seq(Ratio("b"), Open, Remaining(), Close))),
                        Seq(Ratio("a"), F.Id("B")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Now assume I is finite and let v be any real function on I. Define V(t) as the sum over I of v(i)t(i), the objective. The support identity reduces this sum to a and b. Substituting the two coordinate identities and rearranging multiplication gives the displayed formula, still without sign assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("greedy-fill-pair-swap"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/GreedyFillPair.greedyFill_pair_swap"),
                H("Ordering by return per unit weight"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Lt, Call("w", F.Id("a")), Sp, Land, Sp,
                    D(0), Lt, Call("w", F.Id("b")), Sp, Land, Sp,
                    D(0), Le, Sp, F.Id("B"), Sp, Land, Sp, Ratio("b"), Le, Ratio("a"),
                    Sp, Implies, Sp, Call("V", Greedy("ba")), Sp, Le, Sp,
                    Call("V", Greedy("ab"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite I and distinct a and b, suppose both listed weights are positive, B is nonnegative, and v(b)/w(b) is at most v(a)/w(a). Then putting a first cannot decrease the return. The returns may have either sign, and no condition is needed on unlisted weights. If both items fit together the returns coincide. Otherwise the increase is the density difference multiplied by w(a)+w(b)-B when both fit separately, by the weight of the sole item that fits when just one fits, and by B when neither fits. Each multiplier is nonnegative. Equal densities therefore give equal returns for both orders."))),
                DescribeRole.Theorem))));

    private static Formula Choose(Formula condition, Formula yes, Formula no) =>
        Call("ite", condition, yes, no);
    private static Formula At(Formula function, Formula point) => Seq(function, Open, point, Close);
    private static Formula Greedy(string order) => Seq(F.Id("g"), Underscore, Grp(F.Id(order)));
    private static Formula Fits() => Seq(Call("w", F.Id("a")), Le, Sp, F.Id("B"));
    private static Formula Remaining() => Seq(F.Id("B"), Minus, Call("w", F.Id("a")));
    private static Formula SecondFits() => Seq(Call("w", F.Id("b")), Le, Sp, Remaining());
    private static Formula Ratio(string index) =>
        Seq(Frac, Grp(Call("v", F.Id(index))), Grp(Call("w", F.Id(index))));
    private static Formula LeftValue() => Choose(Fits(), D(1),
        Seq(Frac, Grp(F.Id("B")), Grp(Call("w", F.Id("a")))));
    private static Formula RightValue() => Choose(Fits(),
        Choose(SecondFits(), D(1), Seq(Frac, Grp(Remaining()), Grp(Call("w", F.Id("b"))))), D(0));
}
