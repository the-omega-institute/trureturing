using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class TwoStepMixingOppositeProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/TimeArrow/TwoStepMixingOppositeProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two positive doubly stochastic kernels that both reach the uniform kernel in two steps need not have "
            + "opposite-direction inner product one: on the square {-1, 1}^2 the kernel (1 + x_1 y_2 / 2)/4 and its "
            + "transpose give 5/4.",
        H("Two-Step Mixing Does Not Force Opposite Orthogonality"),
        Blocks(
            Node("pds", "Positive doubly stochastic kernel", Disp(Seq(
                    Call("P", F.Id("x"), F.Id("y")), Gt, D(0), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")), Sp, Call("P", F.Id("x"), F.Id("y")), Eq, D(1), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("x")), Sp, Call("P", F.Id("x"), F.Id("y")), Eq, D(1))),
                "A kernel on a finite state space is positive and doubly stochastic when every entry is positive "
                    + "and every row and every column sums to one.",
                "PositiveDoublyStochastic", DescribeRole.Definition),
            Node("mix", "Two-step mixing", Disp(Seq(
                    Sum, Underscore, Grp(F.Id("y")), Sp, Call("P", F.Id("x"), F.Id("y")), Sp,
                    Call("P", F.Id("y"), F.Id("z")), Eq, Sp, Frac, Grp(D(1)), Grp(Lvert, Sp, F.Id("X"), Sp, Rvert))),
                "The kernel mixes in two steps when its square is the uniform kernel Pi(x, z) = 1/|X|.",
                "MixesInTwoSteps", DescribeRole.Definition),
            Node("inner", "Opposite-direction inner product", Disp(Seq(
                    Call("I", F.Id("P"), F.Id("Q")), Eq, Sp,
                    Frac, Grp(D(1)), Grp(Lvert, Sp, F.Id("X"), Sp, Rvert, Caret, Grp(D(2))), Sp,
                    Sum, Underscore, Grp(F.Id("x"), Comma, F.Id("y")), Sp,
                    Lvert, Sp, F.Id("X"), Sp, Rvert, Sp, Call("P", F.Id("x"), F.Id("y")), Sp,
                    Lvert, Sp, F.Id("X"), Sp, Rvert, Sp, Call("Q", F.Id("y"), F.Id("x")))),
                "The one-step inner product of the forward product |X| P(x_0, x_1) of P and the backward product "
                    + "|X| Q(x_1, x_0) of Q under the uniform law on pairs of states.",
                "oppositeInnerProduct", DescribeRole.Definition),
            Node("pair", "Kernel pairs", Disp(Seq(
                    Open, F.Id("X"), Comma, Sp, F.Id("P"), Comma, Sp, F.Id("Q"), Close)),
                "A finite state space X together with two kernels P and Q on it.",
                "FiniteKernelPair", DescribeRole.Definition),
            Node("claim", "Two-step mixing forces orthogonality", Disp(Seq(
                    Forall, Sp, Open, F.Id("X"), Comma, Sp, F.Id("P"), Comma, Sp, F.Id("Q"), Close, Comma, Sp,
                    Call("PDS", F.Id("P")), Comma, Sp, Call("PDS", F.Id("Q")), Comma, Sp,
                    F.Id("P"), Caret, Grp(D(2)), Eq, F.Id("Q"), Caret, Grp(D(2)), Eq, Pi, Sp, Rightarrow, Sp,
                    Call("I", F.Id("P"), F.Id("Q")), Eq, D(1))),
                "The claim asserts that for every finite state space and all positive doubly stochastic kernels P "
                    + "and Q whose squares are the uniform kernel, the opposite-direction inner product is one.",
                "claim", DescribeRole.Definition),
            Node("result", "Refutation", Disp(new Formula.Not(F.Id("claim"))),
                "On the square {-1, 1}^2 take P(x, y) = (1 + r x_1 y_2)/4 with r = 1/2 and Q the transpose of P. "
                    + "All entries lie between 1/8 and 3/8, every row and column sums to one because y_2 and x_1 "
                    + "average to zero, and the square of P is uniform because the sum of y_1 y_2 over the square "
                    + "vanishes; the same holds for Q. Since Q(y, x) = P(x, y), the inner product is the average of "
                    + "(1 + r x_1 y_2)^2, which is 1 + r^2 = 5/4. For the kernels of the parity family the same inner "
                    + "product equals one; the example shows that this uses their common parity factor and not two-step "
                    + "mixing alone.",
                "result", DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("two-step-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args)
    {
        var result = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) result.AddRange([Comma, Sp]);
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq([.. result]);
    }
}
