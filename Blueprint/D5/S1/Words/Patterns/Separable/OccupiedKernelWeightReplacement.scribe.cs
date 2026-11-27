using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedKernelWeightReplacementDocument : IScribeDocumentDefinition
{
    private static Formula A => F.Id("A");
    private static Formula E => F.Id("E");
    private static Formula N => F.Id("n");
    private static Formula I => F.Id("i");
    private static Formula M => F.Id("m");
    private static Formula Power(Formula x, Formula y) => Seq(x, Caret, Grp(y));
    private static Formula Ratio(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Abs(Formula x) => Seq(Left, Lvert, Sp, x, Right, Rvert);
    private static Formula Profile(Formula x) => Power(Seq(Open, D(2), Plus, Abs(x), Close), Seq(Minus, Beta));
    private static Formula Difference => Call("secondDiff", Beta, N, M);
    private static Formula Residual => Call("weightError", A, M);
    private static Formula Term => Abs(Seq(Call("weightError", A, Seq(I, Plus, D(1))), Cdot, Sp,
        Call("secondDiff", Beta, N, Seq(I, Plus, D(1)))));
    private static Formula Estimate => Disp(Seq(
        Exists, Sp, A, Gt, D(0), Comma, Sp, Exists, Sp, E, Ge, D(0), Comma, Sp,
        Forall, Sp, Beta, Comma, N, Comma, Sp,
        Ratio(D(1), D(2)), Le, Sp, Beta, Le, Ratio(D(3), D(4)), Sp, Land, Sp,
        D(0), Lt, N, Sp, Longrightarrow, Sp, Open,
        Sp, Call("Summable", Seq(I, Mapsto, Sp, Term)), Sp, Land, Sp,
        Sum, Underscore, Grp(I, Eq, D(0)), Caret, Grp(Infty), Sp, Term, Sp, Le, Sp,
        D(2, 9, 8), E, Sp, Power(N, Seq(Minus, Beta, Minus, Ratio(D(3), D(2)))), Close));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Schröder jump weights admit a uniform summable replacement by their leading power.",
        H("Summed weight replacement on the positive lattice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-shifted-power-difference"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.secondDiff"),
                H("Paired second difference of the shifted power"),
                StatementSource.FromAuthor(Disp(Seq(Difference, Eq,
                    Profile(Seq(N, Plus, M)), Plus, Profile(Seq(N, Minus, M)),
                    Minus, D(2), Profile(N)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two jump directions use the same even power profile centered at n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-jump-weight-error"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.actualWeightError"),
                H("Actual positive jump coefficient minus its leading power"),
                StatementSource.FromAuthor(Disp(Seq(Residual, Eq,
                    Call("kernelWeight", Seq(M, Minus, D(1))), Minus,
                    Ratio(A, Seq(M, Cdot, Sp, Sqrt, Grp(M)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The variable m is natural. The theorem only uses positive jump sizes m=i+1, where the zero-based kernel index is exactly i."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-sample-lattice-homogeneity"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.sample_eq_lattice"),
                H("Exact homogeneity of the regularized Mellin sample"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("sample", Beta, Ratio(D(2), N), Ratio(M, N)), Eq,
                    Power(N, Seq(Beta, Plus, Ratio(D(3), D(2)))), Cdot, Sp,
                    Power(M, Seq(Minus, Ratio(D(3), D(2)))), Cdot, Sp, Difference))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real beta and both positive real lattice scales n and m, the actual shifted sample is exactly the scaled power profile difference, including the absolute value across m=n. This identity is used when replacing weights and again when converting the later generator sum to the Mellin mesh."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-summed-weight-replacement"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.actual_global_weight_replacement"),
                H("Uniform absolute replacement bound"),
                StatementSource.FromAuthor(Estimate),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the displayed bound, beta ranges over [1/2,3/4] and n over positive natural mesh sizes. The same A and E work for all of them. The error constant absorbs the actual singleton separately from the m>=2 coefficient theorem.")),
                    Paragraph(Text("For m<=n/2, the origin majorant and exact lattice homogeneity give the second-difference estimate; monotone comparison controls the inverse square-root sum. On the remaining positive lattice, 1/m<=2/n and the full absolute sample sum follows from the discrete origin, center, transition and far bands. This bounds the sum of absolute errors, not merely the signed sum."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
