using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Knapsack;

internal sealed class GridDualStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite two-point grids have an exact fractional linear program, and every fractional optimum matches its row density as a dual price.",
        H("Finite grid duality and optimal fill structure"),
        Blocks(
            Paragraph(Text(
                "Let I be any finite index type. For each i, let c(i) and d(i) be real endpoints. Write f(x)=log(1-exp(-x)), h(i)=d(i)-c(i), Delta(i)=f(d(i))-f(c(i)), rho(i)=Delta(i)/h(i), and R=M-sum c(i). The feasible set F consists of real-valued functions a on I with 0<=a(i)<=1 and sum h(i)a(i)<=R. These constraints use only an upper expected coordinate-sum budget.")),
            Paragraph(Math(Disp(Definitions()))),
            Paragraph(Text(
                "Write V(a)=sum [f(c(i))+a(i)Delta(i)] and D(p)=p M+sum max(f(c(i))-p c(i),f(d(i))-p d(i)). The grid dual G is the infimum of D(p) over nonnegative real prices p. Optimal(a) means that a is feasible and V(a) equals the supremum of V over F.")),
            Describe.Lean(
                DescribeId.Create("grid-dual-eq-fill-sup"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/GridDualStructure.grid_dual_eq_fill_sup"),
                H("The exact fractional linear program"),
                StatementSource.FromAuthor(Disp(Seq(F.Id("G"), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("sup")), Underscore,
                    Grp(F.Id("a"), Sp, InMacro, Sp, F.Id("F")), Sp, Call("V", F.Id("a"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume 0<c(i)<d(i) for every i and sum c(i)<=M. Then G equals the supremum of V on F. Subtracting the lower endpoints gives positive weights h, positive returns Delta, and nonnegative budget R. The fractional-knapsack strong duality theorem applies to these data. Translation by the constant sum f(c(i)) carries its supremum and price infimum to the displayed equality. The index type may be empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("slack-fill-improvable"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/GridDualStructure.slack_fill_improvable"),
                H("Strict improvement with spare budget"),
                StatementSource.FromAuthor(Disp(Seq(Exists, Sp, F.Id("b"), Sp, InMacro, Sp,
                    F.Id("F"), Comma, Sp, Call("V", F.Id("a")), Sp, Lt, Sp,
                    Call("V", F.Id("b"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume a belongs to F, a(j)<1, h(j)>0, Delta(j)>0, and sum h(i)a(i)<R. There is a feasible b with V(a)<V(b). No positivity assumption is imposed on other rows in this assertion. Increase coordinate j by epsilon=min(1-a(j),(R-sum h(i)a(i))/h(j)), leaving all other coordinates fixed. Both entries of this minimum are positive. Its two upper bounds preserve the box and budget constraints, and the return increases by Delta(j)epsilon>0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fractional-optimum-saturates"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/GridDualStructure.fractional_optimum_saturates"),
                H("A fractional optimum saturates the budget"),
                StatementSource.FromAuthor(Disp(Seq(SumI(Seq(Call("h", F.Id("i")),
                    Call("a", F.Id("i")))), Sp, Eq, Sp, F.Id("R")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume 0<c(i)<d(i) for all i, Optimal(a), and 0<a(j)<1. Then sum h(i)a(i)=R. Strict monotonicity of f on positive reals gives Delta(j)>0. A strict budget inequality would permit the preceding improvement and contradict attainment of the supremum. This assertion applies to every optimal fill and does not require an extreme-point hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fractional-optimum-matching-price"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/GridDualStructure.fractional_optimum_matching_price"),
                H("The fractional row supplies an attaining price"),
                StatementSource.FromAuthor(Disp(Matching())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume 0<c(i)<d(i) for every i, Optimal(a), and 0<a(j)<1. Put p=rho(j). Then p>0, each row satisfies (1-a(i))(f(c(i))-p c(i))+a(i)(f(d(i))-p d(i))=max(f(c(i))-p c(i),f(d(i))-p d(i)), every full row has rho(i)>=p, every empty row has rho(i)<=p, and D(p)=G.")),
                    Paragraph(Text(
                        "A greedy certificate supplies an attaining nonnegative price. Optimality of a identifies its return with the certificate value. Budget saturation then makes the sum of nonnegative row dual gaps zero, so every row gap is zero. At the strictly fractional row, this equality forces Delta(j)-p h(j)=0. Substitution yields the claimed price, the row maxima, and both density inequalities. Ties are retained by the non-strict inequalities; no uniqueness of the fractional row is needed."))),
                DescribeRole.Theorem))));

    private static Formula SumI(Formula body) => Seq(Sum, Underscore,
        Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("I")), Sp, body);

    private static Formula Definitions() => Seq(
        Call("h", F.Id("i")), Sp, Eq, Sp, Call("d", F.Id("i")), Minus,
        Call("c", F.Id("i")), Comma, Sp,
        F.Id("R"), Sp, Eq, Sp, F.Id("M"), Minus, SumI(Call("c", F.Id("i"))));

    private static Formula Matching() => Seq(
        F.Id("p"), Sp, Eq, Sp, Call("rho", F.Id("j")), Sp, Gt, Sp, D(0),
        Comma, Sp, Call("D", F.Id("p")), Sp, Eq, Sp, F.Id("G"));
}
