using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class CycleRankThreePsdCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed spherical-angle inequalities characterize real cycle completions of rank at most three.",
        H("Cycle Correlations in Three Real Dimensions"),
        Blocks(Describe.Lean(
            DescribeId.Create("cycle-rank-three-psd-completion"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/CycleRankThreePsdCompletion.cycle_rank_three_iff"),
            H("The complete cycle criterion"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuadraticForms/enagylaurentvarvitsiotis2012cycle")),
            Blocks(
                Paragraph(Text("Let n be any natural number at least three and a any real-valued function on Fin n with every value in the closed interval [-1,1]. The successor next(i) is i+1 modulo n, implemented by finRotate n. There exists a real n by n positive semidefinite matrix B of real matrix rank at most three, with B(i,i)=1 and B(i,next(i))=a(i) for every i, if and only if every odd-cardinality subset F of Fin n satisfies the displayed inequality. Complement means complement inside Fin n; the cardinality on the right is cast to the real numbers. No unspecified matrix entries or global realization are given as premises.")),
                Paragraph(Text("The angles are arccos(a(i)), with values in [0,pi]. The criterion is Corollary 2.1, equation (5), of E.-Nagy, Laurent and Varvitsiotis after scaling their normalized angles by pi. Their subsequent discussion supplies the uniform rank-three bound. The statement is established classical mathematics. The closed intervals include a(i)=1 and a(i)=-1. Repeated vectors, nonspanning realizations and singular completions are retained; there is no strict positivity, genericity, orientation or distinctness assumption.")),
                Paragraph(Text("For a subset F define its cost as the sum of pi minus the angle on F and of the angle on its complement. An odd-subset inequality is exactly the assertion that this cost is at least pi. Eliminating two consecutive angles alpha and beta requires one gamma satisfying their triangle interval and every shorter-cycle inequality simultaneously. Take gamma to be the maximum of abs(alpha-beta) and the largest odd-subset lower bound. The original inequalities bound gamma above by alpha+beta and by 2pi-alpha-beta. Costs of two distinct subsets have sum at least pi, which supplies every remaining upper bound for the same gamma.")),
                Paragraph(Text("A spherical triangle with possibly repeated vertices exists whenever its three pairwise angular side lengths are in [0,pi], each is at most the sum of the other two, and their sum is at most 2pi. Use coordinates (cos(alpha),sin(alpha)cos(t),sin(alpha)sin(t)); their norm is one. The intermediate value theorem chooses t with the required inner product. Equal pairwise Gram data align the two endpoints with any existing pair in the same real three-dimensional space. The ambient isometry does not require independent or spanning endpoints, so no division by a degenerate overlap is introduced.")),
                Paragraph(Text("Induction on the number of edges constructs a closed unit-vector chain in the unchanged space R cubed. Insert the triangle vector into the eliminated edge and preserve all other vectors. Taking the Gram matrix gives positive semidefiniteness and diagonal one; its three-row factor bounds real matrix rank by three. Conversely, factor any proposed rank-three PSD matrix in that space. Remove the middle vector of two consecutive edges. The angle triangle inequality, also applied with the middle vector negated, gives the triangle interval and perimeter bound. Induction and the reverse cost identities recover every original odd-subset inequality.")),
                Paragraph(Text("This is an existence characterization of static real correlation data. It does not select a unique completion, provide a computational complexity bound, or assert a physical dynamics or empirical model. The fixed three-dimensional bound is uniform in n."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var n = F.Id("n"); var a = F.Id("a"); var b = F.Id("B");
        var i = F.Id("i"); var f = F.Id("F");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var index = Call("Fin", n);
        var bounds = All(i, index, Seq(Minus, D(1), Sp, Leq, Sp, Call("value", a, i),
            Sp, Land, Sp, Call("value", a, i), Sp, Leq, Sp, D(1)));
        var matrix = Call("Matrix", index, index, real);
        var completion = Some(b, matrix, Seq(Call("PosSemidef", b), Sp, Land, Sp,
            Call("rank", b), Sp, Leq, Sp, D(3), Sp, Land, Sp,
            Open, All(i, index, Seq(Call("entry", b, i, i), Sp, Eq, Sp, D(1))), Close, Sp, Land, Sp,
            All(i, index, Seq(Call("entry", b, i, Call("next", i)), Sp, Eq, Sp, Call("value", a, i)))));
        Formula AngleSum(Formula set) => Seq(new Formula.Subscript(Sum,
            Seq(i, Sp, InMacro, Sp, set)), Sp, Call("arccos", Call("value", a, i)));
        var inequalities = All(f, Call("Finset", index), Seq(Call("Odd", Call("card", f)),
            Sp, Rightarrow, Sp, AngleSum(f), Sp, Minus, Sp,
            AngleSum(Call("complement", f)), Sp, Leq, Sp,
            Open, Call("realcard", f), Sp, Minus, Sp, D(1), Close, Sp, Pi));
        return All(n, nat, All(a, Seq(index, Sp, To, Sp, real), Seq(
            Open, D(3), Sp, Leq, Sp, n, Sp, Land, Sp, bounds, Close, Sp, Rightarrow, Sp,
            Open, Open, completion, Close, Sp, Iff, Sp, inequalities, Close)));
    }

    private static Formula Typed(Formula name, Formula type) => Seq(Open, name, Sp, Colon, Sp, type, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
}
