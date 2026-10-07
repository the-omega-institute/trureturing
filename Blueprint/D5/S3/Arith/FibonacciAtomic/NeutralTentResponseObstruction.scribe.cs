using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class NeutralTentResponseObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two exact zero moments and bounded increments do not give a uniform square-root response bound.",
        H("Neutral Tents and the Square-Root Response Obstruction"),
        Blocks(
            Paragraph(Text("Fix phi to be the positive golden ratio and q=phi^(-2). "
                + "The kernel k is precisely BinetPositiveResponse.response(q,hq), "
                + "where hq proves q>0. Thus k is the Dirichlet inverse of the literal "
                + "Binet logarithmic coefficient applied to the arithmetic logarithm. "
                + "It is not a free kernel or an assumed response law.")),
            Paragraph(Text("For positive integer m, use u(m)=1/(m(m+1)) and "
                + "v(m)=log(m)/m-log(m+1)/(m+1). Let K(J) be the sum of k(d) "
                + "over 1<=d<=J, and let T(f,N) be the sum of k(d)f(floor(N/d)) "
                + "over 1<=d<=N. All sequences are real-valued and indexed by natural numbers.")),
            Paragraph(Text("Write S(f) for the set of |f(m)|/sqrt(m) at positive "
                + "integer m. The predicate I(f) below requires f(0)=0, summability "
                + "of both positive-index moment series, both exact zero moments, "
                + "nonemptiness and upper boundedness of S(f), sup S(f)<=1, "
                + "the pointwise envelope |f(m)|<=sqrt(m) for every natural m, "
                + "and |f(m)-f(m-1)|<=1 for every m>=1. It has no finite-support restriction.")),
            Paragraph(Math(InputFormula())),
            Paragraph(Text("The final quantifier uses O(f), the original zero "
                + "value, two zero moment identities, bounded unit supremum norm, "
                + "and unit adjacent increments. This class has no finite-support "
                + "restriction. Every constructed member of I also belongs to O.")),
            Paragraph(Math(OriginalFormula())),
            Describe.Lean(
                DescribeId.Create("neutral-tent-full-response-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/NeutralTentResponseObstruction.neutral_tent_response_obstruction"),
                H("The actual response is unbounded on the entire neutral input class"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There is one family F, with f_J=F(J), whose "
                        + "members have finite support and satisfy every condition in I "
                        + "simultaneously for every J>=2, including J=2. At the same "
                        + "integer cutoff N_J=64J^3, the signed response divided by sqrt(N_J) "
                        + "is at least K(J)/(16sqrt(J)). This lower bound tends to positive "
                        + "infinity as J tends to infinity through the integers.")),
                    Paragraph(Text("For each 2<=j<=J put m_j=floor(N_J/j) and "
                        + "R_j=floor(sqrt(m_j)/8). Three literal max/absolute-value "
                        + "tents, centered at m_j-2R_j, m_j and m_j+2R_j, are combined "
                        + "with coefficients (-alpha_j,1,-eta_j)/2. The ratio v(m)/u(m) "
                        + "is strictly increasing: its adjacent difference is "
                        + "(m+1)log((m+1)^2/(m(m+2)))>0. Ordered positive weighted "
                        + "averages therefore give the two exact compensating coefficients, "
                        + "with 0<alpha_j<1 and 0<eta_j<2.")),
                    Paragraph(Text("Each pulse has both exact zero moments, "
                        + "center value R_j/2, the square-root envelope and unit increments. "
                        + "An adjacent pair can meet the nonzero support of at most one "
                        + "individual tent; the same property holds between different j "
                        + "blocks. This checks the zero seams as well as the interior slopes. "
                        + "All supports lie in the finite interval from 1 to N_J, so the "
                        + "finite moment cancellations are also the exact infinite sums.")),
                    Paragraph(Text("The endpoint quotient identities are "
                        + "floor(N_J/(m_j-3R_j+1))=j and "
                        + "floor(N_J/(m_j+3R_j))=j-1. Consequently only d=j samples "
                        + "the j-th pulse, at its center; d=1, d=J+1 and all other "
                        + "divisor indices contribute zero to that pulse. The exact "
                        + "response is one half of the sum of k(j)R_j over 2<=j<=J. "
                        + "Since R_j>=J and k(1)=0, this is at least J K(J)/2. "
                        + "The identity sqrt(N_J)=8J sqrt(J) gives the original 1/16 constant.")),
                    Paragraph(Text("The actual Binet contract supplies a positive "
                        + "constant c with k(j)>=c log(j). Thus K(J)>=(J-1)c log(2) "
                        + "for J>=2, and K(J)/(16sqrt(J)) is at least "
                        + "c log(2)sqrt(J)/32. A uniform constant for every member of "
                        + "O and every positive cutoff would contradict this divergence. "
                        + "The finite-support family is used to refute a bound on the "
                        + "entire original class O, rather than defining that class.")),
                    Paragraph(Text("The inputs change with J. They are not the "
                        + "actual arithmetic partial sums H, and no fixed finite-support "
                        + "input is asserted to have a divergent normalized response. "
                        + "The obstruction proves no improvement to a Robin estimate "
                        + "or the Riemann hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula InputFormula()
    {
        var f = F.Id("f"); var m = F.Id("m");
        Formula sum(string weight) => Seq(new Formula.Subscript(Sum, Seq(m, Ge, D(1))),
            Call("f", m), Call(weight, m));
        Formula moment(string weight) => Call("Summable", Seq(m, Mapsto,
            Call("f", Seq(m, Plus, D(1))), Call(weight, Seq(m, Plus, D(1)))));
        return Disp(Seq(Call("I", f), Iff, Sp, Open,
            Call("f", D(0)), Eq, D(0), Land, Sp,
            moment("u"), Land, Sp, moment("v"), Land, Sp,
            sum("u"), Eq, D(0), Land, Sp, sum("v"), Eq, D(0), Land, Sp,
            Call("Nonempty", Call("S", f)), Land, Sp,
            Call("BddAbove", Call("S", f)), Land, Sp,
            Call("sup", Call("S", f)), Le, D(1), Land, Sp,
            Open, Forall, Sp, m, InMacro, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            Lvert, Call("f", m), Rvert, Le, Seq(Sqrt, Grp(m)), Close, Land, Sp,
            Open, Forall, Sp, m, Ge, D(1), Comma, Sp,
            Lvert, Call("f", m), Minus, Call("f", Seq(m, Minus, D(1))), Rvert,
            Le, D(1), Close, Close));
    }

    private static Formula OriginalFormula()
    {
        var f = F.Id("f"); var m = F.Id("m");
        Formula sum(string weight) => Seq(new Formula.Subscript(Sum, Seq(m, Ge, D(1))),
            Call("f", m), Call(weight, m));
        return Disp(Seq(Call("O", f), Iff, Sp, Open,
            Call("f", D(0)), Eq, D(0), Land, Sp,
            sum("u"), Eq, D(0), Land, Sp, sum("v"), Eq, D(0), Land, Sp,
            Call("Nonempty", Call("S", f)), Land, Sp,
            Call("BddAbove", Call("S", f)), Land, Sp,
            Call("sup", Call("S", f)), Le, D(1), Land, Sp,
            Open, Forall, Sp, m, Ge, D(1), Comma, Sp,
            Lvert, Call("f", m), Minus, Call("f", Seq(m, Minus, D(1))), Rvert,
            Le, D(1), Close, Close));
    }

    private static Formula TheoremFormula()
    {
        var family = F.Id("F"); var j = F.Id("J"); var f = F.Id("f");
        var n = F.Id("N"); var c = F.Id("C");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula root(Formula x) => Seq(Sqrt, Grp(x));
        Formula bound = new Formula.Fraction(Call("K", j), Seq(D(1, 6), root(j)));
        Formula cutoff = Seq(D(6, 4), new Formula.Power(j, D(3)));
        Formula fj = Call("F", j);
        Formula response = new Formula.Fraction(Call("T", fj, cutoff), root(cutoff));
        Formula absolute = new Formula.Fraction(Seq(Lvert, Call("T", f, n), Rvert), root(n));
        return Disp(Seq(Open, Exists, Sp, family, Colon, Sp,
            naturals, To, naturals, To, reals, Comma, Sp,
            Forall, Sp, j, InMacro, naturals, Comma, Sp,
            D(2), Le, Sp, j, Rightarrow, Sp, Open,
            Call("Finite", Call("support", fj)), Land, Sp, Call("I", fj), Land, Sp,
            bound, Le, response, Close, Close, Land, Sp,
            new Formula.Subscript(Lim, Seq(j, To, Infty)), bound, Eq, Infty, Land, Sp,
            Neg, Open, Exists, Sp, c, InMacro, reals, Comma, Sp,
            Forall, Sp, f, Colon, naturals, To, reals, Comma, Sp,
            Call("O", f), Rightarrow, Sp, Forall, Sp, n, InMacro, naturals, Comma, Sp,
            D(1), Le, Sp, n, Rightarrow, Sp, absolute, Le, Sp, c, Close));
    }
}
