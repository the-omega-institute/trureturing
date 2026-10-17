using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class ActualCountRatiosDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical actual-shape masses and every fixed-shift count ratio retain the singleton conventions.",
        H("Actual Shape Masses and Fixed Shift Ratios"),
        Blocks(
            Paragraph(Text(
                "U(n) consists of actual permutations of Fin(n) avoiding 2413 and 3142. "
                + "It includes the genuine empty and singleton permutations. Write "
                + "rho=(sqrt(2)-1)^2. Subtraction in a natural index is truncated at zero.")),
            Paragraph(Text(
                "U(n) is the class of literal permutations avoiding 2413 and 3142. "
                + "J(s,n) is its subclass with no proper cut of sign s. Put b=sqrt(2)-1, "
                + "rho=b^2, a=1-b, and ceiling=a/2. The weight shapeWeight(n) is "
                + "rho^(n+1)*card(U(n+1)); thus every shape counted has positive length. "
                + "The kernelWeight adds rho/2 at n=0 and adds zero at other indices.")),
            Describe.Lean(
                DescribeId.Create("critical-actual-shape-masses"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/ActualCountRatios.critical_shape_masses"),
                H("Critical masses and the singleton correction"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Summable", F.Id("shapeWeight")), Sp, Land, Sp,
                    Call("sum", F.Id("shapeWeight")), Eq, F.Id("b"), Sp, Land, Sp,
                    Call("Summable", F.Id("kernelWeight")), Sp, Land, Sp,
                    Call("sum", F.Id("kernelWeight")), Eq, Frac, Grp(D(1)), Grp(D(2)),
                    Sp, Land, Sp, Call("Summable", F.Id("jWeight")), Sp, Land, Sp,
                    Call("sum", F.Id("jWeight")), Eq, F.Id("ceiling"), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Call("jWeight", F.Id("n")), Eq, Frac,
                    Grp(Call("kernelWeight", F.Id("n")), Plus,
                        Frac, Grp(F.Id("rho")), Grp(D(2)), Cdot,
                        Call("indicatorZero", F.Id("n"))), Grp(D(2)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All three real series in the display are summable. Here jWeight(n) "
                        + "is rho^(n+1)*card(J(false,n+1)), and indicatorZero(n) is one at n=0 "
                        + "and zero otherwise. In addition, for every natural n, "
                        + "jWeight(n)=(kernelWeight(n)+(if n=0 then rho/2 else 0))/2. "
                        + "At positive length one both signed indecomposable classes contain "
                        + "one shape; the sign-half relation starts only at length two.")),
                    Paragraph(Text(
                        "The actual cardinality recurrence bounds the partial sums of "
                        + "shapeWeight by b. Its Cauchy product equation identifies the sum "
                        + "with the double root b. The actual signed counts then give the "
                        + "remaining two sums and the displayed pointwise correction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-shift-count-ratio"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/ActualCountRatios.actual_fixed_shift_ratio"),
                H("Full sequence ratio for every fixed shift"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Lim, Underscore, Grp(F.Id("n"), To, Infty),
                    Frac, Grp(Call("card", Call("U", Seq(F.Id("n"), Minus, F.Id("d"))))),
                    Grp(Call("card", Call("U", F.Id("n")))), Eq,
                    F.Id("rho"), Caret, F.Id("d")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The limit is along all natural sizes. No ratio limit, recurrence "
                        + "asymptotic, positivity assumption or subsequence is supplied as "
                        + "a hypothesis. The actual enumeration identifies positive-length "
                        + "counts with largeSchroder(n-1), and an actual identity or reversal "
                        + "permutation supplies the required nonempty finite carriers.")),
                    Paragraph(Text(
                        "Differentiating the formal Schroder generating function yields "
                        + "(n+3)*S(n+2)=(6*n+9)*S(n+1)-n*S(n). The adjacent ratios "
                        + "S(n+1)/S(n) increase from 2 and stay below 3+2*sqrt(2). "
                        + "Their limit satisfies L=6-1/L and is therefore 3+2*sqrt(2). "
                        + "Finite products, reciprocals and shifts give the stated actual ratio."))),
                DescribeRole.Theorem))));
}
