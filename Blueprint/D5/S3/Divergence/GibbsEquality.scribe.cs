using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class GibbsEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality in finite Gibbs' inequality characterizes identical probability distributions.",
        H("Equality in Gibbs' Inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-relative-entropy-characterizes-equal-distributions"),
                DeclarationHandle.Create("D5/S3/Divergence/GibbsEquality.kl_divergence_eq_zero_iff"),
                H("Zero relative entropy characterizes equal distributions"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, F.Id("I"), Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("I"), Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    F.Id("I"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1),
                                    Close, Sp, Land, Sp, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1),
                                    Close, Sp, Land, Sp, RowBreak,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(0),
                                    Sp, Rightarrow, Sp,
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(0), Close,
                                    Sp, Rightarrow, RowBreak,
                                    F.Id("D"), Open,
                                    F.Id("p"), Vert, Sp, F.Id("q"), Close,
                                    Eq, D(0), Sp, Leftrightarrow, Sp,
                                    F.Id("p"), Eq, F.Id("q"), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Let I be a finite alphabet. Let p and q be nonnegative normalized real " +
                                        "mass functions, and assume discrete absolute continuity: q(i) = 0 " +
                                        "implies p(i) = 0. The divergence D is the real-valued finite " +
                                        "klDivergence introduced in ClassicalDPI. Equality p = q is equality of " +
                                        "functions and hence asserts p(i) = q(i) at every letter i.")),
                                    Paragraph(Text(
                                        "Normalization rewrites D(p||q) as the finite sum of " +
                                        "q(i) klFun(p(i)/q(i)). Every summand is nonnegative. If their sum is " +
                                        "zero, the finite nonnegative-sum criterion makes every summand zero. " +
                                        "Where q(i) is positive, Mathlib's unique-zero theorem for klFun gives " +
                                        "p(i)/q(i) = 1 and therefore p(i) = q(i). Where q(i) is zero, absolute " +
                                        "continuity gives the same conclusion directly.")),
                                    Paragraph(Text(
                                        "Conversely, if p and q agree pointwise, every defining summand of the " +
                                        "divergence vanishes. Thus D(p||q) = 0 if and only if p = q. The proof " +
                                        "uses the previously established Gibbs nonnegativity theorem and the " +
                                        "strict zero characterization already supplied by Mathlib; it introduces " +
                                        "neither a new divergence nor a second strict-convexity proof."))),
                DescribeRole.Theorem
            ))));
}
