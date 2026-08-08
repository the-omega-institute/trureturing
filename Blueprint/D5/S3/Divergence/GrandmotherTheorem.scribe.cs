using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class GrandmotherTheoremDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Divergence/GrandmotherTheorem",
            "Absolutely continuous finite mass functions have nonnegative Kullback-Leibler divergence."),
        H("The Grandmother Theorem"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("absolutely-continuous-finite-masses-have-nonnegative-kl-divergence"),
                H("Absolutely continuous finite masses have nonnegative KL divergence"),
                LeanTheorem(
                    "D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg"),
                Disp(Seq(
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
                    Colon, Eq,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("p"), Open, F.Id("i"), Close, Sp,
                    Log, Open,
                    Frac,
                    Grp(F.Id("p"), Open, F.Id("i"), Close),
                    Grp(F.Id("q"), Open, F.Id("i"), Close),
                    Close, Sp, Geq, Sp, D(0), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let I be a finite alphabet and let p and q be nonnegative normalized " +
                        "real mass functions. The last hypothesis is discrete absolute " +
                        "continuity: every zero of q is a zero of p. Consequently the displayed " +
                        "finite sum is the standard boundary extension in which a zero p term " +
                        "contributes zero. The definition of D is exactly the klDivergence " +
                        "imported from ClassicalDPI; this document introduces no second " +
                        "divergence.")),
                    Paragraph(Text(
                        "The Lean proof reuses Mathlib's nonnegativity theorem for klFun. " +
                        "Pointwise multiplication by q(i) rewrites q(i) klFun(p(i)/q(i)) as " +
                        "p(i) log(p(i)/q(i)) plus q(i) minus p(i). At q(i) equal to zero, " +
                        "absolute continuity also makes p(i) zero, so the identity holds at the " +
                        "boundary; elsewhere denominator cancellation proves it directly. " +
                        "Summation preserves nonnegativity, while normalization cancels the " +
                        "affine correction. Thus the remaining sum is precisely D(p||q).")),
                    new DocumentBlock.DisplayFormula(Seq(
                        Begin, Grp(F.Id("aligned")),
                        F.Id("D"), Open,
                        F.Id("p"), Vert, Sp, F.Id("q"), Close,
                        Amp, Eq,
                        Sum, Underscore, Grp(F.Id("i")),
                        F.Id("p"), Open, F.Id("i"), Close,
                        Open, Minus, Log, Open,
                        Frac,
                        Grp(F.Id("q"), Open, F.Id("i"), Close),
                        Grp(F.Id("p"), Open, F.Id("i"), Close),
                        Close, Close, RowBreak,
                        Amp, Geq, Sp, Minus, Log, Open,
                        Sum, Underscore, Grp(F.Id("i")),
                        F.Id("p"), Open, F.Id("i"), Close,
                        Frac,
                        Grp(F.Id("q"), Open, F.Id("i"), Close),
                        Grp(F.Id("p"), Open, F.Id("i"), Close),
                        Close, RowBreak,
                        Amp, Eq, Minus, Log, Open,
                        Sum, Underscore, Grp(
                        F.Id("i"), Colon,
                        F.Id("p"), Open, F.Id("i"), Close, Gt, D(0)),
                        F.Id("q"), Open, F.Id("i"), Close,
                        Close, Geq, Sp, Minus, Log, Open,
                        Sum, Underscore, Grp(F.Id("i")),
                        F.Id("q"), Open, F.Id("i"), Close,
                        Close, Eq, D(0), Dot,
                        End, Grp(F.Id("aligned")))),
                    Paragraph(Text(
                        "Equivalently, apply Jensen's inequality for the convex function minus " +
                        "log on the support of p. The weighted argument has expectation equal " +
                        "to the q mass of that support, which is at most the total q mass one; " +
                        "monotonicity of minus log gives the final inequality. When p has full " +
                        "support, the support sum is exactly sum q(i), recovering the normalized " +
                        "identity E_p[q/p] equal to one verbatim. This is the grandmother " +
                        "mechanism: KL nonnegativity is the Jensen shadow of normalization. The " +
                        "linked Lean declaration records only nonnegativity; it does not add a " +
                        "separate equality characterization.")))))));
}
