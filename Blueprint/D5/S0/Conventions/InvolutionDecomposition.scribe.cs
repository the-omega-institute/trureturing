using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class InvolutionDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every real-linear involution splits each vector into fixed and negated parts.",
        H("Involution Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("involution-even-odd-decomposition"),
                DeclarationHandle.Create(
                    "D5/S0/Conventions/InvolutionDecomposition.involution_even_odd_decomposition"),
                H("Every vector splits into even and odd parts"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("V"), Comma, Sp, F.Id("reverse"), Comma, Sp, F.Id("x"), Comma,
                    Esc, F.Id("reverse"), Sp, Circ, Sp, F.Id("reverse"), Sp, Eq, Sp,
                    F.Id("id"), Comma, Sp,
                    F.Id("even"), Sp, Eq, Sp, Frac,
                    Grp(F.Id("x"), Sp, Plus, Sp, F.Id("reverse"), Open, F.Id("x"), Close),
                    Grp(D(2)), Comma, Sp,
                    F.Id("odd"), Sp, Eq, Sp, Frac,
                    Grp(F.Id("x"), Sp, Minus, Sp, F.Id("reverse"), Open, F.Id("x"), Close),
                    Grp(D(2)), Comma, Sp,
                    F.Id("x"), Sp, Eq, Sp, F.Id("even"), Sp, Plus, Sp, F.Id("odd"), Sp, Land, Sp,
                    F.Id("reverse"), Open, F.Id("even"), Close, Sp, Eq, Sp, F.Id("even"), Sp, Land, Sp,
                    F.Id("reverse"), Open, F.Id("odd"), Close, Sp, Eq, Sp, Minus, F.Id("odd"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let reverse be a real-linear map whose square is the identity. For any vector x, "
                        + "the even part is one half of x plus reverse x, and the odd part is one half of "
                        + "x minus reverse x. Their sum is x; reverse fixes the even part and negates the "
                        + "odd part.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched first. LinearEquiv.ofInvolutive packages an "
                        + "involutive linear map as an equivalence, while no general even-odd decomposition "
                        + "theorem was found. The proof uses the standard linear-map addition, subtraction, "
                        + "and scalar-preservation laws together with the involution hypothesis.")),
                    Paragraph(Text(
                        "This is a continuation partial closure restricted to the algebraic reversal "
                        + "decomposition clause. The weighted integrals, trace-state vanishing, "
                        + "equilibrium-state arrow, fluctuation law, negative-power extension, and "
                        + "even-power cone selection remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
