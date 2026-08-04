using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class PartialQuotientExtractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Depth/PartialQuotientExtraction",
                "Extract a rational continued-fraction maximum and instantiate the exact twelve-scale floor."),
            H("Partial-Quotient Extraction"),
            Blocks(
                Paragraph(Text(
                    "This module makes the normalization denominator endogenous. Its finite partial-quotient tail is computed from the rational input itself by Mathlib's Euclidean continued-fraction algorithm, then placed in the odd-tail terminal convention before taking its maximum. No independent scale parameter remains. The sample-to-rational provenance remains open, and the moat, envelope, and diffusion residuals remain open.")),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("partial-quotient-extraction"),
                    H("A rational mechanically determines its finite partial-quotient tail"),
                    LeanDefinition(
                        "D5/S1/Depth/PartialQuotientExtraction.partialQuotients"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "GenContFract.of separates the integer head from its positive denominator stream. Rational termination turns that stream into a list of natural partial quotients, and an even nonempty tail receives the terminal n to n - 1, 1 rewrite. Integral inputs have an empty tail."))),
                    Disp(Seq(F.Id("C"), Open, F.Id("q"), Close, Eq, Operatorname, Grp(F.Id("OddTail")), NegThin, Left, Open, Operatorname, Grp(F.Id("toList")), Open, Operatorname, Grp(F.Id("partDens")), Open, Operatorname, Grp(F.Id("GenContFract"), Dot, F.Id("of")), Open, F.Id("q"), Close, Close, Close, Right, Close))
                ),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("maximum-partial-quotient"),
                    H("The normalization denominator is the extracted maximum"),
                    LeanDefinition(
                        "D5/S1/Depth/PartialQuotientExtraction.aMax"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The maximum is folded directly over C(q), with zero reserved for the empty integral tail. Neither a caller-supplied finite set nor a separately quantified rational scale participates in the definition."))),
                    Disp(Seq(F.Id("A"), Open, F.Id("q"), Close, Eq, Max, Sp, F.Id("C"), Open, F.Id("q"), Close))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("nonintegral-tail-nonempty"),
                    H("A nonintegral rational has a nonempty extracted tail"),
                    LeanTheorem(
                        "D5/S1/Depth/PartialQuotientExtraction.partialQuotients_nonempty"),
                    Disp(Seq(Forall, Sp, F.Id("q"), InMacro, Mathbb, Grp(F.Id("Q")), Setminus, Mathbb, Grp(F.Id("Z")), Comma, Esc, F.Id("C"), Open, F.Id("q"), Close, Neq, Varnothing)),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "A nonzero fractional part makes the first denominator of GenContFract.of present. Stream-to-list conversion and the terminal normalization preserve nonemptiness.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("extracted-maximum-positive"),
                    H("The extracted maximum is positive off the integers"),
                    LeanTheorem(
                        "D5/S1/Depth/PartialQuotientExtraction.aMax_pos"),
                    Disp(Seq(Forall, Sp, F.Id("q"), InMacro, Mathbb, Grp(F.Id("Q")), Setminus, Mathbb, Grp(F.Id("Z")), Comma, Esc, F.Id("A"), Open, F.Id("q"), Close, Gt, D(0))),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Mathlib proves every present denominator of GenContFract.of is at least one. A positive member therefore lies below the list maximum, including after the odd-tail terminal rewrite.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("continued-fraction-twelve-floor"),
                    H("The finite-sample floor uses the extracted maximum partial quotient"),
                    LeanTheorem(
                        "D5/S1/Depth/PartialQuotientExtraction.twelve_scale_is_extracted_normalized_sample_minimum"),
                    Disp(Seq(Forall, Sp, F.Id("q"), InMacro, Mathbb, Grp(F.Id("Q")), Setminus, Mathbb, Grp(F.Id("Z")), Comma, Esc, Forall, Sp, F.Id("S"), Subset, Underscore, Grp(Mathrm, Grp(F.Id("fin"))), Mathbb, Grp(F.Id("Z")), Comma, Esc, Open, Forall, Psi, InMacro, Sp, F.Id("S"), Comma, Esc, D(1, 2), Mid, Psi, Land, Psi, Neq, D(0), Close, Land, Open, Exists, Psi, Underscore, D(0), InMacro, Sp, F.Id("S"), Comma, Esc, Bar, Psi, Underscore, D(0), Bar, Eq, D(1, 2), Close, Rightarrow, Min, Left, OpenBrace, Frac, Grp(Bar, Psi, Bar), Grp(F.Id("A"), Open, F.Id("q"), Close), Colon, Psi, InMacro, Sp, F.Id("S"), Right, CloseBrace, Eq, Frac, Grp(D(1, 2)), Grp(F.Id("A"), Open, F.Id("q"), Close), Comma, Qquad, Sp, F.Id("A"), Open, F.Id("q"), Close, Eq, Max, Sp, F.Id("C"), Open, F.Id("q"), Close)),                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a nonintegral rational q, every normalized sample member lies above twelve divided by A(q), and an absolute-value-twelve witness attains it. The theorem instantiates the frozen generic twelve-scale lemma at the extracted value; it does not identify which rational belongs to a historical sample.")))
                ))));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
