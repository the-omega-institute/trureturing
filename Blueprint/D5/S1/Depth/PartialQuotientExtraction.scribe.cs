using static StrataLint.Scribe.DefinitionDsl;

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
                    LatexStatement.Create(@"$$C(q)=\operatorname{OddTail}\!\left(\operatorname{toList}(\operatorname{partDens}(\operatorname{GenContFract.of}(q)))\right)$$")
                ),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("maximum-partial-quotient"),
                    H("The normalization denominator is the extracted maximum"),
                    LeanDefinition(
                        "D5/S1/Depth/PartialQuotientExtraction.aMax"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The maximum is folded directly over C(q), with zero reserved for the empty integral tail. Neither a caller-supplied finite set nor a separately quantified rational scale participates in the definition."))),
                    LatexStatement.Create(@"$$A(q)=\max C(q)$$")
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("nonintegral-tail-nonempty"),
                    H("A nonintegral rational has a nonempty extracted tail"),
                    LeanTheorem(
                        "D5/S1/Depth/PartialQuotientExtraction.partialQuotients_nonempty"),
                    LatexStatement.Create(@"$$\forall q\in\mathbb{Q}\setminus\mathbb{Z},\ C(q)\neq\varnothing$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "A nonzero fractional part makes the first denominator of GenContFract.of present. Stream-to-list conversion and the terminal normalization preserve nonemptiness.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("extracted-maximum-positive"),
                    H("The extracted maximum is positive off the integers"),
                    LeanTheorem(
                        "D5/S1/Depth/PartialQuotientExtraction.aMax_pos"),
                    LatexStatement.Create(@"$$\forall q\in\mathbb{Q}\setminus\mathbb{Z},\ A(q)>0$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Mathlib proves every present denominator of GenContFract.of is at least one. A positive member therefore lies below the list maximum, including after the odd-tail terminal rewrite.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("continued-fraction-twelve-floor"),
                    H("The finite-sample floor uses the extracted maximum partial quotient"),
                    LeanTheorem(
                        "D5/S1/Depth/PartialQuotientExtraction.twelve_scale_is_extracted_normalized_sample_minimum"),
                    LatexStatement.Create(@"$$\forall q\in\mathbb{Q}\setminus\mathbb{Z},\ \forall S\subset_{\mathrm{fin}}\mathbb{Z},\ (\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)\land(\exists\psi_0\in S,\ |\psi_0|=12)\Rightarrow\min\left\{\frac{|\psi|}{A(q)}:\psi\in S\right\}=\frac{12}{A(q)},\qquad A(q)=\max C(q)$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a nonintegral rational q, every normalized sample member lies above twelve divided by A(q), and an absolute-value-twelve witness attains it. The theorem instantiates the frozen generic twelve-scale lemma at the extracted value; it does not identify which rational belongs to a historical sample.")))
                ))));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
