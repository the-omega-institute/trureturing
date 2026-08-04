using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class WalkFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Phase/WalkFormula",
                "Isolate the alternating-list and endpoint-translation algebra behind the W3 walk expression."),
            H("Walk Formula Algebra"),
            Blocks(
                Paragraph(Text(
                    "This module records four algebraic laws with all structural premises explicit. It does not prove the BHK theorem, its finite certificates, or the canonical endpoint divisibility premise, and it does not identify any word, column, or Dedekind walk with the displayed expressions. The endpoint integrality theorem is only a conditional corollary and does not discharge the endpoint-translation-integrality residual.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("alternating-walk-concatenation"),
                    H("Concatenation carries the parity sign"),
                    LeanTheorem(
                        "D5/S1/Phase/WalkFormula.alternating_walk_append"),
                    LatexStatement.Create(@"$$\forall x,y\in\operatorname{List}(\mathbb{Z}),\ \operatorname{alt}(\operatorname{append}(x,y))=\operatorname{alt}(x)+(-1)^{\operatorname{length}(x)}\operatorname{alt}(y)$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Concatenating two integer coefficient lists adds the second alternating walk with sign determined by the length of the first list. No continued-fraction normalization or orbit interpretation is inferred.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("alternating-walk-reversal"),
                    H("Reversal carries the length-parity sign"),
                    LeanTheorem(
                        "D5/S1/Phase/WalkFormula.alternating_walk_reverse"),
                    LatexStatement.Create(@"$$\forall x\in\operatorname{List}(\mathbb{Z}),\ \operatorname{alt}(\operatorname{reverse}(x))=(-1)^{\operatorname{length}(x)+1}\operatorname{alt}(x)$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Literal list reversal multiplies the alternating walk by minus one to the length-plus-one power. The theorem does not identify reversal with a fixed-point branch or an inverse orbit.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("endpoint-correction-integrality"),
                    H("An explicit endpoint multiple gives an integral correction"),
                    LeanTheorem(
                        "D5/S1/Phase/WalkFormula.endpoint_correction_is_integer"),
                    LatexStatement.Create(@"$$\forall e,e',c,t\in\mathbb{Z},\ c\neq 0 \land e-e'=ct \Rightarrow \frac{[e-e']_{\mathbb{Q}}}{[c]_{\mathbb{Q}}}=[t]_{\mathbb{Q}}$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "When an integer endpoint difference is explicitly equal to a nonzero denominator times an integer translation, its rational quotient is that integer. This is only a conditional corollary and does not discharge the endpoint-translation-integrality residual; the canonical endpoint divisibility witness remains a separate semantic obligation.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("w3-endpoint-translation"),
                    H("Endpoint translation is exactly covariant"),
                    LeanTheorem(
                        "D5/S1/Phase/WalkFormula.w3_walk_endpoint_translation"),
                    LatexStatement.Create(@"$$\forall a,e,e',c\in\mathbb{Q},\ \forall t\in\mathbb{Z},\ c\neq 0 \Rightarrow 3+a+\frac{(e+c[t]_{\mathbb{Q}})-e'}{c}=\left(3+a+\frac{e-e'}{c}\right)+[t]_{\mathbb{Q}}$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Adding an integral denominator multiple to the first endpoint adds exactly that integer to the rational W3 expression. This algebraic covariance does not assert a BHK or three-walk semantic identification.")))
                ))));
}
