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
                new DocumentBlock.Describe(
                    DescribeId.Create("alternating-walk-concatenation"),
                    DescribeKind.Theorem,
                    H("Concatenation carries the parity sign"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/WalkFormula.alternating_walk_append")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Concatenating two integer coefficient lists adds the second alternating walk with sign determined by the length of the first list. No continued-fraction normalization or orbit interpretation is inferred.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("alternating-walk-reversal"),
                    DescribeKind.Theorem,
                    H("Reversal carries the length-parity sign"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/WalkFormula.alternating_walk_reverse")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Literal list reversal multiplies the alternating walk by minus one to the length-plus-one power. The theorem does not identify reversal with a fixed-point branch or an inverse orbit.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("endpoint-correction-integrality"),
                    DescribeKind.Theorem,
                    H("An explicit endpoint multiple gives an integral correction"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/WalkFormula.endpoint_correction_is_integer")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "When an integer endpoint difference is explicitly equal to a nonzero denominator times an integer translation, its rational quotient is that integer. This is only a conditional corollary and does not discharge the endpoint-translation-integrality residual; the canonical endpoint divisibility witness remains a separate semantic obligation.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("w3-endpoint-translation"),
                    DescribeKind.Theorem,
                    H("Endpoint translation is exactly covariant"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Phase/WalkFormula.w3_walk_endpoint_translation")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Adding an integral denominator multiple to the first endpoint adds exactly that integer to the rational W3 expression. This algebraic covariance does not assert a BHK or three-walk semantic identification.")))))));
}
