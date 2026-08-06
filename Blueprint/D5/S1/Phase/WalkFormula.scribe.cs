using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                    Disp(Seq(Forall, Sp, F.Id("x"), Comma, F.Id("y"), InMacro, Operatorname, Grp(F.Id("List")), Open, Mathbb, Grp(F.Id("Z")), Close, Comma, Esc, Operatorname, Grp(F.Id("alt")), Open, Operatorname, Grp(F.Id("append")), Open, F.Id("x"), Comma, F.Id("y"), Close, Close, Eq, Operatorname, Grp(F.Id("alt")), Open, F.Id("x"), Close, Plus, Open, Minus, D(1), Close, Caret, Grp(Operatorname, Grp(F.Id("length")), Open, F.Id("x"), Close), Operatorname, Grp(F.Id("alt")), Open, F.Id("y"), Close)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Concatenating two integer coefficient lists adds the second alternating walk with sign determined by the length of the first list. No continued-fraction normalization or orbit interpretation is inferred.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("alternating-walk-reversal"),
                    H("Reversal carries the length-parity sign"),
                    LeanTheorem(
                        "D5/S1/Phase/WalkFormula.alternating_walk_reverse"),
                    Disp(Seq(Forall, Sp, F.Id("x"), InMacro, Operatorname, Grp(F.Id("List")), Open, Mathbb, Grp(F.Id("Z")), Close, Comma, Esc, Operatorname, Grp(F.Id("alt")), Open, Operatorname, Grp(F.Id("reverse")), Open, F.Id("x"), Close, Close, Eq, Open, Minus, D(1), Close, Caret, Grp(Operatorname, Grp(F.Id("length")), Open, F.Id("x"), Close, Plus, D(1)), Operatorname, Grp(F.Id("alt")), Open, F.Id("x"), Close)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Literal list reversal multiplies the alternating walk by minus one to the length-plus-one power. The theorem does not identify reversal with a fixed-point branch or an inverse orbit.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("endpoint-correction-integrality"),
                    H("An explicit endpoint multiple gives an integral correction"),
                    LeanTheorem(
                        "D5/S1/Phase/WalkFormula.endpoint_correction_is_integer"),
                    Disp(Seq(Forall, Sp, F.Id("e"), Comma, F.Id("e"), Apos, Comma, F.Id("c"), Comma, F.Id("t"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, F.Id("c"), Neq, Sp, D(0), Sp, Land, Sp, F.Id("e"), Minus, F.Id("e"), Apos, Eq, F.Id("ct"), Sp, Rightarrow, Sp, Frac, Grp(OpenBracket, F.Id("e"), Minus, F.Id("e"), Apos, CloseBracket, Underscore, Grp(Mathbb, Grp(F.Id("Q")))), Grp(OpenBracket, F.Id("c"), CloseBracket, Underscore, Grp(Mathbb, Grp(F.Id("Q")))), Eq, OpenBracket, F.Id("t"), CloseBracket, Underscore, Grp(Mathbb, Grp(F.Id("Q"))))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "When an integer endpoint difference is explicitly equal to a nonzero denominator times an integer translation, its rational quotient is that integer. This is only a conditional corollary and does not discharge the endpoint-translation-integrality residual; the canonical endpoint divisibility witness remains a separate semantic obligation.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("w3-endpoint-translation"),
                    H("Endpoint translation is exactly covariant"),
                    LeanTheorem(
                        "D5/S1/Phase/WalkFormula.w3_walk_endpoint_translation"),
                    Disp(Seq(Forall, Sp, F.Id("a"), Comma, F.Id("e"), Comma, F.Id("e"), Apos, Comma, F.Id("c"), InMacro, Mathbb, Grp(F.Id("Q")), Comma, Esc, Forall, Sp, F.Id("t"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, F.Id("c"), Neq, Sp, D(0), Sp, Rightarrow, Sp, D(3), Plus, F.Id("a"), Plus, Frac, Grp(Open, F.Id("e"), Plus, F.Id("c"), OpenBracket, F.Id("t"), CloseBracket, Underscore, Grp(Mathbb, Grp(F.Id("Q"))), Close, Minus, F.Id("e"), Apos), Grp(F.Id("c")), Eq, Left, Open, D(3), Plus, F.Id("a"), Plus, Frac, Grp(F.Id("e"), Minus, F.Id("e"), Apos), Grp(F.Id("c")), Right, Close, Plus, OpenBracket, F.Id("t"), CloseBracket, Underscore, Grp(Mathbb, Grp(F.Id("Q"))))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Adding an integral denominator multiple to the first endpoint adds exactly that integer to the rational W3 expression. This algebraic covariance does not assert a BHK or three-walk semantic identification.")))
                )),
[
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Phase/WalkFormula.alternating_walk_append")),
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Phase/WalkFormula.alternating_walk_reverse")),
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Phase/WalkFormula.endpoint_correction_is_integer")),
                        DocumentEdge.TruthAnchor.Create(
                            LeanDeclarationRef.Create("D5/S1/Phase/WalkFormula.w3_walk_endpoint_translation")),
                    ]));
}
