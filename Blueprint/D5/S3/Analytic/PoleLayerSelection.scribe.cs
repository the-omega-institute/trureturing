using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PoleLayerSelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shifted inverse-power series selects its pole-layer coefficient by index subtraction.",
        H("Pole-Layer Coefficient Selection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shifted-inverse-power-series-selects-the-pole-layer"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/PoleLayerSelection.pole_layer_coefficient"),
                H("A fourth-order shift selects the corresponding coefficient layer"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(4), F.Id("k"), Leq, Sp, F.Id("a"), Comma, Quad,
                    OpenBracket, F.Id("u"), Caret, F.Id("a"), CloseBracket,
                    Open, Frac, Grp(Open, Minus, D(1), Close, Caret,
                    Grp(F.Id("k"), Minus, D(1))), Grp(F.Id("k")),
                    F.Id("r"), F.Id("u"), Caret, Grp(D(4), F.Id("k")),
                    F.Id("R"), Open, F.Id("u"), Close, Caret,
                    Grp(Minus, F.Id("k")), Close,
                    Eq,
                    Frac, Grp(Open, Minus, D(1), Close, Caret,
                    Grp(F.Id("k"), Minus, D(1))), Grp(F.Id("k")),
                    F.Id("r"),
                    OpenBracket, F.Id("u"), Caret,
                    Grp(F.Id("a"), Minus, D(4), F.Id("k")), CloseBracket,
                    F.Id("R"), Open, F.Id("u"), Close, Caret,
                    Grp(Minus, F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a positive order k, a row a at least 4k, a rational-coefficient "
                        + "power series R, and a rational residue product r, the coefficient "
                        + "of the shifted signed inverse power at row a equals the same scalar "
                        + "times the coefficient of R to the negative k at row a minus 4k.")),
                    Paragraph(Text(
                        "This is a thin honest assembly over pinned Mathlib's power-series "
                        + "coefficient shift and constant-scaling declarations. Mathlib has "
                        + "no named theorem for the source atom's pole-layer specialization. "
                        + "The declaration proves the exact algebraic selection formula; it "
                        + "does not assert analytic continuation, existence of poles, or the "
                        + "atom's five external row calculations."))),
                DescribeRole.Theorem))));
}
