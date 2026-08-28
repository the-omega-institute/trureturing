using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaCore;

internal sealed class OffLinePickWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The shifted finite-difference observer has a quantitative negative one-point witness at an off-line zero.",
        H("Off-Line One-Point Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("off-line-one-point-pick-witness"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaCore/OffLinePickWitness.off_line_one_point_pick_witness"),
                H("Off-line one-point witness"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("rho"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Forall, Sp, F.Id("delta"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("gamma"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("omega"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Open, F.Id("rho"), Eq, Frac, Grp(D(1)), Grp(D(2)), Plus, F.Id("delta"),
                    Plus, F.Id("i"), Cdot, Sp, F.Id("gamma"), Land, Sp,
                    D(0), Lt, F.Id("delta"), Land, Sp, D(0), Lt, F.Id("omega"), Land, Sp,
                    F.Id("omega"), Lt, F.Id("delta"), Land, Sp,
                    F.Id("xiReading"), Open, F.Id("rho"), Close, Eq, D(0), Land, Sp,
                    F.Id("xiReading"), Open, F.Id("rho"), Minus, D(2), Cdot, Sp, F.Id("omega"), Close,
                    Neq, D(0), Close, Sp, Rightarrow, Sp,
                    F.Id("diagonalValue"), Open, F.Id("omega"), Comma,
                    Minus, F.Id("gamma"), Plus, F.Id("i"), Cdot, Sp,
                    Open, F.Id("delta"), Minus, F.Id("omega"), Close, Close,
                    Eq, Minus, Frac, Grp(D(1)), Grp(F.Id("omega"), Cdot, Sp,
                    Open, F.Id("delta"), Minus, F.Id("omega"), Close), Land, Sp,
                    F.Id("diagonalValue"), Open, F.Id("omega"), Comma,
                    Minus, F.Id("gamma"), Plus, F.Id("i"), Cdot, Sp,
                    Open, F.Id("delta"), Minus, F.Id("omega"), Close, Close, Lt, D(0), Land, Sp,
                    F.Id("diagonalValue"), Open, F.Id("omega"), Comma,
                    Minus, F.Id("gamma"), Plus, F.Id("i"), Cdot, Sp,
                    Open, F.Id("delta"), Minus, F.Id("omega"), Close, Close,
                    Leq, Minus, Frac, Grp(D(4)), Grp(F.Id("delta"), Caret, D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a zero represented as one half plus a positive real displacement and an imaginary ordinate, and for a positive shift smaller than that displacement, the finite-difference observer evaluates to a negative diagonal value. The value is exactly minus the reciprocal product of the shift and the remaining displacement, and is bounded above by minus four over the squared displacement. The nonvanishing shifted evaluation is the source condition that keeps the observer defined."))),
                DescribeRole.Theorem)),
        []));
}
