using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class TwoDimensionalEvaluationNegativeDirectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full two-coordinate complex evaluation image contains a strictly negative cross direction.",
        H("Negative Direction in a Full Evaluation Image"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-two-coordinate-evaluations-have-a-negative-cross-direction"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/TwoDimensionalEvaluationNegativeDirection."
                        + "two_dimensional_evaluation_has_negative_direction"),
                H("A full two-coordinate evaluation has a negative cross direction"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("T"), Comma, Sp,
                    Forall, Sp, F.Id("E"), Colon, Sp,
                    F.Id("T"), Sp, To, Sp, F.Id("C"), Caret, Grp(D(2)), Comma, Sp,
                    Forall, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Lt, F.Id("m"), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("dim")), Open,
                    Operatorname, Grp(F.Id("im")), Open, F.Id("E"), Close, Close,
                    Eq, D(2), Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("g"), InMacro, Sp, F.Id("T"), Comma, Sp,
                    D(4), Sp, F.Id("m"), Re, Open,
                    F.Id("E"), Open, F.Id("g"), Close, Underscore, D(1), Cdot,
                    Overline, Grp(F.Id("E"), Open, F.Id("g"), Close, Underscore, D(2)),
                    Close, Lt, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let T be a complex vector space and E a complex-linear map from T to "
                            + "two complex coordinates. If the image of E has complex dimension "
                            + "two, then it is the entire coordinate space. For every positive "
                            + "natural multiplicity m, the theorem produces g in T for which four "
                            + "times m times the real part of the first coordinate multiplied by "
                            + "the conjugate of the second is strictly negative.")),
                    Paragraph(Text(
                        "Mathlib's maximal-finrank submodule theorem turns the rank hypothesis "
                            + "into surjectivity. Lift the coordinate pair (1,-1) through E; its "
                            + "cross value is -4m, which is negative because m is positive. The "
                            + "identity evaluation on the two-coordinate complex space witnesses "
                            + "that the hypotheses are jointly satisfiable.")),
                    Paragraph(Text(
                        "The cross value is the same multiplicity-weighted real cross term used "
                            + "by the neighboring convolution-square orbit formulas."))),
                DescribeRole.Theorem))));
}
