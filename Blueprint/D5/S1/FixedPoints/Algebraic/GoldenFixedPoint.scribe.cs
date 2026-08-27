using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints.Algebraic;

internal sealed class GoldenFixedPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The displayed radical is a positive fixed point of the reciprocal residual map, and it is the unique positive fixed point.",
        H("Golden Reciprocal Fixed Point Uniqueness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-golden-fixed-point-is-unique"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/Algebraic/GoldenFixedPoint."
                        + "golden_fixed_point_unique"),
                H("The golden ratio is the unique positive fixed point"),
                StatementSource.FromAuthor(FixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Define R(x) = 1 + 1/x. The displayed radical is asserted to be "
                            + "positive and to satisfy R(the displayed radical) = the displayed "
                            + "radical; the quantified clause then "
                            + "says that every positive real x is a fixed point exactly when "
                            + "it equals that radical.")),
                    Paragraph(Text(
                        "The reverse direction applies the repository's existing golden-ratio "
                            + "fixed-point theorem. For the forward direction, the existing "
                            + "reciprocal-to-quadratic equivalence gives x squared equal to "
                            + "x plus one; comparison with the golden-ratio identity factors "
                            + "the difference, and positivity excludes the other factor.")),
                    Paragraph(Text(
                        "Thus the type carries the existence witness directly as its first two "
                            + "conjuncts (positivity and fixed-point equality), and carries "
                            + "uniqueness in the final universal characterization. No continuity, "
                            + "nonzero, or conjectural premise is added."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Carrier/GoldenRatio")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Tower/GoldenFixedPoint")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Tower/QuadraticFixedPoint"))]));

    private static Formula FixedPointFormula()
    {
        Formula x = F.Id("x");
        Formula residual = Seq(D(1), Sp, Plus, Sp, Frac, Grp(D(1)), Grp(x));
        Formula radical = Seq(
            Frac, Grp(D(1), Sp, Plus, Sp, Sqrt, Grp(D(5))), Grp(D(2)));
        Formula witnessResidual = Seq(
            D(1), Sp, Plus, Sp, Frac, Grp(D(1)), Grp(radical));

        return Disp(Seq(
            D(0), Sp, Lt, Sp, radical, Sp, Land, Sp,
            Open, witnessResidual, Sp, Eq, Sp, radical, Close, Sp, Land, Sp,
            Forall, Sp, x, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Sp, Lt, Sp, x, Sp, Rightarrow, Sp,
            Open, residual, Sp, Eq, Sp, x, Sp, Iff, Sp,
            x, Sp, Eq, Sp, radical, Close, Dot));
    }
}
