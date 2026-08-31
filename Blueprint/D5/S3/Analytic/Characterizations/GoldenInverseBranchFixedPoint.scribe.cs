using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class GoldenInverseBranchFixedPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first inverse branch has the inverse golden ratio as its unique positive fixed point.",
        H("Golden Inverse-Branch Fixed Point"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-inverse-branch-positive-fixed-point"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Characterizations/GoldenInverseBranchFixedPoint."
                        + "golden_inverse_branch_positive_fixed_point_iff"),
                H("The positive fixed point is characterized exactly"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive real x, the equation one over x plus one equals x "
                            + "holds exactly when x is the inverse golden ratio.")),
                    Paragraph(Text(
                        "The forward direction clears the positive denominator and compares the "
                            + "resulting quadratic with the golden-ratio quadratic. The reverse "
                            + "direction applies the reciprocal identity from the frozen transfer "
                            + "triangle.")),
                    Paragraph(Text(
                        "Repository and pinned Mathlib searches found the supporting golden-ratio "
                            + "identities but no public theorem stating this fixed-point "
                            + "characterization."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("x");
        Formula one = D(1);
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula inverseGolden = new Formula.Power(Varphi, Seq(Minus, one));

        return Disp(Seq(
            Forall, Sp, x, Sp, InMacro, Sp, real, Comma, Sp,
            D(0), Sp, Lt, Sp, x, Sp, Rightarrow, Sp,
            Open,
            new Formula.Fraction(one, Add(x, one)), Sp, Eq, Sp, x,
            Sp, Iff, Sp,
            x, Sp, Eq, Sp, inverseGolden,
            Close, Dot));
    }
}
