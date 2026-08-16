using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport.Equality;

internal sealed class PetzRecoveryDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/DivergenceSupport/Equality/PetzRecovery.";

    private static Formula Statement()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        var w = F.Id("W");
        var r = F.Id("R");
        var x = F.Id("x");
        var y = F.Id("y");
        var wp = F.Seq(F.Open, w, p, F.Close);
        var wq = F.Seq(F.Open, w, q, F.Close);
        var qPosterior = F.Seq(
            F.Widehat, F.Grp(q), F.Underscore, F.Grp(y), F.Open, x, F.Close);

        return F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            F.Forall, F.Sp, F.Id("X"), F.Comma, F.Sp, F.Id("Y"), F.Esc,
            F.OpenBracket,
            F.Operatorname, F.Grp(F.Id("Fintype")), F.Open, F.Id("X"), F.Close,
            F.CloseBracket, F.Sp,
            F.OpenBracket,
            F.Operatorname, F.Grp(F.Id("Fintype")), F.Open, F.Id("Y"), F.Close,
            F.CloseBracket, F.Comma, F.RowBreak,
            F.Forall, F.Sp, p, F.Comma, F.Sp, q, F.Colon, F.Sp,
            F.Id("X"), F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Sp,
            w, F.Colon, F.Sp, F.Id("X"), F.To, F.Sp, F.Id("Y"), F.To, F.Sp,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.RowBreak,
            F.Open,
            F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
            F.D(0), F.Le, F.Sp, p, F.Open, x, F.Close, F.Close,
            F.Sp, F.Land, F.Sp,
            F.Sum, F.Underscore, F.Grp(x), p, F.Open, x, F.Close,
            F.Sp, F.Eq, F.Sp, F.D(1), F.Close, F.Sp, F.Rightarrow, F.RowBreak,
            F.Open,
            F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
            F.D(0), F.Le, F.Sp, q, F.Open, x, F.Close, F.Close,
            F.Sp, F.Land, F.Sp,
            F.Sum, F.Underscore, F.Grp(x), q, F.Open, x, F.Close,
            F.Sp, F.Eq, F.Sp, F.D(1), F.Close, F.Sp, F.Rightarrow, F.RowBreak,
            F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
            q, F.Open, x, F.Close, F.Sp, F.Eq, F.Sp, F.D(0),
            F.Sp, F.Rightarrow, F.Sp, p, F.Open, x, F.Close,
            F.Sp, F.Eq, F.Sp, F.D(0), F.Close, F.Sp, F.Rightarrow, F.RowBreak,
            F.Open,
            F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
            y, F.Colon, F.Sp, F.Id("Y"), F.Comma, F.Sp,
            F.D(0), F.Le, F.Sp, w, F.Open, x, F.Comma, F.Sp, y, F.Close, F.Close,
            F.Sp, F.Land, F.Sp,
            F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
            F.Sum, F.Underscore, F.Grp(y),
            w, F.Open, x, F.Comma, F.Sp, y, F.Close,
            F.Sp, F.Eq, F.Sp, F.D(1), F.Close, F.Close,
            F.Sp, F.Rightarrow, F.RowBreak,
            F.Id("D"), F.Open, p, F.Vert, F.Vert, F.Sp, q, F.Close,
            F.Sp, F.Minus, F.Sp,
            F.Id("D"), F.Open, wp, F.Vert, F.Vert, F.Sp, wq, F.Close,
            F.Sp, F.Eq, F.Sp, F.D(0), F.Sp, F.Leftrightarrow, F.RowBreak,
            F.Exists, F.Sp, r, F.Colon, F.Sp,
            F.Id("Y"), F.To, F.Sp, F.Id("X"), F.To, F.Sp,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.RowBreak,
            F.Open, F.Forall, F.Sp, y, F.Comma, F.Sp, x, F.Comma, F.Sp,
            r, F.Open, y, F.Comma, F.Sp, x, F.Close, F.Sp, F.Eq, F.Sp,
            F.Begin, F.Grp(F.Id("cases")),
            q, F.Open, x, F.Close, F.Comma, F.Sp, F.Amp,
            wq, F.Open, y, F.Close, F.Sp, F.Eq, F.Sp, F.D(0), F.RowBreak,
            qPosterior, F.Comma, F.Sp, F.Amp,
            F.Text, F.Grp(F.Id("otherwise")),
            F.End, F.Grp(F.Id("cases")), F.Close, F.Sp, F.Land, F.RowBreak,
            F.Open, F.Forall, F.Sp, y, F.Comma, F.Sp, x, F.Comma, F.Sp,
            F.D(0), F.Le, F.Sp, r, F.Open, y, F.Comma, F.Sp, x, F.Close,
            F.Close, F.Sp, F.Land, F.RowBreak,
            F.Open, F.Forall, F.Sp, y, F.Comma, F.Sp,
            F.Sum, F.Underscore, F.Grp(x),
            r, F.Open, y, F.Comma, F.Sp, x, F.Close,
            F.Sp, F.Eq, F.Sp, F.D(1), F.Close, F.Sp, F.Land, F.RowBreak,
            F.Operatorname, F.Grp(F.Id("channelOutput")),
            F.Open, r, F.Comma, F.Sp, wp, F.Close,
            F.Sp, F.Eq, F.Sp, p, F.Sp, F.Land, F.RowBreak,
            F.Operatorname, F.Grp(F.Id("channelOutput")),
            F.Open, r, F.Comma, F.Sp, wq, F.Close,
            F.Sp, F.Eq, F.Sp, q, F.Dot,
            F.End, F.Grp(F.Id("gathered"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero general-support DPI defect is equivalent to Bayesian reverse recovery.",
        H("Bayesian Reverse Recovery at Zero DPI Defect"),
        Blocks(
            Paragraph(Text(
                "This result closes only the Bayesian reverse-recovery clause of residual atom "
                + "sha256:11b1a5fd861ba4cdfeb6d0b960c829985e5e82c2cfffa878ed9f945fb22bc574.")),
            Paragraph(Text(
                "The permutation-channel zero-defect specialization REMAINS OPEN. The residual "
                + "atom as a whole is not discharged.")),
            Describe.Lean(
                DescribeId.Create("zero-dpi-defect-is-bayesian-reverse-recoverability"),
                DeclarationHandle.Create(
                    LeanPrefix + "dpi_defect_eq_zero_iff_exists_bayes_recovery"),
                H("Zero DPI defect is Bayesian reverse recoverability"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This finite result is the classical form of the equality condition named "
                        + "for Denes Petz.")),
                    Paragraph(Text(
                        "Petz's 1988 paper \"Sufficiency of Channels over von Neumann Algebras\" "
                        + "is credited here.")),
                    Paragraph(Text(
                        "The bibliographic record is verified at DOI 10.1093/qmath/39.1.97.")),
                    Paragraph(Text(
                        "Its full text was not accessible for this provenance assessment.")),
                    Paragraph(Text(
                        "No claim is made that the paper states this theorem or an equivalent "
                        + "result.")),
                    Paragraph(Text(
                        "The recovery channel is the posterior of q at outputs with positive "
                        + "q-mass and the prior q at zero-mass outputs. It is nonnegative and "
                        + "row-stochastic under the stated hypotheses.")),
                    Paragraph(Text(
                        "Zero defect makes the p and q posteriors coincide wherever p has positive "
                        + "output mass, which gives exact recovery of both inputs. Conversely, "
                        + "data processing for the recovery channel bounds the defect in the "
                        + "reverse direction, while forward data processing bounds it below.")),
                    Paragraph(Text(
                        "The theorem constructs this finite classical recovery channel only. It "
                        + "does not prove the outstanding permutation-channel specialization or "
                        + "discharge the residual atom as a whole."))),
                DescribeRole.Theorem)
        )));
}
