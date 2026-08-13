using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class ZetaConjugationCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Riemann zeta and both completed readings commute with conjugation and conjugate reflection.",
        H("Zeta Conjugation Covariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completed-zeta-commutes-with-conjugation"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/ZetaConjugationCovariance."
                    + "completed_riemann_zeta_conj"),
                H("Completed zeta commutes with conjugation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")),
                    Comma, Esc, Lambda, Open, Overline, Grp(F.Id("s")), Close,
                    Sp, Eq, Sp, Overline, Grp(Lambda, Open, F.Id("s"), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every complex parameter, mathlib's meromorphic completed Riemann zeta "
                    + "at the conjugate parameter equals the conjugate of its original value. "
                    + "The proof first transports conjugation through the real theta-kernel Mellin "
                    + "integral defining the pole-removed completion, then restores the explicit "
                    + "pole terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completed-zeta-has-antiunitary-covariance"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/ZetaConjugationCovariance."
                    + "completed_riemann_zeta_one_sub_conj"),
                H("Completed zeta has antiunitary covariance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")),
                    Comma, Esc, Lambda, Open, D(1), Sp, Minus, Sp,
                    Overline, Grp(F.Id("s")), Close, Sp, Eq, Sp,
                    Overline, Grp(Lambda, Open, F.Id("s"), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every complex parameter, completed zeta at one minus the conjugate "
                    + "parameter equals the conjugate of completed zeta at the original parameter. "
                    + "This composes the global conjugation theorem with mathlib's completed-zeta "
                    + "functional equation; no pole exclusions or analytic hypotheses are added."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("riemann-zeta-commutes-with-conjugation"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.riemann_zeta_conj"),
                H("Riemann zeta commutes with conjugation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")),
                    Comma, Esc, Zeta, Open, Overline, Grp(F.Id("s")), Close,
                    Sp, Eq, Sp, Overline, Grp(Zeta, Open, F.Id("s"), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conjugation covariance holds for every complex parameter, including "
                    + "mathlib's totalized value at zero. Away from zero the proof divides the "
                    + "completed covariance by the conjugation-compatible real Gamma factor; the "
                    + "zero case uses the exact value zeta of zero equals minus one-half."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("xi-reading-commutes-with-conjugation"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/ZetaConjugationCovariance.xi_reading_conj"),
                H("Xi reading commutes with conjugation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")),
                    Comma, Esc, Xi, Open, Overline, Grp(F.Id("s")), Close,
                    Sp, Eq, Sp, Overline, Grp(Xi, Open, F.Id("s"), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The repository's entire xi reading inherits global conjugation covariance "
                    + "from the pole-removed completed zeta function and its real polynomial "
                    + "prefactor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("xi-reading-has-antiunitary-covariance"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/ZetaConjugationCovariance."
                    + "xi_reading_one_sub_conj"),
                H("Xi reading has antiunitary covariance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")),
                    Comma, Esc, Xi, Open, D(1), Sp, Minus, Sp,
                    Overline, Grp(F.Id("s")), Close, Sp, Eq, Sp,
                    Overline, Grp(Xi, Open, F.Id("s"), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The entire completed reading satisfies the same conjugate-reflection identity. "
                    + "The proof composes its newly proved conjugation covariance with the frozen "
                    + "xi reflection theorem."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/CompletedZeta")),
        ]));
}
