using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class CompletedZetaScatteringCollapseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The completed-zeta functional equation collapses the global scattering quotient.",
            H("Completed-Zeta Scattering Collapse"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("completed-zeta-scattering-quotient-equals-one"),
                    DeclarationHandle.Create(
                        "D5/S3/Weil/Scattering/CompletedZetaScatteringCollapse.completed_zeta_scattering_quotient_eq_one"),
                    H("The completed-zeta scattering quotient equals one"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, F.Id("s"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
                        Operatorname, Grp(F.Id("completedZetaReading")), Open, F.Id("s"), Close,
                        Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                        Frac,
                        Grp(Operatorname, Grp(F.Id("completedZetaReading")), Open,
                            D(1), Minus, F.Id("s"), Close),
                        Grp(Operatorname, Grp(F.Id("completedZetaReading")), Open,
                            F.Id("s"), Close),
                        Sp, Eq, Sp, D(1)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every complex parameter, the completed-zeta functional equation "
                            + "identifies the reflected numerator with the denominator. When that "
                            + "denominator is nonzero, division therefore gives one.")),
                        Paragraph(Text(
                            "The nonzero hypothesis is essential because Lean division is total. "
                            + "The frozen critical-line norm theorem remains the separate specialized "
                            + "statement and is not duplicated here."))),
                    DescribeRole.Theorem))));
    }
}
