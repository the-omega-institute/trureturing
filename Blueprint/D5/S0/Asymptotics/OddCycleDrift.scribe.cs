using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class OddCycleDriftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd-length sign reversal forces a real drift value to vanish.",
        H("Odd-Cycle Drift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-cycle-drift-vanishes"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/OddCycleDrift.odd_cycle_drift_eq_zero"),
                H("Odd-cycle drift vanishes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("ell"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Operatorname, Grp(F.Id("Odd")), Open, F.Id("ell"), Close, Sp, Land, Sp,
                    F.Id("s"), Eq, Grp(Minus, D(1)), Caret, Grp(F.Id("ell")),
                    F.Id("s"), Sp, Rightarrow, Sp, F.Id("s"), Eq, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The wrap-around hypothesis says that one traversal of a cycle of length "
                        + "ell multiplies the real drift value by (-1)^ell. Mathlib's parity lemma "
                        + "rewrites this factor to -1 when ell is odd, leaving s = -s; linear "
                        + "arithmetic then forces s = 0.")),
                    Paragraph(Text(
                        "This is an honest partial closure of the odd-cycle parity clause in source "
                        + "theorem 5.9. Deriving the wrap equation from the periodic recurrence, the "
                        + "closed forms for cycle values, every even-cycle assertion, and all explicit "
                        + "quadratic and numerical certificates remain unresolved subitems."))),
                DescribeRole.Theorem))));
}
