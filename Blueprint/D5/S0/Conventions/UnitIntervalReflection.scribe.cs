using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class UnitIntervalReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection about one half is an involution on the closed unit interval.",
        H("Unit-Interval Reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-interval-reflection-is-an-involution"),
                DeclarationHandle.Create(
                    "D5/S0/Conventions/UnitIntervalReflection.unit_interval_reflection_involutive"),
                H("Unit-interval reflection is an involution"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro, OpenBracket, D(0), Comma, Sp, D(1),
                    CloseBracket, Comma, Esc,
                    SigmaLower, Open, SigmaLower, Open, F.Id("s"), Close, Close,
                    Sp, Eq, Sp, F.Id("s"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every s in the closed real unit interval, the central reflection "
                        + "sigma(s) = 1 - s remains in that interval and applying sigma twice "
                        + "returns s.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. "
                        + "unitInterval.symm_involutive is an exact hit, so the Lean declaration "
                        + "is a thin wrapper around that theorem; sub_sub_cancel is a related "
                        + "algebraic hit, and the repository has no existing wrapper for this "
                        + "unit-interval statement.")),
                    Paragraph(Text(
                        "This is a continuation partial closure of the source remark, restricted "
                        + "to its s-to-one-minus-s exchange-involution clause. The weighted path "
                        + "integrals, time-reversal clauses, fluctuation law, extension to negative "
                        + "integer powers, and even-power cone selection remain unresolved."))),
                DescribeRole.Theorem))));
}
