using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class PhaseFunctionCenterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The center of continuous cyclic-window matrix observables is the phase-function algebra.",
        H("The Phase-Function Center of Continuous Observables"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuous-window-center-is-the-phase-function-algebra"),
                DeclarationHandle.Create(
                    "D5/S3/ContinuousObservables/PhaseFunctionCenter."
                    + "continuous_window_center_eq_phase_functions"),
                H("The continuous window center is the phase-function algebra"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("M"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Sp,
                    F.Id("Z"), Open,
                    F.Id("C"), Open, Mathbb, Grp(F.Id("T")), Comma, Sp,
                    F.Id("M"), Underscore, F.Id("M"),
                    Open, Mathbb, Grp(F.Id("C")), Close,
                    Close, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("range")), Open,
                    Operatorname, Grp(F.Id("phaseScalarObservable")),
                    Underscore, F.Id("M"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonempty cyclic window, the center of the algebra of " +
                        "continuous matrix fields over the visible phase circle is exactly " +
                        "the range of scalar continuous fields. This identifies the center " +
                        "with the classical phase-function algebra C(T).")),
                    Paragraph(Text(
                        "A central continuous matrix field commutes with every constant matrix " +
                        "field. Pointwise, Mathlib's matrix-center theorem forces it to be a " +
                        "scalar matrix. Reading one diagonal entry produces the continuous " +
                        "scalar function and proves surjectivity onto the center. Conversely, " +
                        "scalar matrices commute pointwise with every field."))),
                DescribeRole.Theorem))));
}
