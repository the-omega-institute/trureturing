using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class VisiblePhaseInfinityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ENNReal observable-supremum distance is infinite across distinct visible phases.",
        H("Visible-Phase Infinity of the Observer Distance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("distinct-visible-phases-have-top-observer-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/VisiblePhaseInfinity."
                        + "visible_phase_separation_distance_eq_top"),
                H("Distinct visible phases have top observer distance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("tau"), Sp, F.Id("x"), Sp, F.Id("y"), Comma, Sp,
                    F.Id("hphase"), Sp, InMacro, Sp, F.Id("H"), Comma, Esc,
                    F.Id("projection"), Open, F.Id("x"), Close, Neq, Sp,
                    F.Id("projection"), Open, F.Id("y"), Close, Sp, Rightarrow, Sp,
                    F.Id("observerDistance"), Open, F.Id("tau"), Comma, F.Id("x"),
                    Comma, F.Id("y"), Close, Sp, Eq, Sp, Infty, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The distance is the supremum in ENNReal of the endpoint gaps of continuous "
                        + "complex observables whose read-update defect is at most one. If the "
                        + "update preserves the visible projection, the phase character obtained "
                        + "from AddCircle.toCircle has exactly zero defect. Scaling that character "
                        + "by every natural number gives admissible gaps with no finite upper bound. "
                        + "This is the finite observable-supremum shadow only; it does not claim a "
                        + "spectral triple, a bundle identification, or a type-II classification."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hidden-translation-preserves-phase-and-is-nonidentity"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/VisiblePhaseInfinity."
                        + "hiddenTranslation_visible_phase_witness"),
                H("A nonidentity hidden translation supplies the witness"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("tau"), Comma, Esc,
                    F.Id("tau"), Neq, Sp, F.Id("refl"), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("z"), Comma, Sp,
                    Operatorname, Grp(F.Id("proj")), Open, F.Id("tau"), Caret, Grp(Minus, D(1)),
                    F.Id("z"), Close, Eq,
                    Operatorname, Grp(F.Id("proj")), Open, F.Id("z"), Close, Close, Sp, Land, Esc,
                    Operatorname, Grp(F.Id("proj")), Open,
                    Operatorname, Grp(F.Id("flow")), Open, D(0), Close, Close, Neq, Sp,
                    Operatorname, Grp(F.Id("proj")), Open,
                    Operatorname, Grp(F.Id("flow")), Open, Frac, Grp(D(1)), Grp(D(2)), Close, Close,
                    Sp, Land, Esc,
                    F.Id("observerDistance"), Open, F.Id("tau"), Comma, Sp,
                    Operatorname, Grp(F.Id("flow")), Open, D(0), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("flow")), Open, Frac, Grp(D(1)), Grp(D(2)), Close, Close,
                    Sp, Eq, Sp, Infty, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The translation by the frozen nonzero hidden-unit offset is a genuine "
                        + "permutation of the solenoid. Its offset lies in the kernel of the visible "
                        + "projection, so the phase-preservation hypothesis holds. The real-flow "
                        + "points at zero and one half have distinct visible phases, and the main "
                        + "theorem therefore gives top distance for this concrete nonidentity update."))),
                DescribeRole.Theorem))));
}
