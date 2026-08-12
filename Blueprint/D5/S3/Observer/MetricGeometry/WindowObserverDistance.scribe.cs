using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class WindowObserverDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite cyclic distances are exact, and the local LP doubling cost has exact unbounded "
            + "one-third growth.",
        H("Finite-Window Observer Distance and LP Doubling Cost"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-window-observer-distance-equals-cyclic-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/WindowObserverDistance."
                        + "window_observer_distance_eq_cycle_distance"),
                H("Finite-window observer distance equals cyclic distance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
                    Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("Z")), Slash, F.Id("M"), Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    F.Id("d"), Underscore, Grp(F.Id("W")), Open,
                    F.Id("a"), Comma, Sp, F.Id("b"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("cyclicDist")), Open,
                    F.Id("a"), Comma, Sp, F.Id("b"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The admissible observables are real functions on the finite cyclic window "
                        + "whose frozen ObserverMetric perturbation seminorm for the one-step "
                        + "cyclic update is at most one. A finite telescoping argument proves that "
                        + "this updateDefect-constrained ball equals the all-pairs cyclic-Lipschitz "
                        + "ball: each directed arc bounds an endpoint gap, and taking the shorter "
                        + "arc gives the cyclic metric. The distance-from-a observable belongs to "
                        + "that frozen ball through the bridge and attains the cyclic distance; "
                        + "the bridge gives the reverse bound. This is the atom's same-orbit "
                        + "finite-window clause only."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-twelve-window-antipode-attains-distance-six"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/WindowObserverDistance."
                        + "window_twelve_antipode_witness"),
                H("A twelve-window antipode attains distance six"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("f"), Sp, InMacro, Sp,
                    F.Id("B"), Underscore, Grp(F.Id("W")), Comma, Esc,
                    F.Id("f"), Open, D(0), Close, Neq, Sp, F.Id("f"), Open, D(6), Close,
                    Sp, Land, Sp,
                    Vert, Sp, F.Id("f"), Open, D(0), Close, Minus, Sp,
                    F.Id("f"), Open, D(6), Close, Vert, Sp, Eq, Sp, D(6), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the twelve-point cyclic window, the clipped distance observable based "
                        + "at zero is admissible, is nonconstant at the antipode six, and realizes "
                        + "gap six. This supplies a concrete non-vacuity witness for the "
                        + "supremum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-twelve-window-wrap-gap-is-one"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/WindowObserverDistance."
                        + "window_wrap_unit_check"),
                H("The twelve-window wrap gap is one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("cyclicDist")), Open,
                    D(0), Comma, Sp, D(1, 1), Close, Sp, Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The endpoints zero and eleven are adjacent after cyclic wrap-around. Their "
                        + "distance is one rather than eleven, checking that the finite-window "
                        + "construction is genuinely cyclic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lp-cost-at-power-two-has-the-exact-one-third-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/WindowObserverDistance."
                        + "lp_window_cost_power_two_exact"),
                H("LP cost at a power-of-two window has the exact one-third formula"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("C"), Underscore, Grp(D(2), Caret, Grp(F.Id("m"))),
                    Open, Minus, Frac, Grp(D(1)), Grp(D(3)), Close, Sp, Eq, Sp,
                    Frac,
                    Grp(D(2), Caret, Grp(F.Id("m")), Sp, Minus, Sp, D(1)),
                    Grp(D(3)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "No frozen c_n family or corresponding cost function exists in the "
                            + "observer metric modules. Accordingly C_n(x) here is the "
                            + "self-contained cost of the n-1 adjacent steps in a nonempty "
                            + "n-window, each priced at -x. Its doubling law is C_(2n)(x) = "
                            + "2 C_n(x) - x. At x = -1/3, induction on m and that doubling law "
                            + "give the displayed identity exactly.")),
                    Paragraph(Text(
                        "This theorem formalizes the arithmetic core of the certificate footnote. "
                            + "It does not identify the local recurrence with an absent external "
                            + "c_n definition and does not assert that the external eight LP pairs "
                            + "all hit; those pair data were not supplied and are not "
                            + "reconstructed here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "lp-power-two-costs-are-unbounded"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/WindowObserverDistance."
                        + "lp_window_cost_power_two_unbounded"),
                H("LP power-of-two costs are unbounded"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("B"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Exists, Sp, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("B"), Sp, Lt, Sp, Frac,
                    Grp(D(2), Caret, Grp(F.Id("m")), Sp, Minus, Sp, D(1)),
                    Grp(D(3)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real threshold B, Archimedean unboundedness of powers of two gives "
                        + "an exponent m with 2^m greater than 3B+1. Substitution into the exact "
                        + "formula proves that the corresponding local LP cost exceeds B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-four-window-lp-cost-is-one"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/WindowObserverDistance."
                        + "lp_window_cost_four"),
                H("The four-window LP cost is one"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("C"), Underscore, Grp(D(4)),
                    Open, Minus, Frac, Grp(D(1)), Grp(D(3)), Close,
                    Sp, Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Evaluating the recurrence at m = 2 gives C at four of -1/3 equal to one. "
                        + "This concrete positive value is the anti-vacuity check for the exact "
                        + "doubling formula."))),
                DescribeRole.Theorem))));
}
