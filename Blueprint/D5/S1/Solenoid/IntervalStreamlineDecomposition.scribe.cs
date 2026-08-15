using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class IntervalStreamlineDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every continuous unit-interval solenoid path has a continuous real lift and a constant hidden offset.",
        H("Unit-Interval Streamline Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-unit-interval-path-has-a-constant-hidden-offset"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/IntervalStreamlineDecomposition."
                        + "exists_interval_streamline_decomposition"),
                H("Every unit-interval path has a constant hidden offset"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, GammaLower, InMacro, Sp, F.Id("C"), Open,
                    OpenBracket, D(0), Comma, Sp, D(1), CloseBracket, Comma, Sp,
                    Mathcal, Grp(F.Id("S")), Close, Comma, Esc,
                    Exists, Sp, F.Id("x"), InMacro, Sp, F.Id("C"), Open,
                    OpenBracket, D(0), Comma, Sp, D(1), CloseBracket, Comma, Sp,
                    Mathbb, Grp(F.Id("R")), Close, Comma, Esc,
                    Exists, Sp, F.Id("c"), InMacro, Sp, Ker, Open, Pi, Close,
                    Comma, Esc, Forall, Sp, F.Id("t"), Comma, Esc,
                    GammaLower, Open, F.Id("t"), Close, Eq, Sp,
                    F.Id("realFlow"), Open, F.Id("x"), Open, F.Id("t"), Close,
                    Close, Plus, Sp, F.Id("c"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Extend the interval path continuously to the real line using the "
                            + "canonical clamping map. The frozen normalized streamline theorem "
                            + "then supplies a continuous real lift and one element of the "
                            + "projection kernel that reconstruct the extended path. Restricting "
                            + "the lift to the unit interval gives the stated decomposition.")),
                    Paragraph(Text(
                        "The projection kernel is precisely the compatible hidden family: one "
                            + "kernel element is used for every time, so the hidden coordinate is "
                            + "constant while the real lift remains continuous.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies ContinuousMap.IccExtendCM and its restriction "
                            + "identity. The universal-solenoid decomposition itself is imported "
                            + "from the frozen streamline module and applied directly."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Solenoid/StreamlineDecomposition")),
        ]));
}
