using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class StreamlineTheoremDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Solenoid/StreamlineTheorem",
                "A continuous solenoid path has one hidden offset throughout its history."),
            H("The Streamline Theorem"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("continuous-solenoid-paths-have-one-hidden-offset"),
                    H("A continuous path stays on one streamline"),
                    LeanTheorem(
                        "D5/S1/Solenoid/StreamlineTheorem."
                        + "streamline_constant_offset"),
                    StatementProjectionFixtureLoader.FromLean(LeanTheorem(
                        "D5/S1/Solenoid/StreamlineTheorem."
                        + "streamline_constant_offset")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "A streamline decomposition records a continuous solenoid path, a "
                            + "continuous lift of its visible circle history, and a topological "
                            + "additive identification of the hidden kernel with the product of "
                            + "all prime-adic integer addresses. Their pointwise difference lies "
                            + "in that kernel and is the throat component of the path.")),
                        Paragraph(Text(
                            "The throat component is continuous on the connected interval and "
                            + "therefore constant. Subtracting its value at time zero gives zero "
                            + "throughout the interval, while the reconstruction identity writes "
                            + "the entire path as the visible lift translated by that one hidden "
                            + "address. Streamline identity is consequently one datum for the "
                            + "whole history, not a value that can drift with time.")))),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("a-nonconstant-hidden-history-is-not-continuous"),
                    H("A changing hidden address is not a continuous path"),
                    LeanTheorem(
                        "D5/S1/Solenoid/StreamlineTheorem."
                        + "nonconstant_offset_not_continuous"),
                    StatementProjectionFixtureLoader.FromLean(LeanTheorem(
                        "D5/S1/Solenoid/StreamlineTheorem."
                        + "nonconstant_offset_not_continuous")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If two times in the connected interval carry different hidden "
                        + "addresses, continuity would force those values to agree. The explicit "
                        + "contradiction is the negative witness excluding a fake path whose "
                        + "streamline identity changes during its history."))))),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S1/Dynamics/JumpCocycle")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S1/Solenoid/ThroatTransitionCocycle")),
            ]));
}
