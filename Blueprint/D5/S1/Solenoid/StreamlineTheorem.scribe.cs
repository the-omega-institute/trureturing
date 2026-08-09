using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class StreamlineTheoremDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Solenoid/StreamlineTheorem",
                "For a supplied solenoid decomposition, the throat offset is continuous exactly when it is constant."),
            H("Conditional Streamline Rigidity"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("a-supplied-decomposition-has-a-rigid-throat-offset"),
                    H("A supplied decomposition has a rigid throat offset"),
                    LeanTheorem(
                        "D5/S1/Solenoid/StreamlineTheorem."
                        + "streamline_offset_continuous_iff_constant"),
                    Disp(Seq(
                        Operatorname, Grp(F.Id("ContinuousOn")),
                        Open, F.Id("c"), Underscore, F.Id("d"), Comma, Sp,
                        F.Id("I"), Close, Sp, Leftrightarrow, Sp,
                        Forall, Sp, F.Id("t"), InMacro, Sp, F.Id("I"), Comma, Esc,
                        F.Id("c"), Underscore, F.Id("d"), Open, F.Id("t"), Close,
                        Sp, Eq, Sp,
                        F.Id("c"), Underscore, F.Id("d"), Open, F.Id("t"),
                        Underscore, D(0), Close)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "The theorem takes a StreamlineDecomposition as explicit input. It "
                            + "contains a solenoid-valued history, a chosen visible lift with the "
                            + "same visible projection, and an additive identification of the "
                            + "hidden kernel with the product of all prime-adic integer addresses. "
                            + "Their pointwise difference is the supplied decomposition's throat "
                            + "component, and path_decomposition gives its pointwise reconstruction.")),
                        Paragraph(Text(
                            "On a preconnected real interval, the supplied throat component is "
                            + "continuous if and only if it agrees everywhere with its value at a "
                            + "chosen base point. The forward implication directly applies the "
                            + "frozen hidden-fiber rigidity theorem; the reverse implication is "
                            + "continuity of a constant map.")),
                        Paragraph(Text(
                            "Residual: this result does not construct a decomposition from an "
                            + "arbitrary continuous solenoid path, choose a canonical visible "
                            + "projection lift, or prove such a choice is canonical. Those "
                            + "existence and canonicity obligations remain open rather than being "
                            + "inferred from the conditional rigidity statement.")))),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("a-nonconstant-hidden-history-is-not-continuous"),
                    H("A changing hidden address is not continuous"),
                    LeanTheorem(
                        "D5/S1/Solenoid/StreamlineTheorem."
                        + "nonconstant_offset_not_continuous"),
                    Disp(Seq(
                        F.Id("x"), Comma, Sp, F.Id("y"), InMacro, Sp, F.Id("I"),
                        Comma, Quad, Sp, F.Id("k"), Open, F.Id("x"), Close, Sp, Neq, Sp,
                        F.Id("k"), Open, F.Id("y"), Close, Sp, Rightarrow, Sp, Neg,
                        Operatorname, Grp(F.Id("ContinuousOn")),
                        Open, F.Id("k"), Comma, Sp, F.Id("I"), Close)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If two times in the connected interval carry different hidden "
                        + "addresses, continuity would force those values to agree. The explicit "
                        + "contradiction is the negative witness excluding a nonconstant "
                        + "candidate throat history."))))),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S3/Arith/HiddenFiberRigidity")),
            ]));
}
