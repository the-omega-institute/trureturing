using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class MeasureCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary measures make residual-intersection capture submodular.",
        H("Measure Capture Submodularity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("measure-capture-submodularity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/MeasureCapture."
                        + "measure_capture_submodular"),
                H("Residual-intersection capture is submodular for every measure"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed formula is equal in strength to "
                            + "measure_capture_submodular and to conjunct six of "
                            + "directly_provable_laws. Edge and Definition are the two Lean "
                            + "types; MeasurableSpace, Measure, and Set are the corresponding "
                            + "Mathlib type constructors; and nu, residual, cut, A, and B are "
                            + "the theorem's explicit arguments.")),
                    Paragraph(Text(
                        "The displayed name captured is exactly the theorem-local function "
                            + "S => residual intersection iUnion definition in S, cut "
                            + "definition. Formula calls named apply are ordinary Lean function "
                            + "application; union, intersection, and iUnion are respectively "
                            + "Set union, Set intersection, and the bounded iterated union in "
                            + "that local definition. No displayed name introduces an extra "
                            + "predicate or hypothesis.")),
                    Paragraph(Text(
                        "The reusable helper measure_union_add_inter_le_arbitrary proves the "
                            + "underlying arbitrary-set measure inequality by replacing the "
                            + "right set with a same-measure measurable hull. The public theorem "
                            + "identifies capture of A union B with the union of the two capture "
                            + "sets and includes capture of A intersection B in their "
                            + "intersection, yielding exactly the displayed inequality without "
                            + "a measurability premise on residual or cut."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula edgeType = F.Id("Edge");
        Formula definitionType = F.Id("Definition");
        Formula type = F.Id("Type");
        Formula nu = F.Id("nu");
        Formula residual = F.Id("residual");
        Formula cut = F.Id("cut");
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula subset = F.Id("S");
        Formula definition = F.Id("definition");
        Formula captured = F.Id("captured");
        Formula capturedDefinition = Seq(
            Call("apply", captured, subset), Sp, Eq, Sp,
            Call("intersection", residual,
                Call("iUnion", Seq(definition, Sp, InMacro, Sp, subset),
                    Call("apply", cut, definition))));
        Formula captureInequality = Seq(
            Call("apply", nu,
                Call("apply", captured, Call("union", a, b))), Sp, Plus, Sp,
            Call("apply", nu,
                Call("apply", captured, Call("intersection", a, b))), Sp,
            Leq, Sp,
            Call("apply", nu, Call("apply", captured, a)), Sp, Plus, Sp,
            Call("apply", nu, Call("apply", captured, b)));

        return Disp(Seq(
            Forall, Sp, edgeType, Comma, Sp, definitionType, Colon, Sp,
            type, Comma, Esc,
            OpenBracket, Call("MeasurableSpace", edgeType), CloseBracket,
            Comma, Sp,
            nu, Colon, Sp, Call("Measure", edgeType), Comma, Sp,
            residual, Colon, Sp, Call("Set", edgeType), Comma, Sp,
            cut, Colon, Sp, Arrow(definitionType, Call("Set", edgeType)),
            Comma, Sp,
            a, Comma, Sp, b, Colon, Sp, Call("Set", definitionType),
            Comma, Esc,
            captureInequality, Comma, Quad, Sp,
            F.Text, Grp(F.Id("where")), Sp,
            capturedDefinition, Dot));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
}
