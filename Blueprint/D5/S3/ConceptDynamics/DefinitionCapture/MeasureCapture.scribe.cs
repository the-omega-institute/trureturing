using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionCapture;

internal sealed class MeasureCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Capture mass is submodular, but it is not the CAS difference at infinity.",
        H("Capture Mass And The Infinite Bridge Failure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("measure-capture-submodularity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionCapture/MeasureCapture."
                        + "capture_weight_submodular"),
                H("Residual-intersection capture is submodular for every capture weight"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed formula is equal in strength to "
                            + "capture_weight_submodular. It is an adjacent capture-mass lemma, "
                            + "not source clause six and not a conjunct of "
                            + "directly_provable_laws. Edge and Definition are the two Lean "
                            + "types; CaptureWeight and Set are the corresponding type "
                            + "constructors; and nu, residual, cut, A, and B are "
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
                        "CaptureWeight has ENNReal-valued mass and exactly one law: "
                            + "mass_union_add_lower_le. ENNReal retains infinite values, while "
                            + "the law says that a lower set inside the intersection may replace "
                            + "that intersection in the union-plus-intersection inequality. The "
                            + "public theorem "
                            + "identifies capture of A union B with the union of the two capture "
                            + "sets and includes capture of A intersection B in their "
                            + "intersection, then applies that law once.")),
                    Paragraph(Text(
                        "The compiled constructors countingCaptureWeight, "
                            + "nonadditiveCoverageCaptureWeight, and measureCaptureWeight realize "
                            + "count, weight, and measure examples for this adjacent lemma. Their "
                            + "masses are respectively unrestricted Set.encard embedded in "
                            + "ENNReal, a nonadditive nonempty-set coverage weight, and the native "
                            + "values of an arbitrary Mathlib measure. No Finite or "
                            + "IsFiniteMeasure instance is required. The separate theorem "
                            + "measure_capture_submodular states and proves the complete arbitrary-"
                            + "measure specialization, including infinite values. The theorem "
                            + "infinite_counting_cas_bridge_fails separately proves that CAS's "
                            + "F(S) = M(empty) - M(S) cannot equal captured mass in the infinite "
                            + "counting example: the two remaining masses are infinity, F is zero, "
                            + "and the captured singleton has mass one."))),
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
            Call("mass", nu,
                Call("apply", captured, Call("union", a, b))), Sp, Plus, Sp,
            Call("mass", nu,
                Call("apply", captured, Call("intersection", a, b))), Sp,
            Leq, Sp,
            Call("mass", nu, Call("apply", captured, a)), Sp, Plus, Sp,
            Call("mass", nu, Call("apply", captured, b)));

        return Disp(Seq(
            Forall, Sp, edgeType, Comma, Sp, definitionType, Colon, Sp,
            type, Comma, Esc,
            nu, Colon, Sp, Call("CaptureWeight", edgeType), Comma, Sp,
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
