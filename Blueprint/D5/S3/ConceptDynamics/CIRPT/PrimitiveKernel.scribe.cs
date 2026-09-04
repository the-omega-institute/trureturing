using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CIRPT;

internal sealed class PrimitiveKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CIRPT/PrimitiveKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four CIRPT primitive roles share one decidable equivalence-kernel interface.",
        H("CIRPT Primitive Kernels"),
        Blocks(
            DefinitionNode("primitive-axis", "PrimitiveAxis", "Primitive axis",
                "CUT, FLOW, ADMIT, and ANCHOR remain explicit role labels."),
            DefinitionNode("decidable-kernel", "DecidableKernel", "Decidable kernel",
                "A kernel packages a relation, its equivalence laws, and pairwise decidability."),
            DefinitionNode("cut-kernel", "cutKernel", "CUT kernel",
                "The CUT kernel identifies states with equal readout values."),
            DefinitionNode("flow-kernel", "flowKernel", "FLOW kernel",
                "The complete FLOW output is treated as a CUT readout."),
            DefinitionNode("admit-kernel", "admitKernel", "ADMIT kernel",
                "The ADMIT kernel compares admission truth values without deleting states."),
            DefinitionNode("anchor-kernel", "anchorKernel", "ANCHOR kernel",
                "The ANCHOR kernel compares pointed equality profiles."),
            TheoremNode("cut-kernel-reflection", "cutKernel_relation_iff",
                "CUT relation reflection", RelationFormula(
                    "cutKernel", F.Id("q"),
                    Seq(Call("q", F.Id("x")), Sp, Eq, Sp, Call("q", F.Id("y")))),
                "The constructor relation reduces exactly to equality of CUT outputs."),
            TheoremNode("flow-kernel-reflection", "flowKernel_relation_iff",
                "FLOW relation reflection", RelationFormula(
                    "flowKernel", F.Id("flow"),
                    Seq(Call("flow", F.Id("x")), Sp, Eq, Sp, Call("flow", F.Id("y")))),
                "The FLOW constructor exposes equality of complete outputs."),
            TheoremNode("admit-kernel-reflection", "admitKernel_relation_iff",
                "ADMIT relation reflection", RelationFormula(
                    "admitKernel", F.Id("admit"),
                    Seq(Call("admit", F.Id("x")), Sp, Iff, Sp,
                        Call("admit", F.Id("y")))),
                "The ADMIT constructor exposes logical equivalence of truth values."),
            TheoremNode("anchor-kernel-reflection", "anchorKernel_relation_iff",
                "ANCHOR relation reflection", RelationFormula(
                    "anchorKernel", F.Id("a"),
                    Seq(F.Id("x"), Sp, Eq, Sp, F.Id("a"), Sp, Iff, Sp,
                        F.Id("y"), Sp, Eq, Sp, F.Id("a"))),
                "The ANCHOR constructor exposes equality of pointed profiles."),
            TheoremNode("primitive-kernel-equivalence", "primitive_kernel_equivalence",
                "Primitive kernels are equivalence relations", PrimitiveEquivalenceFormula(),
                "Equality kernels and truth-profile kernels are reflexive, symmetric, and transitive."),
            TheoremNode("cut-kernel-is-canonical-concept-kernel",
                "cutKernel_relation_eq_conceptKernel", "CUT is the canonical concept kernel",
                ConceptKernelFormula(),
                "A singleton dependent concept family recovers exactly the CUT collision set."),
            TheoremNode("admit-kernel-boolean-readout",
                "admitKernel_relation_iff_bool_readout", "ADMIT Boolean readout",
                BoolReadoutFormula(
                    "admitKernel", F.Id("admit"), Call("admit", F.Id("state"))),
                "Deciding the admission proposition into Bool preserves its kernel exactly."),
            TheoremNode("anchor-kernel-boolean-readout",
                "anchorKernel_relation_iff_bool_readout", "ANCHOR Boolean readout",
                BoolReadoutFormula(
                    "anchorKernel", F.Id("a"),
                    Seq(F.Id("state"), Sp, Eq, Sp, F.Id("a"))),
                "Deciding equality with the anchor into Bool preserves its kernel exactly."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id, string declaration, string title, Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

    private static Formula RelationFormula(
        string kernel, Formula parameter, Formula right) => Disp(Seq(
        Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("relation", Call(kernel, parameter),
            F.Id("x"), F.Id("y")), Sp, Iff, Sp, right, Dot));

    private static Formula PrimitiveEquivalenceFormula() => Disp(Seq(
        Call("Equivalence", Call("relation", Call("cutKernel", F.Id("q")))), Sp, Land, RowBreak,
        Call("Equivalence", Call("relation", Call("flowKernel", F.Id("flow")))), Sp, Land, RowBreak,
        Call("Equivalence", Call("relation", Call("admitKernel", F.Id("admit")))), Sp, Land, RowBreak,
        Call("Equivalence", Call("relation", Call("anchorKernel", F.Id("a")))), Dot));

    private static Formula ConceptKernelFormula()
    {
        Formula pair = Seq(Open, F.Id("x"), Comma, F.Id("y"), Close);
        Formula family = Seq(
            LambdaLower, Sp, F.Id("u"), Colon, Sp, F.Id("Unit"), Comma, Sp, F.Id("q"));
        Formula unit = Seq(Open, Close);
        return Disp(Seq(
            OpenBrace, pair, Sp, Mid, Sp,
            Call("relation", Call("cutKernel", F.Id("q")), F.Id("x"), F.Id("y")), CloseBrace,
            Sp, Eq, Sp, Call("conceptKernel", family, unit), Dot));
    }

    private static Formula BoolReadoutFormula(
        string kernel, Formula parameter, Formula predicate)
    {
        Formula readout = Seq(
            LambdaLower, Sp, F.Id("state"), Comma, Sp, Call("decide", predicate));
        return Disp(Seq(
            Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
            Call("relation", Call(kernel, parameter), F.Id("x"), F.Id("y")),
            Sp, Iff, Sp,
            Call("ker", readout, F.Id("x"), F.Id("y")), Dot));
    }
}
