using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CIRPT;

internal sealed class UnifiedResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CIRPT/UnifiedResidual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel difference is the common residual calculus for all four CIRPT roles.",
        H("Unified CIRPT Residual Calculus"),
        Blocks(
            DefinitionNode("kernel-residual", "kernelResidual", "Kernel residual",
                "A residual contains pairs retained by the current kernel and rejected by the target kernel."),
            DefinitionNode("identity-kernel", "identityKernel", "Identity kernel",
                "The identity readout packages the equality diagonal as a decidable kernel."),
            DefinitionNode("escape-of-kernel", "escapeOfKernel", "Absolute kernel escape",
                "Absolute escape specializes the residual to the identity target."),
            DefinitionNode("cut-defect", "cutDefect", "CUT defect",
                "The CUT defect is the current CUT residual against a target readout kernel."),
            DefinitionNode("flow-defect", "flowDefect", "FLOW defect",
                "The FLOW defect targets the observed complete flow output."),
            DefinitionNode("admit-defect", "admitDefect", "ADMIT defect",
                "The ADMIT defect targets equality of admission truth values."),
            DefinitionNode("anchor-defect", "anchorDefect", "ANCHOR defect",
                "The symmetric ANCHOR defect targets equality of pointed profiles."),
            DefinitionNode("bundle-role-defect", "bundleRoleDefect", "Bundle role defect",
                "A role defect contains current-kernel pairs separated by at least one atom carrying that role."),
            TheoremNode("cut-residual-is-canonical-defect",
                "kernelResidual_cut_eq_defectRelation",
                "CUT residual is the canonical defect relation", CutBridgeFormula(),
                "Specializing both kernels to CUT readouts recovers the imported canonical defect relation exactly."),
            TheoremNode("escape-is-kernel-minus-diagonal",
                "escapeOfKernel_eq_sdiff_diagonal",
                "Absolute escape removes the diagonal", EscapeFormula(),
                "The identity target removes precisely the equality diagonal from the current kernel."),
            TheoremNode("residual-extensionality", "residual_extensional",
                "Residual extensionality", ExtensionalFormula(),
                "Pointwise equivalent current and target relations determine the same residual set."),
            TheoremNode("joint-target-residual-union",
                "residual_joint_target_eq_iUnion",
                "Joint-target residual is a union", JointTargetFormula(),
                "CIRPT-IE-006 holds for an arbitrary indexed target family and its joint kernel."),
            TheoremNode("bundle-joint-target-residual-union",
                "residual_joint_target_eq_iUnion_bundle",
                "Bundle joint-target residual is a union", BundleJointTargetFormula(),
                "The finite primitive-bundle form is the engine corollary of CIRPT-IE-006."),
            TheoremNode("four-role-residual-union", "four_role_residual_eq_union",
                "Four-role residual union", FourRoleFormula(),
                "The combined CUT, FLOW, ADMIT, and ANCHOR target has the exact union of role defects."),
            TheoremNode("postprocessing-residual-monotonicity",
                "postprocessing_residual_mono",
                "Target postprocessing contracts residuals", PostprocessingFormula(),
                "A distinction surviving postprocessing already survives before postprocessing."))));

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

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Relation(Formula kernel, Formula left, Formula right) =>
        Call("relation", kernel, left, right);

    private static Formula CutBridgeFormula() => Disp(Seq(
        Call("kernelResidual", Call("cutKernel", F.Id("q")),
            Call("cutKernel", F.Id("T"))),
        Sp, Eq, Sp, Call("defectRelation", F.Id("q"), F.Id("T")), Dot));

    private static Formula EscapeFormula()
    {
        Formula pair = Seq(Open, F.Id("x"), Comma, Sp, F.Id("y"), Close);
        Formula kernelPairs = Seq(
            OpenBrace, pair, Sp, Mid, Sp,
            Relation(F.Id("K"), F.Id("x"), F.Id("y")), CloseBrace);
        return Disp(Seq(
            Call("escapeOfKernel", F.Id("K")), Sp, Eq, Sp,
            kernelPairs, Sp, Setminus, Sp, Call("diagonal", F.Id("X")), Dot));
    }

    private static Formula ExtensionalFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula current = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            Relation(F.Id("Kone"), x, y), Sp, Iff, Sp,
            Relation(F.Id("Ktwo"), x, y));
        Formula target = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            Relation(F.Id("Lone"), x, y), Sp, Iff, Sp,
            Relation(F.Id("Ltwo"), x, y));
        return Disp(Seq(
            Open, current, Close, Sp, Land, Sp, Open, target, Close,
            Sp, Rightarrow, Sp,
            Call("kernelResidual", F.Id("Kone"), F.Id("Lone")), Sp, Eq, Sp,
            Call("kernelResidual", F.Id("Ktwo"), F.Id("Ltwo")), Dot));
    }

    private static Formula JointTargetFormula()
    {
        Formula component = Call("L", F.Id("j"));
        return Disp(Seq(
            Call("kernelResidual", F.Id("K"), F.Id("joint")),
            Sp, Eq, Sp, Operatorname, Grp(F.Id("bigcup")), F.Id("j"), Sp,
            Call("kernelResidual", F.Id("K"), component), Dot));
    }

    private static Formula BundleJointTargetFormula()
    {
        Formula component = Call(
            "kernel", Call("atom", F.Id("b"), F.Id("i")));
        return Disp(Seq(
            Call("kernelResidual", F.Id("K"), Call("toKernel", F.Id("b"))),
            Sp, Eq, Sp, Operatorname, Grp(F.Id("bigcup")), F.Id("i"), Sp,
            Call("kernelResidual", F.Id("K"), component), Dot));
    }

    private static Formula FourRoleFormula()
    {
        Formula state = F.Id("x");
        Formula output = Seq(
            Open,
            Call("T", state), Comma, Sp,
            Call("Q", Call("F", state)), Comma, Sp,
            Call("decide", Call("A", state)), Comma, Sp,
            Call("decide", Seq(state, Sp, Eq, Sp, F.Id("a"))),
            Close);
        Formula readout = Seq(LambdaLower, Sp, state, Comma, Sp, output);
        Formula target = Call("cutKernel", readout);
        Formula roleUnion = Call("union",
            Call("union",
                Call("union",
                    Call("cutDefect", F.Id("q"), F.Id("T")),
                    Call("flowDefect", F.Id("q"), F.Id("F"), F.Id("Q"))),
                Call("admitDefect", F.Id("q"), F.Id("A"))),
            Call("anchorDefect", F.Id("q"), F.Id("a")));
        return Disp(Seq(
            Call("kernelResidual", Call("cutKernel", F.Id("q")), target),
            Sp, Eq, Sp, roleUnion, Dot));
    }

    private static Formula PostprocessingFormula() => Disp(Seq(
        Call("kernelResidual", F.Id("K"),
            Call("cutKernel", Call("compose", F.Id("h"), F.Id("f")))),
        Sp, Subseteq, Sp,
        Call("kernelResidual", F.Id("K"), Call("cutKernel", F.Id("f"))), Dot));
}
