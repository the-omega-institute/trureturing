using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeHierarchy;

internal sealed class GeneratedKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeHierarchy/GeneratedKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extensional catalog kernels form a finite bounded lattice inside the generated closure.",
        H("Generated-Kernel Lattice"),
        Blocks(
            Definition("generated-kernel-relation", "generatedKernelRelation",
                "Generated kernel relation",
                "The landed selected-catalog indistinguishability relation is packaged with its existing equivalence and decision proofs."),
            Definition("generated-kernel-setoid", "generatedKernelSetoid",
                "Extensional kernel setoid",
                "Selections are equivalent exactly when their relation truth tables agree at every ordered state pair."),
            Definition("generated-kernel-type", "GeneratedKernel",
                "Generated kernel",
                "The node carrier is the quotient of finite selections by exact relation equality."),
            Definition("generated-kernel-constructor", "generatedKernel",
                "Generated node",
                "A finite selection maps to its extensional generated-kernel class."),
            Definition("generated-kernel-relation-projection", "relation",
                "Node relation",
                "The exact relation descends through the quotient."),
            Theorem("relation-at-generated-kernel", "relation_generatedKernel",
                "Represented relation is catalog indistinguishability", RelationAtGenerated()),
            Definition("generated-kernel-boolean-relation", "relationB",
                "Boolean node relation",
                "The landed Boolean indistinguishability table descends through the extensional quotient."),
            Theorem("boolean-relation-reflection", "relationB_eq_true_iff",
                "Boolean relation reflection", BooleanReflection()),
            Definition("kernel-refines", "KernelRefines",
                "Kernel refinement",
                "A finer node relation is pointwise contained in a coarser node relation."),
            Theorem("generated-kernel-extensionality", "ext",
                "Generated-kernel extensionality", Extensionality()),
            Definition("escape-at-node", "escapeAt",
                "Escape at a node",
                "Escape is the finite set of off-diagonal pairs still related by the node kernel."),
            Definition("edge-capture", "edgeCapture",
                "Edge capture",
                "An edge captures the source escape pairs absent from its target."),
            Theorem("escape-at-generated-kernel", "escapeAt_generatedKernel_eq_escapePairs",
                "Node escape agrees with landed escape", EscapeBridge()),
            Theorem("generated-kernel-union", "generatedKernel_union",
                "Generator union computes meet", UnionMeet()),
            Theorem("generated-kernel-finite-lattice", "generatedKernel_finite_lattice",
                "The generated lattice is finite", FiniteLattice()),
            Theorem("top-is-empty-generated-kernel", "top_eq_generatedKernel_empty",
                "Top is the empty-selection kernel", TopFormula()),
            Theorem("bottom-is-full-generated-kernel", "bot_eq_generatedKernel_full",
                "Bottom is the full-catalog kernel", BottomFormula()),
            Theorem("inf-is-generated-kernel-union", "inf_eq_generatedKernel_union",
                "Meet is generator union", InfFormula()),
            Theorem("infimum-greatest-lower-bound", "isGLB_inf",
                "Meet has the greatest-lower-bound law", GlbFormula()),
            Theorem("supremum-least-upper-bound", "isLUB_sup",
                "Internal join has the least-upper-bound law", LubFormula()),
            Definition("generator-step", "GeneratorStep",
                "Generator step",
                "A step inserts one catalog generator into a representative and certifies downward refinement."),
            Definition("strict-generator-step", "StrictGeneratorStep",
                "Strict generator step",
                "A generator step is strict exactly when reverse refinement fails."),
            Definition("collapsed-addition", "CollapsedAddition",
                "Collapsed addition",
                "A collapsed addition is a certified generator step whose endpoints are one extensional node."),
            Theorem("generator-step-well-defined", "generatorStep_wellDefined",
                "Generator insertion respects extensional equality", StepWellDefined()),
            Theorem("escape-antitone-on-step", "escape_antitone_on_step",
                "Escape is antitone on generator steps", EscapeAntitone()),
            Theorem("strict-kernel-iff-nonempty-increment",
                "strict_kernel_iff_nonempty_increment",
                "Strict refinement exactly means nonempty capture", StrictNonempty()),
            Theorem("strict-kernel-iff-edge-capture-card-positive",
                "strict_kernel_iff_edgeCapture_card_pos",
                "Strict refinement exactly means positive capture count", StrictPositive()))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The certificate is proved from the extensional quotient and the landed catalog kernel laws."))),
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

    private static Formula C() => F.Id("C");
    private static Formula S() => F.Id("S");
    private static Formula T() => F.Id("T");
    private static Formula P() => F.Id("P");
    private static Formula Q() => F.Id("Q");
    private static Formula X() => F.Id("x");
    private static Formula Y() => F.Id("y");
    private static Formula I() => F.Id("i");
    private static Formula Kernel(Formula selected) => Call("generatedKernel", C(), selected);
    private static Formula Relation(Formula node) => Call("relation", node, X(), Y());
    private static Formula Refines(Formula finer, Formula coarser) =>
        Call("KernelRefines", finer, coarser);
    private static Formula Escape(Formula node) => Call("escapeAt", node);
    private static Formula Capture() => Call("edgeCapture", P(), Q());

    private static Formula RelationAtGenerated() => Seq(
        Relation(Kernel(S())), Sp, Iff, Sp, Call("indistinguishable", C(), S(), X(), Y()));

    private static Formula BooleanReflection() => Seq(
        Call("relationB", P(), X(), Y()), Sp, Eq, Sp, F.Id("true"), Sp, Iff, Sp,
        Relation(P()));

    private static Formula Extensionality() => new Formula.Logic(
        Seq(Forall, Sp, X(), Comma, Sp, Y(), Comma, Sp,
            Relation(P()), Sp, Iff, Sp, Relation(Q())),
        FormulaLogicOperator.Implies,
        Seq(P(), Sp, Eq, Sp, Q()));

    private static Formula EscapeBridge() => Seq(
        Escape(Kernel(S())), Sp, Eq, Sp, Call("escapePairs", C(), S()));

    private static Formula UnionMeet() => Seq(
        Kernel(Call("union", S(), T())), Sp, Eq, Sp,
        Call("inf", Kernel(S()), Kernel(T())));

    private static Formula FiniteLattice() => Call("Finite", Call("GeneratedKernel", C()));

    private static Formula TopFormula() => Seq(
        Call("top", Call("GeneratedKernel", C())), Sp, Eq, Sp,
        Kernel(Call("empty")));

    private static Formula BottomFormula() => Seq(
        Call("bottom", Call("GeneratedKernel", C())), Sp, Eq, Sp,
        Kernel(Call("fullIndexSet", C())));

    private static Formula InfFormula() => Seq(
        Call("inf", Kernel(S()), Kernel(T())), Sp, Eq, Sp,
        Kernel(Call("union", S(), T())));

    private static Formula GlbFormula() =>
        Call("IsGLB", Call("pair", P(), Q()), Call("inf", P(), Q()));

    private static Formula LubFormula() =>
        Call("IsLUB", Call("pair", P(), Q()), Call("sup", P(), Q()));

    private static Formula StepWellDefined() => new Formula.Logic(
        Seq(Kernel(S()), Sp, Eq, Sp, Kernel(T())),
        FormulaLogicOperator.Implies,
        Seq(Kernel(Call("insert", I(), S())), Sp, Eq, Sp,
            Kernel(Call("insert", I(), T()))));

    private static Formula EscapeAntitone() => new Formula.Logic(
        Call("GeneratorStep", C(), P(), Q(), I()),
        FormulaLogicOperator.Implies,
        Seq(Escape(Q()), Sp, Subseteq, Sp, Escape(P())));

    private static Formula StrictNonempty() => new Formula.Logic(
        Call("GeneratorStep", C(), P(), Q(), I()),
        FormulaLogicOperator.Implies,
        Seq(Neg, Refines(P(), Q()), Sp, Iff, Sp,
            Capture(), Sp, Ne, Sp, Call("empty")));

    private static Formula StrictPositive() => new Formula.Logic(
        Call("GeneratorStep", C(), P(), Q(), I()),
        FormulaLogicOperator.Implies,
        Seq(Neg, Refines(P(), Q()), Sp, Iff, Sp,
            D(0), Sp, Lt, Sp, Call("card", Capture())));
}
