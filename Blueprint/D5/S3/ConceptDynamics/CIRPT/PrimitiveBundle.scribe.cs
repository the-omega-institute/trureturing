using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CIRPT;

internal sealed class PrimitiveBundleDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CIRPT/PrimitiveBundle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite role-labelled primitive families compute one joint observational kernel.",
        H("CIRPT Primitive Bundles"),
        Blocks(
            DefinitionNode("primitive-atom", "PrimitiveAtom", "Primitive atom",
                "An atom pairs one CIRPT role label with a decidable kernel on the state space."),
            DefinitionNode("primitive-bundle", "PrimitiveBundle", "Primitive bundle",
                "A bundle stores a finite decidable index type and one primitive atom per index."),
            DefinitionNode("bundle-agrees", "agrees", "Bundle agreement",
                "Two states agree when every indexed atom kernel relates them."),
            DefinitionNode("bundle-agrees-boolean", "agreesB",
                "Boolean bundle agreement",
                "A commutative finite-set fold computes the executable Boolean conjunction."),
            DefinitionNode("bundle-to-kernel", "toKernel", "Joint bundle kernel",
                "Logical agreement and its Boolean reflection are packaged as a decidable kernel."),
            DefinitionNode("bundle-nonempty", "Nonempty", "Nonempty bundle",
                "Bundle nonemptiness is inhabitation of the packed index type."),
            DefinitionNode("packed-observer", "PackedObserver", "Packed observer",
                "A readout packages its codomain, decidable equality, and observation function."),
            DefinitionNode("packed-observer-to-atom", "toPrimitiveAtom",
                "Packed observer atom",
                "A packed readout becomes a CUT kernel while retaining the supplied role label."),
            TheoremNode("boolean-agreement-reflection", "agreesB_eq_true_iff",
                "Boolean agreement reflects logical agreement", AgreementReflectionFormula(),
                "Boolean conjunction over the finite universal set is true exactly when every atom relates the pair."),
            TheoremNode("bundle-agreement-equivalence", "agrees_equivalence",
                "Bundle agreement is an equivalence", AgreementEquivalenceFormula(),
                "Reflexivity, symmetry, and transitivity are inherited coordinatewise from every atom kernel."),
            TheoremNode("primitive-bundle-joint-kernel",
                "primitive_bundle_joint_kernel", "Bundle joint-kernel law",
                JointKernelFormula(),
                "The set of agreeing pairs is exactly the indexed intersection of atom collision sets."),
            TheoremNode("bundle-canonical-joint-kernel",
                "bundle_agrees_iff_jointKernel_quotientCuts",
                "Bundle agreement is the canonical quotient-CUT joint kernel",
                QuotientBridgeFormula(),
                "Normalizing each atom through its quotient CUT identifies bundle agreement with the repository jointKernel."),
            TheoremNode("primitive-bundle-kernel-invariance",
                "primitive_bundle_kernel_invariance",
                "Joint-kernel equality preserves finite computation", InvarianceFormula(),
                "Pointwise equality of packaged relations preserves both logical agreement and its computed Boolean result."),
            TheoremNode("packed-observer-atom-reflection",
                "toPrimitiveAtom_relation_iff", "Packed observer reflection",
                ObserverReflectionFormula(),
                "The generated atom kernel relates precisely the states with equal observed outputs."))));

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

    private static Formula AgreementReflectionFormula() => Disp(Seq(
        Forall, Sp, F.Id("b"), Comma, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("agreesB", F.Id("b"), F.Id("x"), F.Id("y")), Sp, Eq, Sp, F.Id("true"),
        Sp, Iff, Sp, Call("agrees", F.Id("b"), F.Id("x"), F.Id("y")), Dot));

    private static Formula AgreementEquivalenceFormula() => Disp(Seq(
        Forall, Sp, F.Id("b"), Colon, Sp, Call("PrimitiveBundle", F.Id("X")), Comma, Sp,
        Call("Equivalence", Call("agrees", F.Id("b"))), Dot));

    private static Formula JointKernelFormula()
    {
        Formula pair = Seq(Open, F.Id("x"), Comma, F.Id("y"), Close);
        Formula intersection = Seq(Operatorname, Grp(F.Id("bigcap")), F.Id("i"));
        return Disp(Seq(
            OpenBrace, pair, Sp, Mid, Sp,
            Call("agrees", F.Id("b"), F.Id("x"), F.Id("y")), CloseBrace,
            Sp, Eq, Sp, intersection, Sp,
            OpenBrace, pair, Sp, Mid, Sp,
            Call("relation", Call("kernel", Call("atom", F.Id("b"), F.Id("i"))),
                F.Id("x"), F.Id("y")), CloseBrace, Dot));
    }

    private static Formula QuotientBridgeFormula()
    {
        Formula pair = Seq(Open, F.Id("x"), Comma, F.Id("y"), Close);
        Formula quotientCuts = Seq(
            LambdaLower, Sp, F.Id("i"), Comma, Sp,
            Call("quotientCut", Call("kernel", Call("atom", F.Id("b"), F.Id("i")))));
        return Disp(Seq(
            Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
            Call("agrees", F.Id("b"), F.Id("x"), F.Id("y")), Sp, Iff, Sp,
            pair, Sp, InMacro, Sp, Call("jointKernel", quotientCuts), Dot));
    }

    private static Formula InvarianceFormula() => Disp(Seq(
        Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("relation", Call("toKernel", F.Id("b")), F.Id("x"), F.Id("y")), Sp, Iff, Sp,
        Call("relation", Call("toKernel", F.Id("c")), F.Id("x"), F.Id("y")), Close,
        Sp, Rightarrow, Sp, Open,
        Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("agrees", F.Id("b"), F.Id("x"), F.Id("y")), Sp, Iff, Sp,
        Call("agrees", F.Id("c"), F.Id("x"), F.Id("y")), Close, Sp, Land, RowBreak,
        Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("agreesB", F.Id("b"), F.Id("x"), F.Id("y")), Sp, Eq, Sp,
        Call("agreesB", F.Id("c"), F.Id("x"), F.Id("y")), Close, Close, Dot));

    private static Formula ObserverReflectionFormula() => Disp(Seq(
        Forall, Sp, F.Id("axis"), Comma, Sp, F.Id("obs"), Comma, Sp,
        F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("relation", Call("kernel", Call("toPrimitiveAtom", F.Id("axis"), F.Id("obs"))),
            F.Id("x"), F.Id("y")), Sp, Iff, Sp,
        Call("observe", F.Id("obs"), F.Id("x")), Sp, Eq, Sp,
        Call("observe", F.Id("obs"), F.Id("y")), Dot));
}
