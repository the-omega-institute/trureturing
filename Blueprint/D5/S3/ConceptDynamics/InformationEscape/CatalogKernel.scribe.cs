using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class CatalogKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/CatalogKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite theorem selections compute executable and structural joint kernels.",
        H("Catalog Joint Kernels"),
        Blocks(
            DefinitionNode("catalog-indistinguishable", "indistinguishable",
                "Selected-catalog indistinguishability",
                "Two states are indistinguishable when every selected theorem bundle agrees."),
            DefinitionNode("catalog-indistinguishable-boolean", "indistinguishableB",
                "Boolean selected-catalog indistinguishability",
                "A finite conjunction of bundle Boolean tests computes indistinguishability."),
            TheoremNode("catalog-indistinguishable-reflection", "indistinguishableB_eq_true_iff",
                "Boolean catalog reflection", ReflectionFormula(),
                "The finite Boolean conjunction is true exactly when all selected theorem bundles agree."),
            TheoremNode("catalog-indistinguishable-forall", "indistinguishable_iff_forall",
                "Catalog indistinguishability is selected agreement", ForallFormula(),
                "Indistinguishability over a finite selection holds exactly when every selected theorem bundle agrees."),
            TheoremNode("catalog-indistinguishable-equivalence", "indistinguishable_equivalence",
                "Catalog indistinguishability is an equivalence", EquivalenceFormula(),
                "Equivalence is inherited coordinatewise from the selected primitive bundles."),
            DefinitionNode("catalog-joint-kernel", "jointKernel", "Catalog joint kernel",
                "The structural kernel is the set of pairs agreeing for every theorem in a Set-level selection."),
            TheoremNode("catalog-canonical-joint-kernel", "jointKernel_eq_canonical_jointKernel",
                "Catalog kernels use the canonical joint kernel", CanonicalBridgeFormula(),
                "Quotient-CUT normalization identifies the catalog relation with the repository's dependent jointKernel."),
            TheoremNode("catalog-joint-kernel-antitone", "jointKernel_antitone",
                "Joint kernels are antitone", AntitoneFormula(),
                "Every agreement for a larger theorem selection remains an agreement for a smaller selection."),
            TheoremNode("catalog-joint-kernel-insert", "jointKernel_insert",
                "Insertion intersects joint kernels", KernelInsertFormula(),
                "Adding one theorem intersects the old common kernel with that theorem bundle's kernel."),
            TheoremNode("catalog-finite-indistinguishable-monotone", "indistinguishable_mono",
                "Finite indistinguishability is antitone", FiniteMonoFormula(),
                "Agreement for a larger finite selection restricts to every smaller selection."),
            TheoremNode("catalog-finite-indistinguishable-insert", "indistinguishable_insert_iff",
                "Finite insertion adds one conjunct", FiniteInsertFormula(),
                "Indistinguishability after insertion is exactly the new bundle agreement and the old relation."))));

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

    private static Formula Agreement(Formula selection) =>
        Call("indistinguishable", F.Id("catalog"), selection, F.Id("left"), F.Id("right"));

    private static Formula BundleAgreement() =>
        Call("agrees", Call("primitives", Call("theoremAt", F.Id("catalog"), F.Id("i"))),
            F.Id("left"), F.Id("right"));

    private static Formula ReflectionFormula() => Disp(Seq(
        Call("indistinguishableB", F.Id("catalog"), F.Id("S"), F.Id("left"), F.Id("right")),
        Sp, Eq, Sp, F.Id("true"), Sp, Iff, Sp, Agreement(F.Id("S")), Dot));

    private static Formula ForallFormula() => Disp(Seq(
        Agreement(F.Id("S")), Sp, Iff, Sp,
        Forall, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp, BundleAgreement(), Dot));

    private static Formula EquivalenceFormula() => Disp(Seq(
        Call("Equivalence", Seq(
            LambdaLower, Sp, F.Id("left"), Comma, Sp, F.Id("right"), Comma, Sp,
            Agreement(F.Id("S")))), Dot));

    private static Formula CanonicalBridgeFormula()
    {
        Formula quotientFamily = Seq(
            LambdaLower, Sp, F.Id("i"), Colon, Sp, F.Id("S"), Comma, Sp,
            Call("quotientCut", Call("toKernel",
                Call("primitives", Call("theoremAt", F.Id("catalog"), F.Id("i"))))));
        return Disp(Seq(
            Call("jointKernel", F.Id("catalog"), F.Id("S")), Sp, Eq, Sp,
            Call("jointKernel", quotientFamily), Dot));
    }

    private static Formula AntitoneFormula() => Disp(Seq(
        F.Id("S"), Sp, Subseteq, Sp, F.Id("T"), Sp, Rightarrow, Sp,
        Call("jointKernel", F.Id("catalog"), F.Id("T")), Sp, Subseteq, Sp,
        Call("jointKernel", F.Id("catalog"), F.Id("S")), Dot));

    private static Formula KernelInsertFormula()
    {
        Formula pair = F.Id("p");
        Formula agreementSet = Seq(
            OpenBrace, pair, Sp, Mid, Sp,
            Call("agrees",
                Call("primitives", Call("theoremAt", F.Id("catalog"), F.Id("i"))),
                Call("fst", pair), Call("snd", pair)),
            CloseBrace);
        return Disp(Seq(
            Call("jointKernel", F.Id("catalog"), Call("insert", F.Id("i"), F.Id("S"))),
            Sp, Eq, Sp,
            Call("intersection", Call("jointKernel", F.Id("catalog"), F.Id("S")), agreementSet),
            Dot));
    }

    private static Formula FiniteMonoFormula() => Disp(Seq(
        F.Id("S"), Sp, Subseteq, Sp, F.Id("T"), Sp, Rightarrow, Sp,
        Agreement(F.Id("T")), Sp, Rightarrow, Sp, Agreement(F.Id("S")), Dot));

    private static Formula FiniteInsertFormula() => Disp(Seq(
        Agreement(Call("insert", F.Id("i"), F.Id("S"))), Sp, Iff, Sp,
        BundleAgreement(), Sp, Land, Sp, Agreement(F.Id("S")), Dot));
}
