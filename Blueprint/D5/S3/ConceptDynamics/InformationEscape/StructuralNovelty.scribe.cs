using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class StructuralNoveltyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/StructuralNovelty.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite escape reduction is canonical strict kernel novelty of quotient CUTs.",
        H("Structural Escape Novelty"),
        Blocks(
            Definition("structurally-lowers-escape", "StructurallyLowersEscape",
                H("Structural escape reduction"), StructuralDefinition()),
            Theorem("structurally-lowers-escape-iff-lowers-escape",
                "structurallyLowersEscape_iff_lowersEscape",
                H("Structural and exact reduction agree"), StructuralCriterion()),
            Definition("semantic-closure-without", "semanticClosureWithout",
                H("Leave-one-out kernel closure"), ClosureDefinition()),
            Definition("quotient-output", "QuotientOutput",
                H("Tagged quotient output"), QuotientOutputDefinition()),
            Definition("tagged-quotient-cut", "taggedQuotientCut",
                H("Tagged canonical quotient CUT"), TaggedCutDefinition()),
            Definition("quotient-cuts-without", "quotientCutsWithout",
                H("Homogeneous leave-one-out CUT family"), CutFamilyDefinition()),
            Theorem("tagged-quotient-cut-mem-semantic-closure-iff",
                "taggedQuotientCut_mem_semanticClosure_iff",
                H("Catalog and canonical closures agree"), ClosureBridge()),
            Theorem("lowers-escape-iff-strict-kernel-novelty",
                "lowersEscape_iff_strict_kernel_novelty",
                H("Canonical strict novelty criterion"), StrictNovelty()),
            Theorem("lowers-escape-iff-not-mem-semantic-closure-without",
                "lowersEscape_iff_not_mem_semanticClosureWithout",
                H("Semantic closure criterion"), ClosureCriterion()),
            Theorem("lowers-escape-false-of-recoverable",
                "lowersEscape_false_of_recoverable",
                H("Recoverability prevents reduction"), RecoverableZero()),
            Theorem("same-kernel-both-zero", "same_kernel_both_zero",
                H("Duplicate kernels have zero capture"), SameKernelZero()),
            Theorem("constant-kernel-zero", "constant_kernel_zero",
                H("Constant kernels have zero capture"), ConstantKernelZero()))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, Heading title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), title,
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "This definition packages the catalog kernel or its canonical quotient CUT."))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, Heading title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), title,
            StatementSource.FromAuthor(Disp(Seq(formula, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The proof preserves bundle kernels and reuses the canonical semantic closure."))),
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

    private static Formula Catalog() => F.Id("C");
    private static Formula Index() => F.Id("i");
    private static Formula Other() => F.Id("j");
    private static Formula Cut(Formula index) =>
        Call("taggedQuotientCut", Catalog(), index);
    private static Formula CutFamily() => Call("quotientCutsWithout", Catalog(), Index());
    private static Formula Closure() => Call("semanticClosureWithout", Catalog(), Index());
    private static Formula BundleKernel(Formula index) =>
        Call("toKernel", Call("primitives", Call("theoremAt", Catalog(), index)));
    private static Formula Agrees(Formula index) =>
        Call("agrees", Call("theoremAt", Catalog(), index), F.Id("x"), F.Id("y"));
    private static Formula CatalogKernel(Formula selected) =>
        Call("catalogJointKernel", Catalog(), selected);
    private static Formula CanonicalKernel(Formula family) =>
        Call("jointKernel", Seq(LambdaLower, Sp, F.Id("d"), Colon, Sp, family,
            Comma, Sp, Call("readout", F.Id("d"))));
    private static Formula Nondegenerate() => Call("Nondegenerate", F.Id("A"));
    private static Formula Lowers() => Call("LowersEscape", Catalog(), Index());

    private static Formula WithoutSet() => Call("setOf", Seq(
        Other(), Sp, Mid, Sp, Other(), Sp, Neq, Sp, Index()));

    private static Formula StructuralDefinition() => Seq(
        Call("StructurallyLowersEscape", Catalog(), Index()), Sp, Leftrightarrow, Sp,
        Call("StrictSubset", CatalogKernel(Call("univ")), CatalogKernel(WithoutSet())));

    private static Formula StructuralCriterion() => new Formula.Logic(
        Nondegenerate(), FormulaLogicOperator.Implies,
        Seq(Call("StructurallyLowersEscape", Catalog(), Index()), Sp,
            Leftrightarrow, Sp, Lowers()));

    private static Formula ClosureDefinition() => Seq(
        Closure(), Sp, Eq, Sp, Call("setOf", Seq(F.Id("K"), Sp, Mid, Sp,
            Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
            Open, Forall, Sp, Other(), Comma, Sp, Other(), Sp, Neq, Sp, Index(),
            Sp, Rightarrow, Sp, Agrees(Other()), Close, Sp, Rightarrow, Sp,
            Call("related", F.Id("K"), F.Id("x"), F.Id("y")))));

    private static Formula QuotientOutputDefinition() => Seq(
        Call("QuotientOutput", Catalog()), Sp, Eq, Sp,
        Call("Sigma", Other(),
            Call("Quotient", BundleKernel(Other()))));

    private static Formula TaggedCutDefinition() => Seq(
        Cut(Index()), Sp, Eq, Sp, LambdaLower, Sp, F.Id("x"), Comma, Sp,
        Call("tag", Index(), Call("quotientCut", BundleKernel(Index()), F.Id("x"))));

    private static Formula CutFamilyDefinition() => Seq(
        CutFamily(), Sp, Eq, Sp,
        Call("image", Seq(LambdaLower, Sp, Other(), Comma, Sp, Cut(Other())),
            WithoutSet()));

    private static Formula ClosureBridge() => Seq(
        Cut(Index()), Sp, InMacro, Sp, Call("SemanticClosure", CutFamily()),
        Sp, Leftrightarrow, Sp, BundleKernel(Index()), Sp, InMacro, Sp, Closure());

    private static Formula StrictNovelty() => new Formula.Logic(
        Nondegenerate(), FormulaLogicOperator.Implies,
        Seq(Lowers(), Sp, Leftrightarrow, Sp,
            Call("StrictSubset",
                CanonicalKernel(Call("insert", Cut(Index()), CutFamily())),
                CanonicalKernel(CutFamily()))));

    private static Formula ClosureCriterion() => new Formula.Logic(
        Nondegenerate(), FormulaLogicOperator.Implies,
        Seq(Lowers(), Sp, Leftrightarrow, Sp, Neg, Open,
            BundleKernel(Index()), Sp, InMacro, Sp, Closure(), Close));

    private static Formula Recoverability() => Seq(
        Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Open, Forall, Sp, Other(), Comma, Sp, Other(), Sp, Neq, Sp, Index(),
        Sp, Rightarrow, Sp, Agrees(Other()), Close, Sp, Rightarrow, Sp,
        Agrees(Index()));

    private static Formula RecoverableZero() => new Formula.Logic(
        Recoverability(), FormulaLogicOperator.Implies, Seq(Neg, Lowers()));

    private static Formula SameKernelZero() => new Formula.Logic(
        Seq(F.Id("i"), Sp, Neq, Sp, F.Id("j"), Sp, Land, Sp,
            Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
            Agrees(F.Id("i")), Sp, Leftrightarrow, Sp, Agrees(F.Id("j")), Close),
        FormulaLogicOperator.Implies,
        Seq(Call("uniqueCaptureCount", Catalog(), F.Id("i")), Sp, Eq, Sp, D(0),
            Sp, Land, Sp,
            Call("uniqueCaptureCount", Catalog(), F.Id("j")), Sp, Eq, Sp, D(0)));

    private static Formula ConstantKernelZero() => new Formula.Logic(
        Seq(Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
            Agrees(Index())),
        FormulaLogicOperator.Implies,
        Seq(Call("uniqueCaptureCount", Catalog(), Index()), Sp, Eq, Sp, D(0)));
}
