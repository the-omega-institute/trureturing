using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PrimitiveResidualBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Catalog unique capture is the canonical CIRPT primitive-kernel residual.",
        H("Primitive Residual Bridge"),
        Blocks(
            Thm("unique-capture-pairs-eq-kernel-residual", "Catalog.uniqueCapturePairs_eq_kernelResidual",
                "Unique capture is leave-one-out kernel residual",
                Eq(Call("uniqueCapturePairs", C, I),
                    Call("kernelResidual", Call("withoutKernel", C, I), Call("primitiveKernel", C, I)))),
            Thm("theorem-gain-depends-only-on-primitive-kernel",
                "Catalog.theoremGain_depends_only_on_primitive_kernel",
                "Theorem gain depends only on primitive kernels",
                Implies(Call("PointwiseKernelEqual", C, U),
                    Eq(Call("theoremGainRate", Call("withTheoremAt", C, U), I),
                        Call("theoremGainRate", C, I)))),
            Thm("closed-truth-cut-kernel-universal", "Catalog.closed_truth_cut_kernel_universal",
                "Closed truth has universal kernel",
                Eq(Call("relation", Call("cutKernel", Call("constantTrue", X))),
                    Call("UniversalRelation", X))),
            Thm("closed-truth-unique-capture-count-zero",
                "Catalog.closed_truth_uniqueCaptureCount_zero",
                "Closed truth has zero unique capture",
                Implies(Call("ClosedTruthKernel", C, I),
                    Eq(Call("uniqueCaptureCount", C, I), D(0)))),
            Thm("theorem-at-proof-irrelevant", "Catalog.theoremAt_proof_irrelevant",
                "Proof certificates do not enter unique capture",
                Implies(Call("PrimitiveFamiliesEqual", C, U),
                    Eq(Call("uniqueCaptureCount", Call("withTheoremAt", C, U), I),
                        Call("uniqueCaptureCount", C, I)))))));

    private static readonly Formula C = F.Id("C");
    private static readonly Formula I = F.Id("i");
    private static readonly Formula U = F.Id("U");
    private static readonly Formula X = F.Id("X");

    private static DocumentBlock Thm(
        string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/InformationEscape/PrimitiveResidualBridge." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The proof specializes the frozen CIRPT and finite information-escape kernels."))),
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

    private static Formula Eq(Formula left, Formula right) => Seq(left, Sp, F.Eq, Sp, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
