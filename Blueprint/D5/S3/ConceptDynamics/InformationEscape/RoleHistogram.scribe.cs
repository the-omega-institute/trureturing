using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class RoleHistogramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leave-one-out residual is partitioned by four-bit CIRPT role signatures.",
        H("Unique Capture Role Histogram"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("without-kernel"), Handle("withoutKernel"),
                H("Leave-one-out catalog kernel"),
                StatementSource.FromAuthor(Disp(Eq(
                    Call("relation", Call("withoutKernel", C, I)),
                    Call("indistinguishable", C, Call("without", C, I))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The other theorem bundles form one decidable equivalence kernel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("role-histogram"), Handle("roleHistogram"),
                H("Residual role-signature multiplicity"),
                StatementSource.FromAuthor(Disp(Eq(Call("roleHistogram", C, I, S),
                    Call("residualSignatureHistogram",
                        Call("primitives", Call("theoremAt", C, I)),
                        Call("withoutKernel", C, I), S)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each bucket counts an exact four-role residual signature."))),
                DescribeRole.Definition),
            Thm("unique-capture-pairs-eq-kernel-residual", "uniqueCapturePairs_eq_kernelResidual",
                "Unique capture is leave-one-out kernel residual",
                Eq(Call("uniqueCapturePairs", C, I),
                    Call("kernelResidual", Call("withoutKernel", C, I),
                        Call("toKernel", Call("primitives", Call("theoremAt", C, I)))))),
            Describe.Lean(
                DescribeId.Create("unique-capture-role-signature-nonzero"),
                Handle("uniqueCapture_roleSignature_nonzero"),
                H("Unique capture has nonzero role signature"),
                StatementSource.FromAuthor(Disp(Implies(
                    Call("Member", P, Call("uniqueCapturePairs", C, I)),
                    Call("NotEqual",
                        Call("residualRoleSignature",
                            Call("primitives", Call("theoremAt", C, I)),
                            Call("withoutKernel", C, I), Call("fst", P), Call("snd", P)),
                        ConstantFalse)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The frozen residual-signature bridge turns unique capture into nonzero role coverage."))),
                DescribeRole.Theorem),
            Thm("unique-capture-pairs-eq-bi-union-role-fibers",
                "uniqueCapturePairs_eq_biUnion_roleFibers",
                "Unique capture is the union of its four active-role fibers",
                Eq(Call("uniqueCapturePairs", C, I),
                    Call("biUnion", Call("univ", F.Id("Fin4")),
                        Seq(Open, K, Sp, Mapsto, Sp,
                            Call("filter", Call("uniqueCapturePairs", C, I),
                                Seq(Open, P, Sp, Mapsto, Sp,
                                    Eq(Call("residualRoleSignature",
                                            Call("primitives", Call("theoremAt", C, I)),
                                            Call("withoutKernel", C, I),
                                            Call("fst", P), Call("snd", P), K),
                                        F.Id("true")), Close)), Close)))),
            Describe.Lean(
                DescribeId.Create("role-histogram-sum-eq-unique-capture-count"),
                Handle("roleHistogram_sum_eq_uniqueCaptureCount"),
                H("Nonzero buckets sum to unique capture"),
                StatementSource.FromAuthor(Disp(Eq(
                    Call("sum", Seq(S, Comma, Sp, Call("NotEqual", S, ConstantFalse)),
                        Call("roleHistogram", C, I, S)),
                    Call("uniqueCaptureCount", C, I)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fiberwise finite counting identifies the nonzero buckets with the residual finset."))),
                DescribeRole.Theorem),
            Thm("theorem-gain-depends-only-on-primitive-kernel",
                "theoremGain_depends_only_on_primitive_kernel",
                "Theorem gain depends only on primitive kernels",
                Implies(KernelEquivalent(C, U),
                    Eq(Call("theoremGainRate", Call("withTheoremAt", C, U), I),
                        Call("theoremGainRate", C, I)))),
            Thm("closed-truth-unique-capture-count-zero",
                "closed_truth_uniqueCaptureCount_zero",
                "Closed truth has zero unique capture",
                Implies(Seq(Open, Forall, Sp, X, Comma, Sp, Y, Comma, Sp,
                        Call("relation", Call("toKernel",
                                Call("primitives", Call("theoremAt", C, I))), X, Y),
                        Sp, Leftrightarrow, Sp,
                        Call("relation", Call("cutKernel", ConstantTrue), X, Y), Close),
                    Eq(Call("uniqueCaptureCount", C, I), D(0)))),
            Thm("theorem-at-proof-irrelevant", "theoremAt_proof_irrelevant",
                "Proof certificates do not enter unique capture",
                Implies(Seq(Open, Forall, Sp, N, Comma, Sp,
                        Eq(Call("primitives", Call("theoremAt", C, N)),
                            Call("primitives", Call("apply", U, N))), Close),
                    Eq(Call("uniqueCaptureCount", Call("withTheoremAt", C, U), I),
                        Call("uniqueCaptureCount", C, I)))),
            Thm("closed-truth-cut-kernel-universal", "closed_truth_cut_kernel_universal",
                "Closed truth has universal kernel",
                Eq(Call("relation", Call("cutKernel", ConstantTrue)),
                    Seq(Open, X, Comma, Sp, Y, Sp, Mapsto, Sp, F.Id("True"), Close))))));

    private static readonly Formula C = F.Id("C");
    private static readonly Formula I = F.Id("i");
    private static readonly Formula K = F.Id("k");
    private static readonly Formula N = F.Id("j");
    private static readonly Formula P = F.Id("p");
    private static readonly Formula S = F.Id("s");
    private static readonly Formula U = F.Id("U");
    private static readonly Formula X = F.Id("x");
    private static readonly Formula Y = F.Id("y");

    private static Formula ConstantFalse =>
        Seq(Open, K, Sp, Mapsto, Sp, F.Id("false"), Close);

    private static Formula ConstantTrue =>
        Seq(Open, X, Sp, Mapsto, Sp, F.Id("true"), Close);

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/RoleHistogram." + declaration);

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

    private static Formula KernelEquivalent(Formula catalog, Formula units) =>
        Seq(Open, Forall, Sp, N, Comma, Sp, X, Comma, Sp, Y, Comma, Sp,
            Call("relation", Call("toKernel",
                Call("primitives", Call("theoremAt", catalog, N))), X, Y),
            Sp, Leftrightarrow, Sp,
            Call("relation", Call("toKernel",
                Call("primitives", Call("apply", units, N))), X, Y), Close);

    private static DocumentBlock Thm(
        string id, string declaration, string title, Formula formula) =>
        Describe.Lean(
            DescribeId.Create(id), Handle(declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The proof uses the finite residual and exact-count APIs."))),
            DescribeRole.Theorem);
}
