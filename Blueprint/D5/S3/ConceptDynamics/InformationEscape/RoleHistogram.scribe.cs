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
                DescribeId.Create("without-kernel"), Handle("Catalog.withoutKernel"),
                H("Leave-one-out catalog kernel"),
                StatementSource.FromAuthor(Disp(Eq(
                    Call("relation", Call("withoutKernel", C, I)),
                    Call("indistinguishable", C, Call("without", C, I))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The other theorem bundles form one decidable equivalence kernel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("role-histogram"), Handle("Catalog.roleHistogram"),
                H("Residual role-signature multiplicity"),
                StatementSource.FromAuthor(Disp(Eq(Call("roleHistogram", C, I, S),
                    Call("residualSignatureHistogram", Call("withoutKernel", C, I), S)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each bucket counts an exact four-role residual signature."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unique-capture-role-signature-nonzero"),
                Handle("Catalog.uniqueCapture_roleSignature_nonzero"),
                H("Unique capture has nonzero role signature"),
                StatementSource.FromAuthor(Disp(Implies(Call("Member", P, Call("uniqueCapturePairs", C, I)),
                    Call("NotEqual", Call("residualRoleSignature", C, I, P), Z)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The frozen residual-signature bridge turns unique capture into nonzero role coverage."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("role-histogram-sum-eq-unique-capture-count"),
                Handle("Catalog.roleHistogram_sum_eq_uniqueCaptureCount"),
                H("Nonzero buckets sum to unique capture"),
                StatementSource.FromAuthor(Disp(Eq(Call("sumNonzero", Call("roleHistogram", C, I)),
                    Call("uniqueCaptureCount", C, I)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fiberwise finite counting identifies the nonzero buckets with the residual finset."))),
                DescribeRole.Theorem))));

    private static readonly Formula C = F.Id("C");
    private static readonly Formula I = F.Id("i");
    private static readonly Formula P = F.Id("p");
    private static readonly Formula S = F.Id("s");
    private static readonly Formula Z = F.Id("z");

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
}
