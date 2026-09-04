using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CIRPT.InformationEscape;

internal sealed class QuotientCutNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CIRPT/InformationEscape/QuotientCutNormalForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A decidable kernel supplies a computable quotient whose projection is a canonical CUT.",
        H("Quotient CUT Normal Form"),
        Blocks(
            DefinitionNode("kernel-to-setoid", "toSetoid",
                "Kernel setoid",
                "The kernel equivalence proof equips its relation with the canonical Setoid interface."),
            DefinitionNode("kernel-quotient-cut", "quotientCut",
                "Canonical quotient CUT",
                "Each state is sent to its equivalence class under the kernel relation."),
            DefinitionNode("kernel-quotient-decidable-equality",
                "instDecidableEqQuotient", "Decidable quotient equality",
                "Equality of quotient representatives is decided by the underlying kernel decision."),
            TheoremNode("quotient-cut-kernel-normal-form",
                "quotient_cut_kernel_normal_form", "Quotient CUT kernel normal form",
                NormalFormFormula(),
                "Mathlib quotient equality identifies precisely the pairs related by the source kernel."),
            TheoremNode("quotient-cut-constructor-recovers-relation",
                "cutKernel_quotientCut_relation_iff", "The CUT constructor recovers the kernel",
                CutRecoveryFormula(),
                "The decidable quotient equality makes the generic CUT constructor available without changing the relation."))));

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

    private static Formula NormalFormFormula() => Disp(Seq(
        Forall, Sp, F.Id("K"), Colon, Sp, Call("DecidableKernel", F.Id("X")), Comma, Sp,
        Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, F.Id("X"), Comma, Sp,
        Call("relation", F.Id("K"), F.Id("x"), F.Id("y")), Sp, Iff, Sp,
        Call("quotientCut", F.Id("K"), F.Id("x")), Sp, Eq, Sp,
        Call("quotientCut", F.Id("K"), F.Id("y")), Dot));

    private static Formula CutRecoveryFormula() => Disp(Seq(
        Forall, Sp, F.Id("K"), Colon, Sp, Call("DecidableKernel", F.Id("X")), Comma, Sp,
        Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, F.Id("X"), Comma, Sp,
        Call("relation", Call("cutKernel", Call("quotientCut", F.Id("K"))),
            F.Id("x"), F.Id("y")), Sp, Iff, Sp,
        Call("relation", F.Id("K"), F.Id("x"), F.Id("y")), Dot));
}
