using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class LiteralNegationTriggerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Two is not below two.",
        H("Literal Negation Trigger"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-refutes-below-two"),
                DeclarationHandle.Create("D5/S3/PrimeForms/LiteralNegationTrigger.result"),
                H("Two refutes the bound"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Open, Forall, F.Id("n"), Sp, Colon, Sp,
                    Operatorname, Grp(F.Id("Nat")), Sp, F.Id("n"), Lt, D(2), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The number two is not below two."))),
                DescribeRole.Theorem))));
}
