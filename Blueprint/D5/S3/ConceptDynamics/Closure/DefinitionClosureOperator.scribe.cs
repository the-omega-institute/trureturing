using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Closure;

internal sealed class DefinitionClosureOperatorDocument : IScribeDocumentDefinition
{
    private const string Declaration = "D5/S3/ConceptDynamics/Closure/DefinitionClosureOperator.isClosed_definitionClosureOperator_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The repository semantic definition closure is bundled as Mathlib's "
            + "canonical closure operator.",
        H("Definition Closure as an Upstream Closure Operator"),
        Blocks(Describe.Lean(
            DescribeId.Create("definition-closure-operator"),
            DeclarationHandle.Create(Declaration),
            H("Upstream closed families are exactly semantically closed families"),
            StatementSource.FromAuthor(ClosedIffFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The repository already proves that DefinitionClosure is extensive, monotone, and literally idempotent on same-codomain readout families.")),
                Paragraph(Text(
                    "Those laws are bundled as Mathlib's ClosureOperator without introducing a second closure operation. Its closed-element carrier is therefore available to standard order-theoretic APIs.")),
                Paragraph(Text(
                    "A family is closed exactly when it contains every readout constant on the family's common observational kernel."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois")),
        ]));

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

    private static Formula ClosedIffFormula()
    {
        Formula family = F.Id("Gamma");
        return Disp(Seq(
            Forall, Sp, family, Comma, Sp,
            Call("IsClosed", Call("definitionClosureOperator"), family),
            Sp, Iff, Sp,
            Call("DefinitionClosure", family), Sp, Eq, Sp, family, Dot));
    }

}
