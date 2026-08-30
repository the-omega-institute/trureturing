using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GovernanceFixedPoint;

internal sealed class BlindGateUniqueDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GovernanceFixedPoint/BlindGateUnique.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Status blindness reduces the gate equation to pointwise equality with one fixed "
            + "context section, giving existence and uniqueness without finiteness assumptions.",
        H("Blind Gate Uniqueness"),
        Blocks(Describe.Lean(
            DescribeId.Create("status-blind-gate-has-unique-solution"),
            DeclarationHandle.Create(
                Prefix + "status_blind_gate_has_unique_solution"),
            H("Status-blind gates have unique solutions"),
            StatementSource.FromAuthor(UniqueGateFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Factoring the self-reading deriver through the blind lift supplies the "
                        + "context section as a solution.")),
                Paragraph(Text(
                    "Pointwise gate agreement then makes every other solution equal to that "
                        + "section by function extensionality."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula UniqueGateFormula()
    {
        Formula contextType = F.Id("Context");
        Formula entryType = F.Id("Entry");
        Formula statusType = F.Id("Status");
        Formula deriver = F.Id("D");
        Formula context = F.Id("context");
        Formula handwritten = F.Id("handwritten");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula statusMap = Arrow(entryType, statusType);
        Formula deriverType = Apply(
            F.Id("SelfReadingDeriver"), contextType, entryType, statusType);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(contextType, Comma, Sp, entryType, Comma, Sp, statusType), type),
                Comma),
            Seq(Typed(deriver, deriverType), Comma),
            Seq(
                Apply(F.Id("StatusBlind"), deriver), Sp, Rightarrow, Sp,
                Forall, Sp, Typed(context, contextType), Comma),
            Seq(
                Exists, Bang, Sp, Typed(handwritten, statusMap), Comma, Sp,
                Apply(
                    F.Id("Gate"), handwritten,
                    Apply(deriver, context, handwritten)), Dot),
        ]));
    }
}
