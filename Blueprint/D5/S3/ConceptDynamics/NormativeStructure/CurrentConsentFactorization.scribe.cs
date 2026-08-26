using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class CurrentConsentFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Non-factorization of current consent rules out exact systems using only history.",
        H("Current Consent Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("current-consent-not-history-only"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/NormativeStructure/CurrentConsentFactorization."
                        + "current_consent_not_history_only"),
                H("Current consent cannot be recovered from history alone"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state carrier, history readout, and current-consent readout are "
                            + "independent source primitives on the canonical Concept carrier.")),
                    Paragraph(Text(
                        "The premise states publicly that current consent does not refine through "
                            + "history. The conclusion quantifies a history-factoring system and "
                            + "requires exact equality with current consent, then rules out that "
                            + "pair.")),
                    Paragraph(Text(
                        "The proof composes the proposed system factor with its exact-response "
                            + "equality, contradicting the non-factorization premise. No object is "
                            + "defined from the nonexistence target.")),
                    Paragraph(Text(
                        "The search found no exact frozen current-consent theorem; the pinned "
                            + "Refines factorization relation is applied directly."))),
                DescribeRole.Theorem))));

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

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula historyType = F.Id("H");
        Formula history = F.Id("Hnow");
        Formula current = F.Id("Cnow");
        Formula system = F.Id("J");
        Formula boolType = F.Id("Bool");
        Formula readout = Seq(state, Sp, To, Sp, boolType);
        Formula historyReadout = Seq(state, Sp, To, Sp, historyType);
        Formula nonFactor = Seq(
            Neg, Sp, Call("Refines", current, history));
        Formula exactSystem = Seq(
            Exists, Sp, system, Comma, Sp, system, Colon, Sp, readout, Comma, Sp,
            Call("Refines", system, history), Sp, Land, Sp,
            system, Sp, Eq, Sp, current);
        return Disp(Seq(
            Forall, Sp, state, Sp, Colon, Sp, F.Id("Type"), Comma, Sp,
            historyType, Sp, Colon, Sp, F.Id("Type"), Comma, RowBreak, Grp(),
            history, Colon, Sp, historyReadout, Comma, Sp,
            current, Colon, Sp, readout, Comma, RowBreak, Grp(),
            nonFactor, Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, exactSystem, Dot));
    }
}
