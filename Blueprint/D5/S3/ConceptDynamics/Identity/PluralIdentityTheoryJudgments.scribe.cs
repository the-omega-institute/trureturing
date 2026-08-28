using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identity;

internal sealed class PluralIdentityTheoryJudgmentsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Identity/PluralIdentityTheoryJudgments."
            + "identity_theories_can_disagree_on_distinct_propositions";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct identity concepts can issue opposite judgments under distinct relations.",
        H("Plural Identity Theory Judgments"),
        Blocks(Describe.Lean(
            DescribeId.Create("plural-identity-theory-judgments"),
            DeclarationHandle.Create(Declaration),
            H("Identity theories can disagree on distinct propositions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first Boolean concept is constant, while the second is the identity "
                        + "readout. They are different concepts and induce different "
                        + "concept-relative compatibility relations.")),
                Paragraph(Text(
                    "The constant concept identifies false with true, whereas the identity "
                        + "concept distinguishes them. Because each judgment names its own "
                        + "compatibility relation, the disagreement is not a proposition and "
                        + "its negation inside one theory."))),
            DescribeRole.Theorem))));

    private static Formula Identity(Formula concept, Formula left, Formula right) =>
        Call("ConceptIdentity", concept, left, right);

    private static Formula TheoremFormula()
    {
        Formula first = F.Id("C1");
        Formula second = F.Id("C2");
        Formula boolean = F.Id("Bool");
        Formula falseValue = F.Id("false");
        Formula trueValue = F.Id("true");
        Formula conceptType = Seq(boolean, Sp, To, Sp, boolean);

        return Disp(Seq(
            Exists, Sp, first, Comma, Sp, second, Colon, Sp, conceptType, Comma,
            RowBreak, Grp(),
            first, Sp, Neq, Sp, second, Sp, Land,
            RowBreak, Grp(),
            Call("ConceptIdentity", first), Sp, Neq, Sp,
            Call("ConceptIdentity", second), Sp, Land,
            RowBreak, Grp(),
            Identity(first, falseValue, trueValue), Sp, Land,
            RowBreak, Grp(),
            Neg, Sp, Identity(second, falseValue, trueValue), Dot));
    }
}
