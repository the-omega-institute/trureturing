using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalOntology;

internal sealed class DuplicateActionLabelInvarianceDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/OperationalOntology/DuplicateActionLabelInvariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Replicating labels for existing action behaviors does not create operational freedom.",
        H("Duplicate Action Label Invariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-action-label-quotient-map"),
                DeclarationHandle.Create(DeclarationPrefix + "actionLabelQuotientMap"),
                H("The retained-label map descends to behavior classes"),
                StatementSource.FromAuthor(MapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each extended label is assigned an original representative with the same "
                        + "complete continuation profile, while the retained original labels "
                        + "retract to themselves. The inclusion therefore induces the displayed "
                        + "map between the two profile-kernel quotients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("duplicate-labels-preserve-effective-action-space"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "duplicate_action_labels_preserve_effective_space"),
                H("Duplicate labels preserve effective action space and capacity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The profile functions are source-semantic primitives: they record the "
                            + "outcome for every continuation. No quotient or capacity is defined "
                            + "to be the theorem's conclusion.")),
                    Paragraph(Text(
                        "The canonical map induced by retaining old labels is bijective. Its "
                            + "inverse sends every extended label to its chosen behaviorally "
                            + "equivalent original representative; the two inverse laws hold "
                            + "after quotienting by complete-profile equality.")),
                    Paragraph(Text(
                        "For finite label types, equivalence of the effective quotients gives "
                            + "equal cardinalities and hence equal base-two log-cardinality "
                            + "operational capacities."))),
                DescribeRole.Proposition))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula ProfileType(Formula action, Formula continuation, Formula outcome) =>
        Arrow(action, Arrow(continuation, outcome));

    private static Formula EffectiveQuotient(Formula profile) =>
        Call("QuotientKer", profile);

    private static Formula MapFormula()
    {
        Formula action = F.Id("A");
        Formula extendedAction = F.Id("Aplus");
        Formula continuation = F.Id("W");
        Formula outcome = F.Id("O");
        Formula profile = F.Id("Prof");
        Formula extendedProfile = F.Id("ProfPlus");
        Formula include = F.Id("i");
        Formula representative = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, action, Comma, Sp, extendedAction, Comma, Sp,
            continuation, Comma, Sp, outcome, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            Typed(profile, ProfileType(action, continuation, outcome)), Comma, Sp,
            Typed(extendedProfile,
                ProfileType(extendedAction, continuation, outcome)), Comma,
            RowBreak, Grp(),
            Typed(include, Arrow(action, extendedAction)), Comma, Sp,
            Typed(representative, Arrow(extendedAction, action)), Comma,
            RowBreak, Grp(),
            Call("LeftInverse", representative, include), Sp, Land, Sp,
            Open, Forall, Sp, F.Id("a"), Colon, Sp, extendedAction, Comma, Sp,
            Seq(extendedProfile, Open, F.Id("a"), Close), Sp, Eq, Sp,
            Seq(profile, Open, representative, Open, F.Id("a"), Close, Close), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Call("actionLabelQuotientMap", profile, extendedProfile, include,
                representative), Colon, Sp,
            Arrow(EffectiveQuotient(profile), EffectiveQuotient(extendedProfile)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TheoremFormula()
    {
        Formula action = F.Id("A");
        Formula extendedAction = F.Id("Aplus");
        Formula continuation = F.Id("W");
        Formula outcome = F.Id("O");
        Formula profile = F.Id("Prof");
        Formula extendedProfile = F.Id("ProfPlus");
        Formula include = F.Id("i");
        Formula representative = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula quotientMap = Call("actionLabelQuotientMap", profile,
            extendedProfile, include, representative);
        Formula originalQuotient = EffectiveQuotient(profile);
        Formula extendedQuotient = EffectiveQuotient(extendedProfile);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, action, Comma, Sp, extendedAction, Comma, Sp,
                continuation, Comma, Sp, outcome, Colon, Sp, type, Comma),
            Seq(Call("Finite", action), Comma, Sp, Call("Finite", extendedAction), Comma),
            Seq(
                Typed(profile, ProfileType(action, continuation, outcome)), Comma, Sp,
                Typed(extendedProfile,
                    ProfileType(extendedAction, continuation, outcome)), Comma),
            Seq(
                Typed(include, Arrow(action, extendedAction)), Comma, Sp,
                Typed(representative, Arrow(extendedAction, action)), Comma),
            Seq(
                Call("LeftInverse", representative, include), Sp, Land, Sp,
                Open, Forall, Sp, F.Id("a"), Colon, Sp, extendedAction, Comma, Sp,
                Seq(extendedProfile, Open, F.Id("a"), Close), Sp, Eq, Sp,
                Seq(profile, Open, representative, Open, F.Id("a"), Close, Close), Close,
                Sp, Rightarrow),
            Seq(
                Call("Bijective", quotientMap), Sp, Land),
            Seq(
                Call("log2", Call("card", originalQuotient)), Sp, Eq, Sp,
                Call("log2", Call("card", extendedQuotient)), Dot),
        ]));
    }
}
