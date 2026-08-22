using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.D5.S3.ConceptDynamics.Attribution.SymmetricEventNoUniqueCulprit;

internal sealed class SymmetricEventNoUniqueCulpritDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A completely symmetric event cannot have an equivariant unique culprit when at least "
            + "two subject labels are available.",
        H("Symmetric Events Have No Unique Culprit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-event-has-no-equivariant-unique-culprit"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "symmetric_event_admits_no_equivariant_culprit"),
                H("A symmetric event has no equivariant unique culprit"),
                StatementSource.FromAuthor(NoUniqueCulpritFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose at least two subject labels are available, every relabeling "
                            + "fixes the event, and the culprit selector commutes with every "
                            + "relabeling. Choose a label distinct from the selected culprit "
                            + "and swap the two labels.")),
                    Paragraph(Text(
                        "Complete symmetry leaves the event unchanged, so the selector must "
                            + "retain its value. Equivariance simultaneously requires the swap "
                            + "to move that value to the distinct label, which is impossible."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-point-event-is-completely-symmetric"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "trivial_event_is_completely_symmetric"),
                H("The one-point event is completely symmetric"),
                StatementSource.FromAuthor(TrivialEventFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The one-point event space supplies a concrete symmetric event for every "
                        + "number of subject labels. Its action always returns the sole event, "
                        + "so every permutation fixes that event and the symmetry premise is "
                        + "not vacuous."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("anchored-event-admits-an-equivariant-culprit"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "anchored_event_admits_equivariant_culprit"),
                H("An anchored event admits an equivariant culprit"),
                StatementSource.FromAuthor(AnchoredEventFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When an event carries a subject label that is transported by relabeling, "
                        + "the identity map selects that transported label equivariantly. Thus "
                        + "equivariance alone does not prevent a unique culprit; the obstruction "
                        + "comes from complete symmetry of the event."))),
                DescribeRole.Lemma))));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula FiniteSubjects(Formula size) =>
        Call("Fin", size);

    private static Formula Permutations(Formula size) =>
        Call("Perm", FiniteSubjects(size));

    private static Formula NoUniqueCulpritFormula()
    {
        Formula size = F.Id("n");
        Formula eventType = F.Id("Event");
        Formula action = F.Id("act");
        Formula culprit = F.Id("culprit");
        Formula eventValue = F.Id("event");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, size, Colon, Sp, NaturalNumbers(), Comma, Sp,
            eventType, Colon, Sp, TypeUniverse(), Comma, RowBreak, Grp(),
            action, Colon, Sp,
            Arrow(Permutations(size), Arrow(eventType, eventType)), Comma, RowBreak, Grp(),
            culprit, Colon, Sp,
            Arrow(eventType, FiniteSubjects(size)), Comma, Sp,
            eventValue, Colon, Sp, eventType, Comma, RowBreak, Grp(),
            Open,
            D(2), Sp, Leq, Sp, size, Sp, Land, Sp,
            Call("IsEquivariantCulprit", action, culprit), Sp, Land, Sp,
            Call("IsCompletelySymmetric", action, eventValue),
            Close, Sp, Rightarrow, Sp, F.Id("False"), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TrivialEventFormula()
    {
        Formula size = F.Id("n");
        Formula unitEvent = Seq(Open, Close);

        return Disp(Seq(
            Forall, Sp, size, Colon, Sp, NaturalNumbers(), Comma, Sp,
            Call(
                "IsCompletelySymmetric",
                Call("trivialEventAction", size),
                unitEvent),
            Dot));
    }

    private static Formula AnchoredEventFormula()
    {
        Formula size = F.Id("n");
        Formula culprit = F.Id("culprit");
        Formula subjects = FiniteSubjects(size);

        return Disp(Seq(
            Forall, Sp, size, Colon, Sp, NaturalNumbers(), Comma, Sp,
            Exists, Sp, culprit, Colon, Sp, Arrow(subjects, subjects), Comma, Sp,
            Call("IsEquivariantCulprit", F.Id("anchoredEventAction"), culprit),
            Dot));
    }
}
