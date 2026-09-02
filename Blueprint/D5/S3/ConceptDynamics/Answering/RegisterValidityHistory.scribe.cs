using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Answering;

internal sealed class RegisterValidityHistoryDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Answering/RegisterValidityHistory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Append-only validity deltas keep exactly one active settlement per assertion key.",
        H("Register Validity History"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("revision-never-overwrites-the-history"),
                DeclarationHandle.Create(DeclarationPrefix + "revise_preserves_history_prefix"),
                H("Revision never overwrites the history"),
                StatementSource.FromAuthor(PrefixFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A validity history is a list of assignments, each setting one record to "
                        + "active or void; the effective status of a record is its latest "
                        + "assignment. Revision appends a delta that voids the superseded "
                        + "records and then appends the replacement as active, so the prior "
                        + "history is a prefix of the revised one and no record or delta is "
                        + "ever rewritten."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("revision-leaves-exactly-one-active-record-per-key"),
                DeclarationHandle.Create(DeclarationPrefix + "revise_leaves_exactly_one_active"),
                H("Revision leaves exactly one active record per key"),
                StatementSource.FromAuthor(ExactlyOneActiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose the delta voids every record that was active for the key and "
                            + "the replacement is a fresh record carrying that key. After "
                            + "revision a record is active for the key exactly when it is the "
                            + "replacement: a superseded record now ends in a void assignment, "
                            + "an untouched record keeps its old status and so was never active "
                            + "for the key, and the replacement ends in its active assignment.")),
                    Paragraph(Text(
                        "This is the Step 5 validity invariant of the codex-formal-answer skill: "
                            + "after any revision of P or G, one active settlement per assertion "
                            + "key remains, and the superseded ones stay in the history as void "
                            + "rather than disappearing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("revision-of-one-key-leaves-other-keys-unchanged"),
                DeclarationHandle.Create(DeclarationPrefix + "revise_preserves_other_keys"),
                H("Revision of one key leaves other keys unchanged"),
                StatementSource.FromAuthor(OtherKeysFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When every superseded record and the replacement carry the revised key, "
                        + "no appended assignment names a record of another key, so the "
                        + "effective status and the active set of every other key are the "
                        + "same before and after the revision."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula MemberOf(Formula element, Formula list) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, list);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula HistoryType(Formula recordType) =>
        Call("List", Call("Assignment", recordType));

    private static Formula PrefixFormula()
    {
        Formula recordType = F.Id("R");
        Formula history = F.Id("h");
        Formula superseded = F.Id("s");
        Formula replacement = F.Id("p");

        return Disp(ForAll(
            [
                Bound("R", F.Id("Type")),
                Bound("h", HistoryType(recordType)),
                Bound("s", Call("List", recordType)),
                Bound("p", recordType),
            ],
            Call("IsPrefix", history, Call("revise", history, superseded, replacement))));
    }

    private static Formula ExactlyOneActiveFormula()
    {
        Formula recordType = F.Id("R");
        Formula keyType = F.Id("K");
        Formula keyOf = F.Id("k");
        Formula history = F.Id("h");
        Formula key = F.Id("a");
        Formula superseded = F.Id("s");
        Formula replacement = F.Id("p");
        Formula record = F.Id("r");
        Formula cover = ForAll(
            [Bound("r", recordType)],
            ImpliesFormula(
                Call("IsActive", keyOf, history, key, record),
                MemberOf(record, superseded)));
        Formula hypotheses = And(
            cover,
            And(
                new Formula.Not(MemberOf(replacement, superseded)),
                Equal(Apply(keyOf, replacement), key)));
        Formula conclusion = ForAll(
            [Bound("r", recordType)],
            IffFormula(
                Call(
                    "IsActive",
                    keyOf,
                    Call("revise", history, superseded, replacement),
                    key,
                    record),
                Equal(record, replacement)));

        return Disp(ForAll(
            [
                Bound("R", F.Id("Type")),
                Bound("K", F.Id("Type")),
                Bound("k", Arrow(recordType, keyType)),
                Bound("h", HistoryType(recordType)),
                Bound("a", keyType),
                Bound("s", Call("List", recordType)),
                Bound("p", recordType),
            ],
            ImpliesFormula(hypotheses, conclusion)));
    }

    private static Formula OtherKeysFormula()
    {
        Formula recordType = F.Id("R");
        Formula keyType = F.Id("K");
        Formula keyOf = F.Id("k");
        Formula history = F.Id("h");
        Formula key = F.Id("a");
        Formula otherKey = F.Id("b");
        Formula superseded = F.Id("s");
        Formula replacement = F.Id("p");
        Formula record = F.Id("r");
        Formula element = F.Id("x");
        Formula keyed = ForAll(
            [Bound("x", recordType)],
            ImpliesFormula(MemberOf(element, superseded), Equal(Apply(keyOf, element), key)));
        Formula hypotheses = And(
            keyed,
            And(Equal(Apply(keyOf, replacement), key), NotEqual(otherKey, key)));
        Formula conclusion = ForAll(
            [Bound("r", recordType)],
            IffFormula(
                Call(
                    "IsActive",
                    keyOf,
                    Call("revise", history, superseded, replacement),
                    otherKey,
                    record),
                Call("IsActive", keyOf, history, otherKey, record)));

        return Disp(ForAll(
            [
                Bound("R", F.Id("Type")),
                Bound("K", F.Id("Type")),
                Bound("k", Arrow(recordType, keyType)),
                Bound("h", HistoryType(recordType)),
                Bound("a", keyType),
                Bound("b", keyType),
                Bound("s", Call("List", recordType)),
                Bound("p", recordType),
            ],
            ImpliesFormula(hypotheses, conclusion)));
    }
}
