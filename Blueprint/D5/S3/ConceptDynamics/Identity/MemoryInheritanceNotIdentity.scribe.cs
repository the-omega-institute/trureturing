using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identity;

internal sealed class MemoryInheritanceNotIdentityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Identity/MemoryInheritanceNotIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A branching memory relation is not right-unique and therefore cannot coincide with "
            + "equality.",
        H("Branching Memory Inheritance Is Not Equality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("branching-memory-is-not-right-unique"),
                DeclarationHandle.Create(DeclarationPrefix + "branching_not_right_unique"),
                H("Branching memory is not right-unique"),
                StatementSource.FromAuthor(NotRightUniqueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A branch gives one predecessor two distinct successors. Right uniqueness "
                        + "would force those successors to be equal, contradicting the "
                        + "distinction that witnesses the branch."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("branching-memory-is-not-equality"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "branching_memory_is_not_equality"),
                H("Branching memory inheritance is not equality"),
                StatementSource.FromAuthor(NotEqualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If a memory relation agreed with equality on every pair, then any two "
                            + "successors of the same predecessor would both equal that "
                            + "predecessor and hence equal each other.")),
                    Paragraph(Text(
                        "Such a relation would be right-unique. A branching memory relation has "
                            + "two distinct successors for one predecessor, so it cannot "
                            + "coincide with equality."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula RelationType(Formula person) =>
        Arrow(person, Arrow(person, F.Id("Prop")));

    private static Formula NotRightUniqueFormula()
    {
        Formula person = F.Id("Person");
        Formula relation = F.Id("M");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Person", F.Id("Type")),
                Bound("M", RelationType(person)),
            ],
            new Formula.Logic(
                Call("AllowsBranching", relation),
                FormulaLogicOperator.Implies,
                new Formula.Not(Call("RightUnique", relation)))));
    }

    private static Formula NotEqualityFormula()
    {
        Formula person = F.Id("Person");
        Formula relation = F.Id("M");
        Formula left = F.Id("a");
        Formula right = F.Id("b");
        Formula equalityCharacterization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("a", person), Bound("b", person)],
            new Formula.Logic(
                new Formula.Apply(relation, [left, right]),
                FormulaLogicOperator.Iff,
                Equal(left, right)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Person", F.Id("Type")),
                Bound("M", RelationType(person)),
            ],
            new Formula.Logic(
                Call("AllowsBranching", relation),
                FormulaLogicOperator.Implies,
                new Formula.Not(equalityCharacterization))));
    }
}
