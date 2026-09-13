using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class TranslationPrefixDomainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Domains of Guarded Translation Words.",
        H("Domains of Guarded Translation Words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("translationprefixdomain-eval-eq-some-iff"),
                DeclarationHandle.Create("D5/S0/Rewriting/TranslationPrefixDomain.eval_eq_some_iff"),
                H("All prefixes determine successful evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite coordinate set, a natural capacity at each coordinate, and a finite "
                    + "word of integer translation vectors, evaluation succeeds at a specified endpoint "
                    + "exactly when every prefix displacement added to the initial state lies between "
                    + "zero and the capacity in every coordinate, and the endpoint is the initial state "
                    + "plus the sum of the word. Prefixes include the empty word and the whole word. "
                    + "The recursive evaluation stops at the first state outside the box; the empty "
                    + "word also checks its initial state."))),
                DescribeRole.Theorem))));
}
