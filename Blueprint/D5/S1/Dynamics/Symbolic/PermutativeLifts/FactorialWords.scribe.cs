using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class FactorialWordsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialWords.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recognizable factorial words and finite holonomy.",
        H("Recognizable factorial words and finite holonomy"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "word"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The words begin with the single letter a at level zero. At level n+1 they concatenate (n+1)! copies of the zero-type level-n word and (a+1)(n+1)! copies of the one-type word. The same unbounded sequence of words neutralizes every prescribed finite group-valued letter product once the level is large enough. The ordered holonomy multiplies the last letter on the left. Pair occurrence and length growth are used by the minimality and aperiodicity proofs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "word_holonomy_eq_one"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The words begin with the single letter a at level zero. At level n+1 they concatenate (n+1)! copies of the zero-type level-n word and (a+1)(n+1)! copies of the one-type word. The same unbounded sequence of words neutralizes every prescribed finite group-valued letter product once the level is large enough. The ordered holonomy multiplies the last letter on the left. Pair occurrence and length growth are used by the minimality and aperiodicity proofs."))), DescribeRole.Theorem))));
}
