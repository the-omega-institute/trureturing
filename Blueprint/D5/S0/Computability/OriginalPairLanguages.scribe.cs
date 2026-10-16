using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class OriginalPairLanguagesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All raw outer words have an exact guarded intersection characterization.",
        H("The ordered original guarded pair language"),
        Blocks(Describe.Lean(
            DescribeId.Create("ordered-guarded-pair-split"),
            DeclarationHandle.Create("D5/S0/Computability/OriginalPairLanguages.pair_split"),
            H("UNSAT is first and SAT is second"),
            StatementSource.FromAuthor(All("w", Id("Word"), Iff(Call("Q", Id("w")),
                And(new Formula.Not(Call("S", Call("leftGuard", Id("w")))),
                    Call("S", Call("rightGuard", Id("w"))))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The outer decoder projects the first component with a valid true fallback "
                + "and the second with a valid false fallback. Each component is then repaired "
                + "with the corresponding original unrestricted guard. Thus the left factor "
                + "is complement SAT after true repair, and the right factor is SAT after "
                + "false repair. Their conjunction equals the exact language Q on every raw "
                + "word. Invalid outer pairs and either invalid component are excluded. "
                + "Payloads keep the original formulaWord bytes, arbitrary finite clause and "
                + "name lengths, repetitions, tautologies, and both empty boundaries. "
                + "This is a semantic decomposition; polynomial execution of the decoder "
                + "repair requires its source-semantic connection to the lexical machine."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/OriginalClauseLanguages")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/PairProjection"))]));

    private static Formula All(string n, Formula d, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, p);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
