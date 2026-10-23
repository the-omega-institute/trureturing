using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class OriginalClauseLanguagesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact original guarded clause languages.",
        H("Exact original guarded clause languages"),
        Blocks(
            Paragraph(Text("W is the domain of the unrestricted original decoder. S requires that same decoder and a satisfying assignment on the original appearing-name subtype; U is W and not S. Q is the ordered pair of U first and S second under the unchanged outer pairWords encoding. Empty conjunction and one empty clause give the valid true word 00 and valid false word 011000. False repair always returns a valid original formula and preserves SAT. True repair converts guarded UNSAT exactly to complement SAT; malformed words lie in neither guarded language. The pair equivalence covers all raw outer words.")),
            Describe.Lean(
                DescribeId.Create("repair-laws"),
                DeclarationHandle.Create("D5/S0/Computability/OriginalClauseLanguages.repair_laws"),
                H("repair_laws"),
                StatementSource.FromAuthor(Presentation0()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("W is the domain of the unrestricted original decoder. S requires that same decoder and a satisfying assignment on the original appearing-name subtype; U is W and not S. Q is the ordered pair of U first and S second under the unchanged outer pairWords encoding. Empty conjunction and one empty clause give the valid true word 00 and valid false word 011000. False repair always returns a valid original formula and preserves SAT. True repair converts guarded UNSAT exactly to complement SAT; malformed words lie in neither guarded language. The pair equivalence covers all raw outer words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pair-language"),
                DeclarationHandle.Create("D5/S0/Computability/OriginalClauseLanguages.pair_language"),
                H("pair_language"),
                StatementSource.FromAuthor(Presentation1()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Computability/rbarish2026binarymachine")),
                Blocks(Paragraph(Text("W is the domain of the unrestricted original decoder. S requires that same decoder and a satisfying assignment on the original appearing-name subtype; U is W and not S. Q is the ordered pair of U first and S second under the unchanged outer pairWords encoding. Empty conjunction and one empty clause give the valid true word 00 and valid false word 011000. False repair always returns a valid original formula and preserves SAT. True repair converts guarded UNSAT exactly to complement SAT; malformed words lie in neither guarded language. The pair equivalence covers all raw outer words."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/UnrestrictedClauseWords")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/BinaryMachine/StackPair"))]));

    private static Formula All(string n, Formula d, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, p);
    private static Formula Ex(string n, Formula d, Formula p) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, p);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Presentation0() =>
        All("w", Id("Word"),
        And(Call("W", Call("repair", Id("falseWord"), Id("w"))),
            And(Iff(Call("S", Call("repair", Id("falseWord"), Id("w"))), Call("S", Id("w"))),
                And(Iff(Call("U", Id("w")), new Formula.Not(
                        Call("S", Call("repair", Id("trueWord"), Id("w"))))),
                    Imp(Call("W", Id("w")), And(
                        Equal(Call("repair", Id("falseWord"), Id("w")), Id("w")),
                        Equal(Call("repair", Id("trueWord"), Id("w")), Id("w"))))))));

    private static Formula Presentation1() =>
        All("w", Id("Word"), Iff(Call("Q", Id("w")),
        Ex("u", Id("Word"), Ex("v", Id("Word"),
            And(Equal(Call("decodePair", Id("w")), Call("some", Call("pair", Id("u"), Id("v")))),
                And(Call("U", Id("u")), Call("S", Id("v"))))))));
}
