using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class LanguageMonitorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every canonical increasing digit pair has the endpoint complement property", H("Every canonical increasing digit pair has the endpoint complement property"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagemonitor-initial"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.initial"),
                H("initial"), StatementSource.FromAuthor(Disp(Equal(F.Id("initial"),Tuple(F.Id("badStart"),F.Id("endpointStart"),D(0),D(0),F.Id("false"),F.Id("true"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructor lists fields bad, endpoint, previousX, previousY, strict and valid in that order."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagemonitor-invalid"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.invalid"),
                H("invalid"), StatementSource.FromAuthor(Disp(Equal(F.Id("invalid"),Tuple(D(0),D(0),D(0),D(0),F.Id("false"),F.Id("false"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The invalid signature is absorbing under the monitor update."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagemonitor-step"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.step"),
                H("step"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"s",F.Id("Signature"),Bind(FormulaQuantifier.ForAll,"symbol",Call("Fin",D(4)),Equal(Call("step",F.Id("s"),F.Id("symbol")),Call("if",Call("boolOr",Call("not",Call("valid",F.Id("s"))),Call("boolOr",Call("boolAnd",Call("eqBool",Call("previousX",F.Id("s")),D(1)),Call("eqBool",Call("div",Call("val",F.Id("symbol")),D(2)),D(1))),Call("boolOr",Call("boolAnd",Call("eqBool",Call("previousY",F.Id("s")),D(1)),Call("eqBool",Call("mod",Call("val",F.Id("symbol")),D(2)),D(1))),Call("boolAnd",Call("not",Call("strict",F.Id("s"))),Call("decide",Less(Call("mod",Call("val",F.Id("symbol")),D(2)),Call("div",Call("val",F.Id("symbol")),D(2)))))))),F.Id("invalid"),Tuple(Call("maskStep",F.Id("badRows"),Call("bad",F.Id("s")),Call("val",F.Id("symbol"))),Call("maskStep",F.Id("endpointMasks"),Call("endpoint",F.Id("s")),Call("val",F.Id("symbol"))),Call("div",Call("val",F.Id("symbol")),D(2)),Call("mod",Call("val",F.Id("symbol")),D(2)),Call("boolOr",Call("strict",F.Id("s")),Call("decide",Less(Call("div",Call("val",F.Id("symbol")),D(2)),Call("mod",Call("val",F.Id("symbol")),D(2))))),F.Id("true")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The expression is this literal update. Let x=val(symbol) div 2 and y=val(symbol) mod 2, where div is truncated natural division. Return invalid if not valid, if previousX=x=1, if previousY=y=1, or if strict is false and y<x. Otherwise return (maskStep(badRows,bad,val(symbol)),maskStep(endpointMasks,endpoint,val(symbol)),x,y,strict OR decide(x<y),true)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagemonitor-hasaccept"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.hasAccept"),
                H("hasAccept"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"mask",Naturals(),Bind(FormulaQuantifier.ForAll,"accept",Naturals(),Equal(Call("hasAccept",F.Id("mask"),F.Id("accept")),Call("notEqualBool",Call("bitAnd",F.Id("mask"),F.Id("accept")),D(0))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("bitAnd is natural bitwise AND. notEqualBool returns true precisely when its arguments differ."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagemonitor-conclusion"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.conclusion"),
                H("conclusion"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"s",F.Id("Signature"),Equal(Call("conclusion",F.Id("s")),Implies(Equal(Call("valid",F.Id("s")),F.Id("true")),Implies(Equal(Call("strict",F.Id("s")),F.Id("true")),Equal(Call("hasAccept",Call("bad",F.Id("s")),F.Id("badAccept")),Call("not",Call("hasAccept",Call("endpoint",F.Id("s")),F.Id("endpointAccept")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A valid strictly increasing canonical pair is accepted by exactly one of the mismatch and endpoint languages."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagemonitor-every-word"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageMonitor.every_word"),
                H("every_word"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"w",Call("List",Call("Fin",D(4))),Call("conclusion",Call("foldl",F.Id("step"),F.Id("initial"),F.Id("w")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The concrete monitor certificate is closed under all four digit-pair symbols and satisfies the terminal implication at every listed state. Induction transports those finite statements to every word; invalid or non-strict words retain the implication without a claim about complementarity."))), DescribeRole.Theorem))));


    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Tuple(params Formula[] items) => Call("tuple", items);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
