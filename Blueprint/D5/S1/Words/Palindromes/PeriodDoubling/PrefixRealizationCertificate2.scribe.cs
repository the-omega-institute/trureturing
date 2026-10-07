using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class PrefixRealizationCertificate2Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal marker successors are completely represented in this finite row interval.", H("Marker Reconstruction Certificate"), Blocks(
        Describe.Lean(DescribeId.Create("pd-prefixrealizationcertificate2-rows"),
            DeclarationHandle.Create("D5/S1/Words/Palindromes/PeriodDoubling/PrefixRealizationCertificate2.prefix_realization_rows_2"), H("Rows 1024 through 1535"),
            StatementSource.FromAuthor(Disp(All("i",N(),Imp(And(LeF(new Formula.Number(1024),V("i")),LtF(V("i"),new Formula.Number(1536))),
                Eqn(Call("prefixRealizationRowCheck",V("i")),Ty("true")))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Kernel reduction checks every literal marker successor against the indexed edge list and every target index against the 4262-state bound. The interval includes its lower endpoint and excludes its upper endpoint."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);



}
