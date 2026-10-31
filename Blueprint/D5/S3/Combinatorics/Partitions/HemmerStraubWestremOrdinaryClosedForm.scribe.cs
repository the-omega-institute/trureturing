using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class HemmerStraubWestremOrdinaryClosedFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var left = Call("ordinaryLeftAverage", n);
        var right = Call("ordinaryRightAverage", n);
        var half = Call("natDiv", n, new Formula.Number(2));
        var value = Call("parityValue", n, Call("choose", new Formula.Binary(half, FormulaBinaryOperator.Add, new Formula.Number(2)), new Formula.Number(2)));
        var statement = All("n", Call("Nat"), Imp(Call("positive", n), And(Eq(left, right), And(Eq(left, value), Eq(right, value)))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Both original ordinary HSW averages and their common value", H("Both original ordinary HSW averages and their common value"), Blocks(
                Paragraph(Text("ordinaryLeftAverage and ordinaryRightAverage are the complex trace averages defined in HemmerStraubWestremOrdinary. The first is the signed sum over every even-part partition of 2n with at most three rows and literal zero padding. The second uses the literal rectangle (n,n,0) for every n, including odd n. Both retain every input partition lambda of n, every independent per-occurrence Ev replacement and duplicate outcome, and the reciprocal centralizer product over all positive cycle sizes including one. Each reciprocal is formed in the rationals and then cast to the complex numbers.")),
                Paragraph(Text("In the formula, n is a natural number at least one, division by two is natural-number division, choose is the natural binomial coefficient, and parityValue(n,b) is the canonical complex cast of b when n is even and zero when n is odd. Thus both averages have the value choose(n/2+2,2) in even degree and zero in odd degree. The actual same-shape trace comparison is consumed through both ordinary-term transports before the existing rational coefficient result is applied.")),
                Describe.Lean(DescribeId.Create("result"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinaryClosedForm.result"),
                    H("Full positive-degree ordinary-character conclusion"), StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/hemmerstraubwestrem2025riordan")),
                    Blocks(Paragraph(Text("The coefficient evaluation is reused from the canonical HemmerStraubWestremWeightedAverage supplier. Its implementation and formal differential-equation uniqueness proof remain owned there. This composition introduces no coefficient-evaluation assumption and no new coefficient proof."))), DescribeRole.Theorem))));
    }

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
