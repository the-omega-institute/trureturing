using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using DefinitionDsl = StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class CloitreVToothpickPrefixDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/CellularAutomata/CloitreVToothpickPrefix";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/cloitre2026vtoothpick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All prefix corrections of the honeycomb V-toothpick kernel vanish.",
        H("Vanishing prefix corrections in the V-toothpick kernel"),
        Blocks(
            Definition("period-index", "periodIndex", "Euclidean period index", PeriodIndex(),
                "The notation i(j,p,r) denotes this index. The offset and remainder are "
                + "computed in the integers, and Int.toNat converts the entire sum."),
            Definition("column-period", "columnPeriod", "Column period", ColumnPeriod(),
                "The notation p(j) denotes this period. For j ≥ 1, it is twice the least "
                + "power of two strictly greater than j."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("The full prefix equality"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Section 9 asks whether all prefix corrections ηⱼ vanish, "
                        + "equivalently whether for every dyadic P the coefficients of E_c "
                        + "of degree less than P are determined by c modulo 2P.")),
                    Paragraph(Text("Here e(j,c) is the coefficient of degree j in the integer "
                        + "polynomial E_c of equation (17) and is computed by birthKernelEntry. "
                        + "The period p(j) is 2 raised to "
                        + "floor(log₂ j)+2, twice the least dyadic integer P strictly above j. "
                        + "The function i(j,p,r) returns j−1 plus the Euclidean remainder "
                        + "of r−j+1 modulo p, computed over the integers before conversion to a natural. "
                        + "The third equality states that the correction "
                        + "of equation (43) is zero. At j=1 the prefix range is empty.")),
                    Paragraph(Text("Take any dyadic P>j. For each of the two cuts, height "
                        + "4P at column c+2P and height 3P at column c have the same strict "
                        + "bound on g=2x+y+p, where p is the vertex color. "
                        + "At read time s=6P−c−1+j, every nonzero signed weight "
                        + "lies strictly below the displaced-wall horizon in both runs. "
                        + "The first-touch comparison matches the birth indicators at "
                        + "both cuts, including vertices missing from a clipped domain.")),
                    Paragraph(Text("The strip identity shifts the adjacent-cut difference "
                        + "at height 3P and column c by 2P to give the difference at "
                        + "height 4P and column c. Reading both coefficients at the common "
                        + "dyadic enclosure gives e(j,c)=e(j,c+2P). For the least eligible P, "
                        + "the negative offset in the Euclidean remainder of equation (43) "
                        + "gives i(j,p(j),c mod p(j))=c+p(j)."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string name, string title, Formula formula,
        string description) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);

    private static Formula PeriodIndex()
    {
        var j = DefinitionDsl.Id("j");
        var p = DefinitionDsl.Id("p");
        var r = DefinitionDsl.Id("r");
        var one = Num(1);
        var offset = Add(Subtract(IntCast(r), IntCast(j)), one);
        var remainder = new Formula.Modulo(Parenthesized(offset), IntCast(p));
        var index = Add(Subtract(IntCast(j), one), Parenthesized(remainder));
        var toNat = Seq(Operatorname, Grp(FormulaDsl.Id("Int"), Dot, FormulaDsl.Id("toNat")));
        return All("j", All("p", All("r", Equal(Call("periodIndex", j, p, r),
            new Formula.Apply(toNat, [index])))));
    }

    private static Formula ColumnPeriod()
    {
        var j = DefinitionDsl.Id("j");
        var log = Seq(Operatorname, Grp(FormulaDsl.Id("Nat"), Dot, FormulaDsl.Id("log2")));
        return All("j", Equal(Call("columnPeriod", j),
            new Formula.Power(Num(2), Add(new Formula.Apply(log, [j]), Num(2)))));
    }

    private static Formula IntCast(Formula value) =>
        Parenthesized(Seq(value, Colon, Sp, Mathbb, Grp(FormulaDsl.Id("Z"))));

    private static Formula Statement()
    {
        var j = DefinitionDsl.Id("j");
        var c = DefinitionDsl.Id("c");
        var p = Call("columnPeriod", j);
        var index = Call("periodIndex", j, p, new Formula.Modulo(c, p));
        var prefix = Call("birthKernelEntry", j, c);
        var shifted = Call("birthKernelEntry", j, Add(c, p));
        var periodic = Call("birthKernelEntry", j, index);
        var equalities = new Formula.Logic(Equal(prefix, shifted), FormulaLogicOperator.And,
            new Formula.Logic(Equal(shifted, periodic), FormulaLogicOperator.And,
                Equal(Subtract(prefix, periodic), Num(0))));
        return All("j", All("c", Implies(LeqOf(Num(1), j),
            Implies(LeqOf(Add(c, Num(2)), j), equalities))));
    }

    private static Formula All(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable),
            Seq(Mathbb, Grp(DefinitionDsl.Id("N"))), body);

    private static Formula LeqOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
}
