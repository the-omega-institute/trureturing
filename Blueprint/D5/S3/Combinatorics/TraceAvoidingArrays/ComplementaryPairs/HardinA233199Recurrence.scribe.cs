using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs;

internal sealed class HardinA233199RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233199Recurrence.";
    private const string LeanName =
        "D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233199Recurrence";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233199");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal width-five OEIS A233199 recurrence.",
        H("The anchored width-five array count"),
        Blocks(
            Describe.Lean(DescribeId.Create("literal-count"), DeclarationHandle.Create(Prefix + "a"),
                H("Literal count"),
                StatementSource.FromAuthor(Disp(LiteralCount())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("At positive height n, count exactly the functions from Fin n times Fin 5 "
                    + "to Fin 8 with top-left value zero. The endpoints of each contained horizontal, "
                    + "vertical and antidiagonal edge are unequal and their natural labels do not sum to seven. "
                    + "An occurrence of 2, 3, 4, 5 or 6 requires an earlier 1. An occurrence of 3, 4 or 5 "
                    + "requires an earlier 2. An occurrence of 4 requires an earlier 3. Earlier means strictly "
                    + "smaller rank 5 times the row plus the column. Colours may be unused."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("recurrence"), DeclarationHandle.Create(Prefix + "result"),
                H("The ten signed lags at every height at least twelve"),
                StatementSource.FromAuthor(Disp(Recurrence())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The width counting bridge reads the original literal rows. The boundary "
                        + "records each column's complementary pair and the first-use stage records which "
                        + "lower representatives have occurred in the full prefix. A relabelling permutes "
                        + "only pairs whose lower representatives have already appeared and preserves "
                        + "each colour's orientation within its pair.")),
                    Paragraph(Text("There are twenty-three boundary classes across the three possible "
                        + "post-row stages. The kernel checks the signed row counts in every matrix entry and "
                        + "the initial vector from the literal anchored first row. The terminal vector is "
                        + "one at every state. The checked vector relation starts at the eleventh matrix "
                        + "power and left multiplication propagates it to all higher powers. The literal "
                        + "count at height n uses power n minus one, yielding all ten signed lags with onset twelve. "
                        + "The recurrence interprets the counts and arithmetic in the integers, and its lag "
                        + "indices in the natural numbers."))),
                DescribeRole.Theorem))));

    private static Formula LiteralCount()
    {
        var n = F.Id("n");
        var f = F.Id("f");
        Formula Fin(Formula size) => new Formula.Apply(Qualified("Fin"), [size]);
        var cells = Seq(Open, Fin(n), Sp, Times, Sp, Fin(D(5)), Close);
        var array = new Formula.TypeArrow(cells, Fin(D(8)));
        var legal = new Formula.Apply(
            Qualified("HardinA233196Strip.widthLegal"),
            [Qualified("rowLegal"), Qualified("bonds"), f]);
        var arrays = Seq(OpenBrace, f, Colon, Sp, array, Sp, Mid, Sp, legal, CloseBrace);
        var card = new Formula.Apply(Qualified("Nat.card"), [arrays]);
        var equation = new Formula.Relation(
            new Formula.Apply(Qualified(LeanName + ".a"), [n]), FormulaRelationOperator.Equal, card);
        return Seq(Forall, Sp, Typed(n, Qualified("Nat")), Comma, Sp, equation);
    }

    private static Formula Recurrence()
    {
        var n = F.Id("n");
        Formula Count(Formula height) =>
            Typed(new Formula.Apply(Qualified(LeanName + ".a"), [height]), Qualified("Int"));
        Formula Term(Formula coefficient, Formula lag) =>
            new Formula.Binary(coefficient, FormulaBinaryOperator.Multiply,
                Count(new Formula.Binary(n, FormulaBinaryOperator.Subtract, lag)));
        Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
        Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
        var rhs = Term(D(7, 3, 6), D(1));
        rhs = Sub(rhs, Term(D(2, 0, 3, 7, 7, 6), D(2)));
        rhs = Add(rhs, Term(D(3, 3, 0, 6, 2, 9, 1, 2), D(3)));
        rhs = Sub(rhs, Term(D(3, 6, 6, 5, 8, 2, 1, 6, 9, 6), D(4)));
        rhs = Add(rhs, Term(D(2, 7, 0, 8, 5, 1, 3, 7, 5, 1, 0, 4), D(5)));
        rhs = Sub(rhs, Term(D(1, 0, 6, 8, 5, 8, 7, 8, 6, 3, 2, 4, 4, 8), D(6)));
        rhs = Sub(rhs, Term(D(1, 1, 6, 5, 4, 8, 2, 3, 2, 5, 4, 4, 2, 5, 6), D(7)));
        rhs = Add(rhs, Term(D(3, 5, 1, 8, 4, 3, 7, 2, 0, 8, 8, 8, 3, 2, 0, 0, 0), D(8)));
        rhs = Sub(rhs, Term(D(1, 4, 2, 3, 1, 3, 7, 4, 8, 2, 2, 4, 9, 0, 7, 6, 7, 3, 6), D(9)));
        rhs = Add(rhs, Term(D(1, 8, 4, 4, 6, 7, 4, 4, 0, 7, 3, 7, 0, 9, 5, 5, 1, 6, 1, 6), D(1, 0)));
        var onset = new Formula.Relation(D(1, 2), FormulaRelationOperator.LessThanOrEqual, n);
        var equation = new Formula.Relation(Count(n), FormulaRelationOperator.Equal, rhs);
        return Seq(Forall, Sp, Typed(n, Qualified("Nat")), Comma, Sp,
            new Formula.Logic(onset, FormulaLogicOperator.Implies, equation));
    }

    private static Formula Typed(Formula value, Formula type) => Seq(Open, value, Colon, Sp, type, Close);
    private static Formula Qualified(string name) => Seq(name.Split('.').SelectMany((part, index) =>
        index == 0 ? new[] { Seq(Operatorname, Grp(F.Id(part))) }
                   : new[] { Dot, Seq(Operatorname, Grp(F.Id(part))) }).ToArray());
}
