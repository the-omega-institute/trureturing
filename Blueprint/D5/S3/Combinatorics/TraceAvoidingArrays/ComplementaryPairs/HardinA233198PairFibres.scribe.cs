using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs;

internal sealed class HardinA233198PairFibresDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198PairFibres.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233198");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered complementary-pair fibres for literal width-four eight-colour arrays.",
        H("Eight colours and four complementary pairs"),
        Blocks(
            Def("generating-function", "GeneratingFunction", "The full generating-function proposition",
                GeneratingFunctionFormula(),
                "Division means formal inversion in rational power series.", true),
            Paragraph(Text(
                "A cell is a pair in Fin n times Fin 4, and its row-major rank is "
                + "four times its first natural label plus its second. Fin.val is "
                + "the natural label of a finite element. Natural-number sums are "
                + "used for the exclusion of complementary colours. The three "
                + "directed edge representatives describe precisely the contained "
                + "horizontal, vertical and antidiagonal bonds.")),
            Thm("two-colours", "ordinary_two_count", "The two-colour boundary", SmallColourFormula(2, 2, 0),
                "At height one the graph is a path. Every larger height contains the "
                + "triangle on cells (0,0), (0,1), (1,0), which excludes two colours."),
            Thm("three-colours", "ordinary_three_count", "The three-colour classification", SmallColourFormula(3, 24, 6),
                "At height one there are twenty-four proper rows. For a row that has "
                + "a compatible neighbour, the three distinct colours force the pattern "
                + "(a,b,c,a); the unique successor is (c,a,b,c). The kernel-checked local "
                + "compatibility certificate and continuation induction give six colourings "
                + "at every larger height."),
            Thm("four-series", "ordinary_series_four", "The four-colour formal series", FourSeriesFormula(),
                "Proper rows have the five equality patterns 0101, 0102, 0120, 0121, "
                + "0123. Their compatibility test compares equal columns and the old "
                + "column j+1 with the new column j. The complete finite row table "
                + "and initial row-pair distribution are checked by kernel reduction. "
                + "The general continuation transfer is applied after a bijection from "
                + "the exact graph's proper maps to proper-row words. A kernel-checked "
                + "fourth-order matrix relation gives the recurrence at every applicable "
                + "height. Coefficientwise multiplication then proves the formal-series "
                + "identity; the denominator is a unit because its constant coefficient is one."),
            Thm("generating-function-theorem", "generating_function", "The literal all-height identity",
                FullSeriesEquality(),
                "Rescale the ordinary four-colour series by sixteen. The weighted count "
                + "identifies the coefficients of 384 A minus that rescaled series: "
                + "zero in degree zero, 2496 in degree one, and 384 times sixteen to "
                + "the power n minus one in every degree n at least two. Multiplication "
                + "by one minus sixteen X leaves 2496 X minus 33792 X squared. "
                + "The rescaled four-colour denominator and numerator then give the "
                + "entire displayed polynomial identity. Its denominator has constant "
                + "coefficient one, so formal inversion is valid. The coefficient "
                + "definition of A retains exactly the literal positive-height arrays, "
                + "including the height-one boundary and unused colours."))));

    private static DocumentBlock Def(string id, string name, string title, Formula formula,
        string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);


    private static DocumentBlock Thm(string id, string name, string title, Formula formula,
        string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233198PairFibres.";
    private static Formula SmallColourFormula(long q, long first, long later)
    {
        var n = V("n");
        return All("n", Q("Nat"), Imp(Lt(D(0), n), Eq(Own("ordinaryCount", Num(q), n),
            Call("ite", Eq(n, D(1)), Num(first), Num(later)))));
    }

    private static Formula FourSeriesFormula()
    {
        var x = Q("PowerSeries.X");
        Formula Term(long c, byte k) => Mul(Num(c), Power(x, D(k)));
        var num = Sub(Add(Sub(Term(108, 1), Term(528, 2)), Term(960, 3)), Term(1200, 4));
        var den = Add(Sub(Add(Sub(D(1), Term(12, 1)), Term(40, 2)), Term(68, 3)), Term(64, 4));
        return Eq(Own("ordinarySeries", D(4)), Mul(num, Power(den, new Formula.Negate(D(1)))));
    }

    private static Formula GeneratingFunctionFormula()
        => Iff(Own("GeneratingFunction"), FullSeriesEquality());

    private static Formula FullSeriesEquality()
    {
        var x = Q("PowerSeries.X");
        Formula Term(long c, byte k) => Mul(Num(c), Power(x, D(k)));
        var num = Mul(x, Sub(Add(Sub(Add(Sub(D(1,1), Term(1760, 1)), Term(99328, 2)),
            Term(3080192, 3)), Term(55050240, 4)), Term(369098752, 5)));
        var den = Mul(Sub(D(1), Term(16, 1)),
            Add(Sub(Add(Sub(D(1), Term(192, 1)), Term(10240, 2)), Term(278528, 3)), Term(4194304, 4)));
        return Eq(Own("A"), Mul(num, Power(den, new Formula.Negate(D(1)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula Own(string name, params Formula[] args) => App(Q(LeanPrefix + name), args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula a, Formula b) => P(Seq(a, Colon, Sp, b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Iff, P(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(P(a), FormulaBinaryOperator.Add, P(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(P(a), FormulaBinaryOperator.Subtract, P(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(P(a), FormulaBinaryOperator.Multiply, P(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string v, Formula t, Formula b) => Seq(Forall, Sp, Typed(V(v), t), Comma, Sp, P(b));
}
