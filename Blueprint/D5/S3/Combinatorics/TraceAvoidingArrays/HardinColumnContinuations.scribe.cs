using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinColumnContinuationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233170");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual column decompositions for two-row and three-row diagonal strips.",
        H("Column reading preserves every original bond"),
        Blocks(
            Def("column", "Column", "Actual three-label columns", "Column h is Fin(h+1) to Fin 3, without an internal vertical restriction."),
            Def("cross", "cross", "All bonds between consecutive columns", "For each row the two horizontal labels differ. For each pair of adjacent rows the two diagonal label pairs differ. These are exactly the original horizontal and both diagonal edges, with no vertical or wraparound edge."),
            Describe.Lean(DescribeId.Create("decidable-cross"), DeclarationHandle.Create(Prefix + "instDecidableCross"),
                H("Decision for all column cross-bonds"), StatementSource.FromAuthor(Disp(DecidableCrossFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For h : Nat and actual columns p,q : Fin (h+1) to Fin 3, inferInstanceAs decides the conjunction of all horizontal inequalities and both diagonal inequalities at every adjacent row."))), DescribeRole.Definition),
            Def("continuation", "columnV", "Complete column continuations", "The zero-column tail has one filling. At each successor length, sum over all actual next columns satisfying cross. There is no restriction to a representative subset of the graph domain."),
            Def("equivalence", "coloringEquiv", "Reversible reading and reconstruction", "Read an actual graph colouring by columns. Conversely place every supplied column entry back at its original cell. The adjacent-column cross conditions supply every graph bond, and both maps are inverse at every positive width and height."),
            Def("class-b", "classB", "The two column classes", "Class zero has equal labels and class one has distinct labels. Their actual initial cardinalities are 3 and 6."),
            Def("matrix-b", "B", "The source B matrix", "B=((2,2),(1,0)). All four cross-bonds occur between two-row columns, so the consecutive label supports are disjoint. Each entry is checked for every actual incoming column."),
            Def("continuation-b", "vB", "B continuations", "vB(0,i)=1 and vB(k+1,i)=sum over j of B(i,j)vB(k,j)."),
            Def("class-h", "classH", "Every three-row column class", "The four classes are 000; 001 or 011; 010; and 012, up to label permutation. Their exact initial counts are 3,12,6,6. The two equal-adjacent shapes share a class because their continuation counts agree."),
            Def("matrix-h", "H", "The source H matrix", "H=((2,4,2),(1,1,0),(1,0,0)) on the first three classes."),
            Def("matrix-full", "Hfull", "The isolated class is retained", "Hfull has H in its upper-left corner and a zero fourth row and fourth column. An all-distinct column has no successor because the next middle label would have to avoid all three colours. No column can precede it, either. These statements concern actual cross-bonds."),
            Def("continuation-h", "hV", "The three-class source recurrence", "hV(0,i)=1 and hV(k+1,i)=sum over the three source classes of H(i,j)hV(k,j)."),
            Def("continuation-full", "vH", "The complete four-class recurrence", "vH uses Hfull and has initial value one in every class. Its first three entries equal hV at every length. Its fourth entry is one at length zero and zero at every positive length."),
            Describe.Lean(DescribeId.Create("column-certificate"),
                DeclarationHandle.Create(Prefix + "column_certificate"),
                H("Exact column transitions and class sizes"), StatementSource.FromAuthor(Disp(ColumnCertificateFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every actual column, the successor counts equal B or Hfull at its class. The two-row class sizes are 3 and 6; the three-row class sizes are 3, 12, 6 and 6. The Hfull transition and size projections supply the zero-defect sectors of HardinA229536Strip after its exact budget and class cut and the natural-to-integer cast."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "column_result"),
                H("Exact universal B and H interpretations"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The variable k is the number of appended columns, so the actual width is k+1. The equations hold for every k≥0 on the original two-row and three-row strip graphs. Reading columns and splitting off the first one gives the exact graph count. The finite class certificates then feed induction on every continuation length. Consequently B and H have the displayed source interpretations, independently of terminal generating-series equality. At k=0 the three-row count is 3+12+6+6=27, and the literal normalized count is 11. For positive k the isolated contribution vanishes, giving precisely the source H expression for widths at least two. The width-one correction is part of the formula."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part, k) => k == 0
        ? new[] { Seq(Operatorname, Grp(F.Id(part))) }
        : new[] { Dot, Seq(Operatorname, Grp(F.Id(part))) }).ToArray());
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Name(name) : new Formula.Apply(Name(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula ResultFormula()
    {
        var k = F.Id("k");
        Formula Count(byte h) => Call("Nat.card", Call("Coloring",
            Call("stripGraph", Call("true"), D(h), k), Call("Fin", D(3))));
        Formula Bv(byte i) => Call("vB", k, D(i));
        Formula Hv(byte i) => Call("hV", k, D(i));
        var correction = Call("ite", Seq(k, Sp, F.Eq, Sp, D(0)), D(6), D(0));
        return Seq(Forall, Sp, k, Colon, Sp, Call("Nat"), Comma, Sp,
            Count(1), Sp, F.Eq, Sp, Add(Mul(D(3), Bv(0)), Mul(D(6), Bv(1))), Sp, Land, Sp,
            Count(2), Sp, F.Eq, Sp,
            Add(Add(Add(Mul(D(3), Hv(0)), Mul(D(1,2), Hv(1))), Mul(D(6), Hv(2))), correction));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Fin(byte size) => Call("Fin", D(size));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(
        Seq(Call("if"), Sp, Parenthesized(test), Sp, Call("then"), Sp, Parenthesized(yes), Sp, Call("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Vector(params Formula[] entries) => Seq(new Formula[] { Bang, OpenBracket }
        .Concat(entries.SelectMany((f,i) => i == 0 ? new[] { f } : new[] { Comma, Sp, f })).Append(CloseBracket).ToArray());
    private static Formula ColumnCertificateFormula()
    {
        var p = V("p"); var q = V("q"); var j = V("j");
        Formula Own(string name, params Formula[] args) => Call("HardinColumnContinuations." + name, args);
        Formula Column(byte h) => Own("Column", D(h));
        Formula Transition(byte h, byte size, string cl, string matrix) =>
            All("p", Column(h), All("j", Fin(size), Eq(SumOver("q", Column(h), Conditional(
                And(Own("cross", p, q), Eq(Own(cl, q), j)), D(1), D(0))), Own(matrix, Own(cl, p), j))));
        Formula Initial(byte h, byte size, string cl, Formula values) =>
            All("j", Fin(size), Eq(SumOver("p", Column(h), Conditional(Eq(Own(cl, p), j), D(1), D(0))),
                At(Typed(values, new Formula.TypeArrow(Fin(size), Call("Nat"))), j)));
        return And(Transition(1, 2, "classB", "B"), And(Transition(2, 4, "classH", "Hfull"),
            And(Initial(1, 2, "classB", Vector(D(3), D(6))),
                Initial(2, 4, "classH", Vector(D(3), D(1,2), D(6), D(6))))));
    }

    private static Formula DecidableCrossFormula() => All("h", Call("Nat"), All("p", Call("HardinColumnContinuations.Column", V("h")),
            All("q", Call("HardinColumnContinuations.Column", V("h")), Typed(
                Call("HardinColumnContinuations.instDecidableCross", V("h"), V("p"), V("q")),
                Call("Decidable", Call("HardinColumnContinuations.cross", V("p"), V("q")))))));

}
