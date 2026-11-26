using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233198Formulas;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs;

internal sealed class HardinA233198LiteralModelDocument : IScribeDocumentDefinition
{
    private const string ModelPrefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/ComplementaryPairs/HardinA233198LiteralModel.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233198");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal width-four eight-colour rectangle, complementary pairs and ordinary colourings.",
        H("Literal model and coefficient convention"),
        Blocks(
            Def("edge", "Edge", "Contained bonds", EdgeFormula(),
                "The vertical row increases by one. On the antidiagonal the column "
                + "decreases by one. Every endpoint already belongs to the finite "
                + "rectangle; main-diagonal and wraparound constraints are absent."),
            Def("normal", "Normal", "Strict earlier-colour prerequisites", NormalFormula(),
                "Each existential predecessor has strictly smaller rank. There "
                + "is no requirement that a colour occur."),
            Def("legal", "Legal", "The literal arrays", LegalFormula(),
                "The top-left existential rejects height zero. The two bond "
                + "conditions concern inequality and natural sum seven.", true),
            Def("count", "a", "Literal cardinality", CountFormula(),
                "Nat.card counts the subtype of all functions satisfying Legal. "
                + "The domain has n rows and four columns.", true),
            Def("series", "A", "Positive-height coefficient encoding", SeriesFormula(),
                "The power series has rational coefficients. Degree zero is "
                + "explicitly zero and every positive coefficient is the literal count."),
            Def("pair", "pair", "Complementary pairs", PairFormula(),
                "The pair label is the smaller member of the complementary pair. "
                + "Two colours are allowed on a bond exactly when their pair labels differ."),
            Def("pair-normal", "PairNormal", "Order of first use", PairNormalFormula(),
                "An occurrence of pair two or three requires an earlier pair one. "
                + "An occurrence of pair three also requires an earlier pair two. "
                + "The anchor fixes pair zero at the least cell."),
            Def("pair-legal", "PairLegal", "Proper pair maps", PairLegalFormula(),
                "The same literal edge relation is used for the pair map. "
                + "First-use requirements allow higher pairs to remain absent."),
            Def("first", "First", "First occurrence in a pair", FirstFormula(),
                "The comparison uses the supplied natural rank function."),
            Def("free", "Free", "The independent binary positions", FreeFormula(),
                "A free cell has an earlier cell with the same pair label. "
                + "The first member of each used pair is forced to be its smaller colour."),
            Def("fibre-count", "fibreCount", "Literal fibre cardinality", FibreCountFormula(),
                "The fibre consists of the literal arrays whose pointwise pair map equals p."),
            Def("proper", "Proper", "Ordinary colourings on the same graph", ProperFormula(),
                "The finite colour set has q labels. Every literal contained edge "
                + "is retained. These ordinary maps have no anchor or earlier-colour prerequisites."),
            Def("ordinary-count", "ordinaryCount", "The labelled colouring count", OrdinaryCountFormula(),
                "All proper functions are counted, including functions that omit labels."),
            Def("ordinary-series", "ordinarySeries", "The ordinary colouring series", OrdinarySeriesFormula(),
                "The coefficient at zero is zero. Positive coefficients count the same "
                + "contained horizontal, vertical and antidiagonal graph."),
            Thm("fibre", "literal_fibre_card", "The exact pair fibre", FibreFormula(),
                "Fix a proper ordered pair map. Assign its smaller colour at each "
                + "first occurrence and either complementary colour at every other "
                + "cell. Least-rank representatives supply all literal earlier-colour "
                + "requirements. Conversely the literal prerequisites force the "
                + "smaller first representatives. These constructions are inverse "
                + "and identify the fibre with all Boolean assignments to Free p."),
            Thm("fibre-power", "literal_fibre_power", "One forced cell per used pair", FibrePowerFormula(),
                "The first cells are in bijection with the range of the pair map. "
                + "Distinct first cells cannot have the same pair because row-major "
                + "rank is injective. Every used pair has a least-rank representative. "
                + "There are four times n cells altogether."),
            Thm("sum", "literal_count_by_pairs", "The disjoint fibre sum", FibreSumFormula(),
                "Every literal array determines a unique legal pair map. "
                + "Summation over all such maps includes every possible number of used pairs."),
            Thm("ordinary-pairs", "ordinary_count_by_pairs", "Injective labels on the used pairs",
                OrdinaryPairsFormula(),
                "Order the used colour classes by their least row-major ranks. Missing labels "
                + "are ordered after every actual cell. The resulting canonical pair map "
                + "satisfies the anchor and first-use conditions. Two such pair maps with "
                + "the same equality classes agree: at a first disagreement, the smaller "
                + "label must already have occurred in the other map. Injective assignments "
                + "of q labels to the used pairs are therefore in bijection with all proper "
                + "q-colourings. The falling factorial counts these assignments even when "
                + "some labels are unused."),
            Thm("literal-ordinary", "literal_ordinary_count", "The complete weighted count",
                LiteralOrdinaryFormula(),
                "Every positive-height graph has a horizontal edge, so each legal pair map "
                + "uses two, three or four pairs. For each of these three possibilities, "
                + "the Boolean fibre weight equals the stated weighted falling-factorial "
                + "combination. Summation gives the identity without an orbit division "
                + "or a surjectivity assumption."))));

    private static DocumentBlock Def(string id, string name, string title, Formula formula,
        string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(ModelPrefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Thm(string id, string name, string title, Formula formula,
        string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(ModelPrefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

}

internal static class HardinA233198Formulas
{
    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.ComplementaryPairs.HardinA233198PairFibres.";
    internal static Formula EdgeFormula()
    {
        var n = V("n"); var v = V("v"); var w = V("w");
        Formula Row(Formula z) => Call("Prod.fst", z);
        Formula Col(Formula z) => Call("Prod.snd", z);
        var horizontal = And(Eq(Row(v), Row(w)), Eq(Val(Col(w)), Add(Val(Col(v)), D(1))));
        var vertical = And(Eq(Val(Row(w)), Add(Val(Row(v)), D(1))), Eq(Col(v), Col(w)));
        var antidiagonal = And(Eq(Val(Row(w)), Add(Val(Row(v)), D(1))),
            Eq(Val(Col(v)), Add(Val(Col(w)), D(1))));
        return All("n", Q("Nat"), All("v", Cells(n), All("w", Cells(n),
            Iff(Own("Edge", v, w), Or(horizontal, Or(vertical, antidiagonal))))));
    }

    internal static Formula NormalFormula()
    {
        var t = V("V"); var r = V("r"); var f = V("f"); var v = V("v"); var w = V("w");
        var current = App(f, v);
        Formula Earlier(int c) => Ex("w", t,
            And(Lt(App(r, w), App(r, v)), Eq(App(f, w), Typed(Num(c), Fin(D(8))))));
        var conditions = All("v", t, And(
            Imp(And(Le(D(2), Val(current)), Le(Val(current), D(6))), Earlier(1)),
            And(Imp(Or(Eq(current, D(3)), Or(Eq(current, D(4)), Eq(current, D(5)))), Earlier(2)),
                Imp(Eq(current, D(4)), Earlier(3)))));
        return All("V", Q("Type"), All("r", Arrow(t, Q("Nat")), All("f", Arrow(t, Fin(D(8))),
            Iff(Own("Normal", r, f), conditions))));
    }

    internal static Formula LegalFormula()
    {
        var n = V("n"); var f = V("f"); var v = V("v"); var w = V("w");
        var bonds = All("v", Cells(n), All("w", Cells(n), Imp(Own("Edge", v, w),
            And(Ne(App(f, v), App(f, w)), Ne(Add(Val(App(f, v)), Val(App(f, w))), D(7))))));
        return All("n", Q("Nat"), All("f", Arrow(Cells(n), Fin(D(8))),
            Iff(Own("Legal", f), And(Anchor(n, f), And(Own("Normal", Own("rank"), f), bonds)))));
    }

    internal static Formula CountFormula()
    {
        var n = V("n");
        return All("n", Q("Nat"), Eq(Own("a", n), Call("Nat.card",
            Subtype("f", Arrow(Cells(n), Fin(D(8))), Own("Legal", V("f"))))));
    }

    internal static Formula SeriesFormula()
    {
        var n = V("n");
        return Eq(Own("A"), Call("PowerSeries.mk", Fn("n", Q("Nat"),
            Call("ite", Eq(n, D(0)), D(0), Typed(Own("a", n), Q("Rat"))))));
    }

    internal static Formula PairFormula()
    {
        var x = V("x");
        return All("x", Fin(D(8)), Eq(Val(Own("pair", x)),
            Call("ite", Lt(Val(x), D(4)), Val(x), Call("Nat.sub", D(7), Val(x)))));
    }

    internal static Formula PairNormalFormula()
    {
        var t = V("V"); var r = V("r"); var p = V("p"); var v = V("v"); var w = V("w");
        Formula Earlier(int c) => Ex("w", t,
            And(Lt(App(r, w), App(r, v)), Eq(App(p, w), Typed(Num(c), Fin(D(4))))));
        return All("V", Q("Type"), All("r", Arrow(t, Q("Nat")), All("p", Arrow(t, Fin(D(4))),
            Iff(Own("PairNormal", r, p), All("v", t,
                And(Imp(Le(D(2), Val(App(p, v))), Earlier(1)),
                    Imp(Eq(App(p, v), D(3)), Earlier(2))))))));
    }

    internal static Formula PairLegalFormula()
    {
        var n = V("n"); var p = V("p"); var v = V("v"); var w = V("w");
        var bonds = All("v", Cells(n), All("w", Cells(n),
            Imp(Own("Edge", v, w), Ne(App(p, v), App(p, w)))));
        return All("n", Q("Nat"), All("p", Arrow(Cells(n), Fin(D(4))),
            Iff(Own("PairLegal", p), And(Anchor(n, p), And(Own("PairNormal", Own("rank"), p), bonds)))));
    }

    internal static Formula FirstFormula()
    {
        var t = V("V"); var r = V("r"); var p = V("p"); var v = V("v"); var w = V("w");
        return All("V", Q("Type"), All("r", Arrow(t, Q("Nat")), All("p", Arrow(t, Fin(D(4))),
            All("v", t, Iff(Own("First", r, p, v), All("w", t,
                Imp(Lt(App(r, w), App(r, v)), Ne(App(p, w), App(p, v)))))))));
    }

    internal static Formula FreeFormula()
    {
        var n = V("n"); var p = V("p");
        return All("n", Q("Nat"), All("p", Arrow(Cells(n), Fin(D(4))),
            Eq(Own("Free", p), Subtype("v", Cells(n), Not(Own("First", Own("rank"), p, V("v")))))));
    }

    internal static Formula FibreFormula()
    {
        var n = V("n"); var p = V("p");
        return All("n", Q("Nat"), All("p", Arrow(Cells(n), Fin(D(4))),
            Imp(Own("PairLegal", p), Eq(Own("fibreCount", p),
                Power(D(2), Call("Nat.card", Own("Free", p)))))));
    }

    internal static Formula FibreCountFormula()
    {
        var n = V("n"); var p = V("p"); var v = V("v"); var f = V("f");
        var fibre = Subtype("f", Arrow(Cells(n), Fin(D(8))),
            And(Own("Legal", f), Eq(Fn("v", Cells(n), Own("pair", App(f, v))), p)));
        return All("n", Q("Nat"), All("p", Arrow(Cells(n), Fin(D(4))),
            Eq(Own("fibreCount", p), Call("Nat.card", fibre))));
    }

    internal static Formula FibrePowerFormula()
    {
        var n = V("n"); var p = V("p");
        return All("n", Q("Nat"), All("p", Arrow(Cells(n), Fin(D(4))),
            Imp(Own("PairLegal", p), Eq(Own("fibreCount", p),
                FibreWeight(n, p)))));
    }

    internal static Formula FibreSumFormula()
    {
        var n = V("n"); var p = V("p");
        var pairMaps = Subtype("p", Arrow(Cells(n), Fin(D(4))), Own("PairLegal", p));
        return All("n", Q("Nat"), Eq(Own("a", n), Call("Finset.sum", Q("Finset.univ"),
            Fn("p", pairMaps, FibreWeight(n, Call("Subtype.val", p))))));
    }

    internal static Formula FibreWeight(Formula n, Formula p) =>
        Power(D(2), Call("Nat.sub", Mul(D(4), n), Call("Nat.card", Call("Set.range", p))));

    internal static Formula ProperFormula()
    {
        var q = V("q"); var n = V("n"); var f = V("f"); var v = V("v"); var w = V("w");
        return All("q", Q("Nat"), All("n", Q("Nat"), All("f", Arrow(Cells(n), Fin(q)),
            Iff(Own("Proper", f), All("v", Cells(n), All("w", Cells(n),
                Imp(Own("Edge", v, w), Ne(App(f, v), App(f, w)))))))));
    }

    internal static Formula OrdinaryCountFormula()
    {
        var q = V("q"); var n = V("n");
        return All("q", Q("Nat"), All("n", Q("Nat"), Eq(Own("ordinaryCount", q, n),
            Call("Nat.card", Subtype("f", Arrow(Cells(n), Fin(q)), Own("Proper", V("f")))))));
    }

    internal static Formula OrdinarySeriesFormula()
    {
        var q = V("q"); var n = V("n");
        return All("q", Q("Nat"), Eq(Own("ordinarySeries", q),
            Call("PowerSeries.mk", Fn("n", Q("Nat"), Call("ite", Eq(n, D(0)), D(0),
                Typed(Own("ordinaryCount", q, n), Q("Rat")))))));
    }

    internal static Formula OrdinaryPairsFormula()
    {
        var q = V("q"); var n = V("n"); var p = V("p");
        var maps = Subtype("p", Arrow(Cells(n), Fin(D(4))), Own("PairLegal", p));
        var weight = Call("Nat.descFactorial", q,
            Call("Nat.card", Call("Set.range", Call("Subtype.val", p))));
        return All("q", Q("Nat"), All("n", Q("Nat"),
            Imp(Le(q, D(4)), Imp(Lt(D(0), n), Eq(Own("ordinaryCount", q, n),
                Call("Finset.sum", Q("Finset.univ"), Fn("p", maps, weight)))))));
    }

    internal static Formula LiteralOrdinaryFormula()
    {
        var n = V("n");
        Formula Count(byte q) => Typed(Own("ordinaryCount", D(q), n), Q("Rat"));
        var weighted = Add(Add(new Formula.Fraction(Count(4), Num(24)),
            new Formula.Fraction(Count(3), D(6))),
            new Formula.Fraction(Mul(D(5), Count(2)), D(4)));
        return All("n", Q("Nat"), Imp(Lt(D(0), n), Eq(Typed(Own("a", n), Q("Rat")),
            Mul(Power(Num(16), Call("Nat.sub", n, D(1))), weighted))));
    }

    internal static Formula Anchor(Formula n, Formula f) => Ex("h", Lt(D(0), n),
        Eq(App(f, Pair(Call("Fin.mk", D(0), V("h")), D(0))), D(0)));
    internal static Formula Cells(Formula n) => Product(Fin(n), Fin(D(4)));
    internal static Formula Subtype(string v, Formula t, Formula p) => Call("Subtype", Fn(v, t, p));
    internal static Formula V(string name) => F.Id(name);
    internal static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    internal static Formula Own(string name, params Formula[] args) => App(Q(LeanPrefix + name), args);
    internal static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    internal static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    internal static Formula Fin(Formula n) => Call("Fin", n);
    internal static Formula Val(Formula x) => Call("Fin.val", x);
    internal static Formula P(Formula f) => Seq(Open, f, Close);
    internal static Formula Pair(Formula a, Formula b) => P(Seq(a, Comma, Sp, b));
    internal static Formula Product(Formula a, Formula b) => Seq(P(a), Sp, Times, Sp, P(b));
    internal static Formula Typed(Formula a, Formula b) => P(Seq(a, Colon, Sp, b));
    internal static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Fn(string n, Formula t, Formula b) => P(Seq(LambdaLower, Sp, Typed(V(n), t), Sp, Mapsto, Sp, b));
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Iff(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Iff, P(b));
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    internal static Formula Or(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Or, P(b));
    internal static Formula Add(Formula a, Formula b) => new Formula.Binary(P(a), FormulaBinaryOperator.Add, P(b));
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(P(a), FormulaBinaryOperator.Subtract, P(b));
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(P(a), FormulaBinaryOperator.Multiply, P(b));
    internal static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    internal static Formula Not(Formula a) => Seq(Neg, P(a));
    internal static Formula All(string v, Formula t, Formula b) => Seq(Forall, Sp, Typed(V(v), t), Comma, Sp, P(b));
    internal static Formula Ex(string v, Formula t, Formula b) => Seq(Exists, Sp, Typed(V(v), t), Comma, Sp, P(b));
}
