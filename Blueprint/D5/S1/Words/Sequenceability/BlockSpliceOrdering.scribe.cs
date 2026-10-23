using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class BlockSpliceOrderingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block surgery on a directed cycle with distinct vertices and labels.",
        H("An old edge cut after a block splice"),
        Blocks(Describe.Lean(
            DescribeId.Create("block-splice-ordering"),
            DeclarationHandle.Create("D5/S1/Words/Sequenceability/BlockSpliceOrdering.block_splice_ordering"),
            H("Exact complementary labels and separated prefixes"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let G be any additive commutative group. Distinct cyclic vertices "
                    + "z(0),...,z(N-1) have distinct labels c(i)=z((i+1) mod N)-z(i). "
                    + "For 2 <= k <= t < N, assume the chord z(k)-z(0) equals c(t). "
                    + "The construction cuts the old edge indexed by t and retains the new chord. "
                    + "It orders exactly the labels c(k),...,c(N-1), each once. All bounded "
                    + "prefix sums, including empty and full prefixes, are distinct; every "
                    + "nonempty bounded interval has nonzero sum. The full sum is -c(t) and is nonzero.")),
                Paragraph(Text("The explicit path traverses z(t+1),...,z(N-1), then z(0), "
                    + "then z(k),...,z(t). Its label indices are t+1,...,N-1, then t for the new "
                    + "chord, then k,...,t-1. The three disjoint index blocks prove both inventories "
                    + "and distinctness. The initial block can be empty when t=N-1, and the last "
                    + "label block can be empty when t=k, including simultaneous emptiness. "
                    + "The label equality identifies values, not edge occurrences. No distinction "
                    + "between old and new label values, or restriction on characteristic, is assumed.")),
                Paragraph(Text("The result also returns a path P whose bounded vertices permute "
                    + "z(0),z(k),...,z(N-1), with no repetitions. The word consists of consecutive "
                    + "differences of P. Existing list telescoping gives every prefix as P(j)-P(0); "
                    + "prefix splitting then proves the interval assertion. In the displayed formula, "
                    + "rangeFrom(k,n) denotes List.range' k n, map takes the function first, and "
                    + "take and drop take the count first. List operations otherwise have their "
                    + "usual meanings. The statement is a general cycle surgery result; finite-field "
                    + "primitive elements, independence and transport to a prescribed frame are "
                    + "separate premises needed to apply it to independent omitted vectors."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var n = X("N"); var k = X("k"); var t = X("t"); var g = X("G");
        var l = Sub(n, k); var nat = X("Nat"); var z = X("z"); var c = X("c");
        var p = X("P"); var w = X("w"); var i = X("i"); var j = X("j");
        var vertices = Map(p, Call("range", Add(l, D(1))));
        var kept = Call("rangeFrom", k, l);
        var step = Fun("i", nat, Sub(Call("P", Add(i, D(1))), Call("P", i)));
        var prefix = Fun("j", Call("Fin", Add(Call("length", w), D(1))),
            Sum(Call("take", Call("val", j), w)));
        var interval = Sum(Call("take", Sub(j, i), Call("drop", i, w)));
        var result = And(
            Call("Perm", vertices, Map(z, Call("cons", D(0), kept))),
            Call("Nodup", vertices),
            Eq(w, Map(step, Call("range", l))),
            All("j", nat, Imp(Le(j, l), Eq(Sum(Call("take", j, w)),
                Sub(Call("P", j), Call("P", D(0)))))),
            Call("Perm", w, Map(c, kept)), Call("Nodup", w), Eq(Call("length", w), l),
            Call("Injective", prefix),
            All("i", nat, All("j", nat, Imp(Lt(i, j), Imp(Le(j, Call("length", w)), Ne(interval, D(0)))))),
            Eq(Sum(w), Negate(Call("c", t))), Ne(Sum(w), D(0)));
        var cycle = All("i", nat, Imp(Lt(i, n), Eq(Call("c", i),
            Sub(Call("z", Call("mod", Add(i, D(1)), n)), Call("z", i)))));
        var body = Imp(Le(D(2), k), Imp(Le(k, t), Imp(Lt(t, n),
            Imp(Call("InjOn", z, Call("Iio", n)), Imp(Call("InjOn", c, Call("Iio", n)),
            Imp(cycle, Imp(Eq(Sub(Call("z", k), Call("z", D(0))), Call("c", t)),
                Ex("P", Arrow(nat, g), Ex("w", Call("List", g), result)))))))));
        return Disp(All("G", X("Type"), Seq(OpenBracket, Call("AddCommGroup", g), CloseBracket, Sp,
            All("z", Arrow(nat, g), All("c", Arrow(nat, g), All("N", nat,
                All("k", nat, All("t", nat, body))))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(X(name), [.. args]);
    private static Formula Map(Formula f, Formula l) => Call("map", f, l);
    private static Formula Sum(Formula l) => Call("sum", l);
    private static Formula Fun(string name, Formula type, Formula body) => Seq(Operatorname, Grp(X("fun")), Sp,
        Open, X(name), Colon, Sp, type, Close, Sp, Mapsto, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Negate(Formula a) => Seq(Minus, a);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula And(params Formula[] terms)
    {
        var result = terms[^1];
        for (int i = terms.Length - 2; i >= 0; --i)
            result = new Formula.Logic(Seq(Open, terms[i], Close), FormulaLogicOperator.And, Seq(Open, result, Close));
        return result;
    }
}
