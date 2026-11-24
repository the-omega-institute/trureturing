using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow;

internal sealed class HardinA233178ChromaticDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/FiveRow/HardinA233178Chromatic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact three-label transfer on the five-row horizontal and diagonal exclusion graph.",
        H("Literal columns and continuation counts"),
        Blocks(
            Paragraph(Text("A column is encoded in base three, with row r stored in digit r. "
                + "Bond tests precisely the pairs of rows at distance at most one across consecutive "
                + "columns. The strip has free boundaries and has no within-column bonds.")),
            LiteralNode("moves", Arrow(Column(), Call("List", Column())), "The Lean definition is the literal vector of 243 successor lists. Applying the vector to the current column code selects its list. The theorem moves_eq_filter identifies each list with the eligible columns in code order."),
            FormulaNode("moves_eq_filter", MovesFilter(), true, "Filtering the ordered column codes by the bond condition gives the stored successor list."),
            LiteralNode("table", Arrow(Fin(12), Arrow(Column(), new Formula.Integers())), "The Lean definition is the literal 12-by-243 integer vector of vectors. The first index is the number of extra columns and the second selects the boundary code. The theorem powers_table identifies the rows with continuation vectors."),
            FormulaNode("coefficients", Coefficients(), false, "The coefficients are listed in order of increasing power."),
            FormulaNode("step_fast", Step(), true, "Matrix action at a boundary is the sum over its legal successors."),
            FormulaNode("powers_table", Powers(), true, "The tabulated row is the continuation vector at the specified exponent."),
            FormulaNode("Column", Eq(Column(), Fin(243)), false, "Five-row column codes in base three."),
            FormulaNode("colour", Colour(), false, "Nat.div takes the natural quotient and Nat.mod takes its remainder modulo three."),
            FormulaNode("Bond", Bond(), false, "Each entry differs from the entries at the same or adjacent rows of the next column."),
            FormulaNode("instDecidableBond", BondInstance(), false, "The legal-bond predicate is decidable by checking the finitely many row pairs."),
            FormulaNode("forwardCutPair", ForwardCutPair(), false, "The embedding sends a row index to its cast into the larger row type and its successor."),
            FormulaNode("cut_parts", CutParts(), true, "The adjacent pairs in one direction are the image of this embedding. The two diagonal directions are disjoint, and their union is disjoint from the straight pairs."),
            FormulaNode("T", TransferEntry(), false, "Rows index the current column and columns index its successor."),
            FormulaNode("v", Continuations(), false, "Each coordinate counts continuations of the specified length from its boundary column."),
            FormulaNode("vector_certificate", VectorCertificate(), true, "At exponent eleven the continuation vector is the given linear combination of the vectors at exponents one through ten."),
            FormulaNode("result", Recurrence(), true, "The finite vector relation propagates to all subsequent exponents by TransferMatrix.scalarRelationShift."))));

    private static DocumentBlock FormulaNode(string name, Formula statement, bool theorem, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(name), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static DocumentBlock LiteralNode(string name, Formula type, string prose) =>
        Describe.Lean(DescribeId.Create(name), DeclarationHandle.Create(Prefix + name),
            H(name), StatementSource.FromAuthor(Disp(Typed(C(name), type))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(long c, Formula a) => new Formula.Binary(N(c), FormulaBinaryOperator.Multiply, a);
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Pow(Formula a,Formula b) => Seq(Parenthesized(a),Caret,Grp(b));


    private static Formula VectorLiteral(long[] entries)
    {
        Formula tail = Q("Matrix.vecEmpty");
        for (int i = entries.Length - 1; i >= 0; i--)
            tail = Call("Matrix.vecCons", N(entries[i]), tail);
        return tail;
    }
    private static Formula Column() => Q("HardinA233178Chromatic.Column");
    private static Formula C(string n,params Formula[] a) => Call("HardinA233178Chromatic."+n,a);

    private static Formula Colour() {
        var p = V("p");
        var r = V("r");
        return All("p", Column(), All("r", Fin(5), Eq(Val(Typed(C("colour", p, r), Fin(3))),
            Call("Nat.mod", Call("Nat.div", Val(p), Pow(N(3), Val(r))), N(3)))));
    }

    private static Formula Bond() {
        var p = V("p");
        var q = V("q");
        var r = V("r");
        var s = V("s");
        var adjacent = new Formula.Logic(
            new Formula.Relation(Val(r), FormulaRelationOperator.LessThanOrEqual, Add(Val(s), N(1))),
            FormulaLogicOperator.And,
            new Formula.Relation(Val(s), FormulaRelationOperator.LessThanOrEqual, Add(Val(r), N(1))));
        var unequal = new Formula.Relation(C("colour", p, r), FormulaRelationOperator.NotEqual, C("colour", q, s));
        var rows = All("r", Fin(5), All("s", Fin(5),
            new Formula.Logic(Parenthesized(adjacent), FormulaLogicOperator.Implies, unequal)));
        return All("p", Column(), All("q", Column(),
            new Formula.Logic(C("Bond", p, q), FormulaLogicOperator.Iff, Parenthesized(rows))));
    }

    private static Formula BondInstance() => All("p", Column(), All("q", Column(),
        Typed(C("instDecidableBond", V("p"), V("q")), Call("Decidable", C("Bond", V("p"), V("q"))))));

    private static Formula ForwardCutPair()
    {
        var k = V("k");
        var i = V("i");
        var smaller = Call("Fin", k);
        return All("k", Q("Nat"), All("i", smaller,
            Eq(C("forwardCutPair", k, i), Parenthesized(Seq(Call("Fin.castSucc", i), Comma, Sp, Call("Fin.succ", i))))));
    }

    private static Formula CutParts()
    {
        var k = V("k");
        var height = Add(k, N(1));
        var row = Call("Fin", height);
        Formula Universe(Formula type) => Typed(Q("Finset.univ"), Call("Finset", type));
        Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, Parenthesized(b));
        var forward = Call("Finset.map", C("forwardCutPair", k), Universe(Call("Fin", k)));
        var swap = Call("Equiv.toEmbedding", Call("Equiv.prodComm", row, row));
        var backward = Call("Finset.map", swap, forward);
        var straight = Call("Finset.diag", Universe(row));
        var diagonal = Call("HardinA229637RowColumn.betw", height);
        var union = new Formula.SetOperation(forward, FormulaSetOperator.Union, backward);
        return All("k", Q("Nat"), And(Eq(Call("HardinA229637RowColumn.horiz", height), forward),
            And(Eq(diagonal, union), And(Call("Disjoint", forward, backward), Call("Disjoint", straight, diagonal)))));
    }

    private static Formula MovesFilter()
    {
        var p = V("p");
        var q = V("q");
        var predicate = Parenthesized(Seq(LambdaLower, Sp, Typed(q, Column()), Mapsto, Sp,
            Call("decide", C("Bond", p, q))));
        return All("p", Column(), Eq(Typed(C("moves", p), Call("List", Column())),
            Call("List.filter", predicate, Call("List.finRange", N(243)))));
    }
    private static Formula Coefficients() => Eq(Typed(C("coefficients"),Arrow(Fin(10),Q("Int"))),
        VectorLiteral([-36,72,192,-514,93,417,-163,-97,31,6]));
    private static Formula One() => Typed(N(1),Arrow(Column(),Q("Int")));
    private static Formula Power(Formula exponent) => Call("Matrix.mulVec",Pow(C("T"),exponent),One());
    private static Formula VectorCertificate()
    {
        var j = V("j");
        var term = Call("SMul.smul", C("coefficients", j), Power(Add(N(1), Val(j))));
        return Eq(Power(Add(N(1), N(10))), Seq(F.Sum, Underscore, Grp(Typed(j, Fin(10))), Sp,
            Parenthesized(term)));
    }
    private static Formula TransferEntry()
    {
        var p = V("p");
        var q = V("q");
        var entry = Seq(Q("if"), Sp, C("Bond", p, q), Sp, Q("then"), Sp, N(1), Sp, Q("else"), Sp, N(0));
        return All("p", Column(), All("q", Column(), Eq(Typed(C("T", p, q), Q("Int")), entry)));
    }

    private static Formula Continuations() => All("n", Q("Nat"),
        Eq(Typed(C("v", V("n")), Arrow(Column(), Q("Int"))), Power(V("n"))));

    private static Formula Recurrence()
    {
        Formula Readout(int shift) => Call("dotProduct", V("w"), C("v", Add(V("n"), N(shift))));
        var rhs = Add(Mul(6, Readout(10)), Mul(31, Readout(9)));
        rhs = Sub(Sub(rhs, Mul(97, Readout(8))), Mul(163, Readout(7)));
        rhs = Add(Add(rhs, Mul(417, Readout(6))), Mul(93, Readout(5)));
        rhs = Add(Sub(rhs, Mul(514, Readout(4))), Mul(192, Readout(3)));
        rhs = Sub(Add(rhs, Mul(72, Readout(2))), Mul(36, Readout(1)));
        return All("w", Arrow(Column(), Q("Int")), All("n", Q("Nat"), Eq(Readout(11), rhs)));
    }

    private static Formula Step() => All("w",Arrow(Column(),Q("Int")),All("p",Column(),
        Eq(App(Call("Matrix.mulVec",C("T"),V("w")),V("p")),
            Call("List.sum",Call("List.map",V("w"),C("moves",V("p")))))));
    private static Formula Powers() => All("k",Fin(12),Eq(Power(Val(V("k"))),C("table",V("k"))));
}
