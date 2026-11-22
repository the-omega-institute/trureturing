using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a;

internal sealed class HardinA229538StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538Strip.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical one-defect colourings of five-row HDA arrays", H("Canonical one-defect colourings of five-row HDA arrays"), Blocks(
            Paragraph(Text("Colours are introduced in row-major order. At the widths used in the recurrence, each canonical array has six distinct label permutations.")),
            Node("canonicalCount",CanonicalCount(),false,"The filter counts five-by-n arrays with exactly D monochromatic bonds and row-major canonical colour introduction."),
            Node("a",Count(),false,"The column-sweep count uses defect budget one."),
            Node("residual",Residual(),false,"Budgets zero and one select the right and left summands respectively."),
            Node("transition_entry",TransitionEntry(),true,"A successor entry has the value one only for the column and residual budget produced by the cut."),
            Node("labelled_scale",LabelledScale(),true,"At widths at least two and with fewer than three defects, each canonical array has six labelled representatives. The subscript on literalCount gives the palette size."),
            Paragraph(Text("Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.")),
            Node("edges",Edges(),false,"The oriented cut is the set of pairs of row indices that form a bond between columns zero and one."),
            Node("cost",Cost(),false,"The cost is the number of monochromatic bonds on the cut between two decoded columns."),
            Node("bondDefects_empty",BondDefectsEmpty(),true,"The number of monochromatic bonds of a row against itself over the empty edge set is zero."),
            Node("cost_zero",ZeroCost(),true,"A cut has cost zero exactly when every bond has different colours at its endpoints."),
            Node("zero_cost_entry",ZeroCostEntry(),true,"The proper-colouring transfer entry is the indicator of a cut without monochromatic bonds."),
            Node("oneDefect",OneDefect(),false,"Each entry is the indicator of a cut with exactly one monochromatic bond."),
            Node("transfer",Transfer(),false,"The two summands represent one and zero residual defects. A zero-cost cut preserves the budget and a cut of cost one moves from the first summand to the second."),
            Node("terminal",Terminal(),false,"The empty continuation completes an array exactly when its remaining budget is zero."),
            Node("transfer_readout",TransferReadout(),true,"The state type belongs to an arbitrary universe. A vector recurrence for a matrix and terminal vector gives a shifted scalar recurrence for every readout vector."),
            Node("countCut",CountCut(),false,"The cost counts the colour coincidences at the thirteen oriented pairs of row positions."),
            Node("cost_countCut",CutEquality(),true,"The sum of the thirteen indicators equals the number of monochromatic bonds on the cut."),
            Node("movesOne",Moves(),false,"The list consists of the successor columns with cut cost one, in increasing column-code order."),
            Node("step_one",StepOne(),true,"The action of the exact-one-cut matrix is a sum over its successors."),
            Node("weights",Weights(),false,"The identity selects the first twelve rows. The row at exponent twelve appends the proper-colouring coefficients to two zeros. The remaining rows are stored in a lookup of shape Fin 10 × Fin 12 and satisfy the displayed recurrence. Each recursive exponent is strictly below the current exponent and below 23."),
            Node("classIndex",ClassIndex(),false,"The lookup classifies five-entry boundary columns under colour permutation and row reversal."),
            Node("tableOne",TableOne(),false,"The stored lookup has shape Fin 23 × Fin 25, with row n and column classIndex(p). The displayed entry is the left-summand projection of the continuation vector at exponent n."),
            Node("zeroValues",ZeroValues(),false,"For larger exponents the zero-defect values are linear combinations of the twelve proper-colouring vectors."),
            Node("weight_eq",WeightEquality(),true,"The same coefficient formula also holds at the tabulated exponents."),
            Node("zero_values",PowerZero(),true,"The reconstructed value is the proper-colouring continuation vector at each exponent."),
            Node("table_powers",TablePowers(),true,"The first coordinate gives the one-defect continuations and the second gives the inherited proper-colouring continuations."),
            Node("coefficients538",Coefficients(),false,"The entries are ordered from the smallest shift of the recurrence to the largest."),
            Node("vector_polynomial",Polynomial(),true,"The relation holds simultaneously for all boundary columns and both residual budgets."),
            Node("result",Recurrence(),true,"The transfer counts labelled arrays by adjacent column cuts. The six-to-one count in labelled_scale identifies that readout with six times a at the widths of the recurrence. Cancelling six in the integer readout gives the order-twenty recurrence for every width at least twenty-three."))));

    private static DocumentBlock Node(string name, Formula statement, bool theorem, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(name), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229538")),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula Pair(Formula a,Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Product(Formula a,Formula b) => Seq(Parenthesized(a),Times,Parenthesized(b));
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Subtract,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Multiply,Parenthesized(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Ex(string n,Formula t,Formula b) => Seq(Exists,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Fn(string n,Formula t,Formula b) => Parenthesized(Seq(LambdaLower,Sp,Typed(V(n),t),Mapsto,Sp,Parenthesized(b)));
    private static Formula If(Formula c,Formula a,Formula b) =>
        Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,a,Sp,Q("else"),Sp,b));
    private static Formula AsInt(Formula a) => Typed(a,Q("Int"));
    private static Formula Column() => Q("HardinA233178Chromatic.Column");
    private static Formula Own(string n,params Formula[] a) => Call("HardinA229538Strip."+n,a);
    private static Formula Count() => All("n",Q("Nat"),
        Eq(Typed(Own("a",V("n")),Q("Nat")),Own("canonicalCount",N(1),V("n"))));

    private static Formula CutEdges() {
        var pairs = Product(Fin(5),Fin(5));
        var r = Val(V("r"));
        var s = Val(V("s"));
        var adjacent = new Formula.Logic(Eq(s,Add(r,N(1))),FormulaLogicOperator.Or,Eq(r,Add(s,N(1))));
        var predicate = new Formula.Logic(Eq(s,r),FormulaLogicOperator.Or,adjacent);
        var filter = Parenthesized(Seq(LambdaLower,Sp,Typed(Pair(V("r"),V("s")),pairs),
            Mapsto,Sp,Parenthesized(predicate)));
        return Call("Finset.filter",filter,Typed(Q("Finset.univ"),Call("Finset",pairs)));
    }

    private static Formula FilteredCount(Formula n, Formula budget) {
        var a=V("A");var cells=Product(Fin(5),Fin(n));
        Formula idx(Formula p)=>Add(Mul(Val(Call("Prod.fst",p)),n),Val(Call("Prod.snd",p)));
        var canonical=All("p",cells,All("c",Fin(3),Imp(Lt(V("c"),App(a,V("p"))),Ex("q",cells,And(Lt(idx(V("q")),idx(V("p"))),Eq(App(a,V("q")),V("c")))))));
        var cols=Call("List.ofFn",Fn("j",Fin(n),Fn("i",Fin(5),App(a,Pair(V("i"),V("j"))))));
        var empty=Typed(Q("Finset.empty"),Call("Finset",Product(Fin(5),Fin(5))));
        var arrays=Arrow(cells,Fin(3));
        var cut=CutEdges();
        var predicate=Fn("A",arrays,And(Eq(Call("DefectTransfer.defects",empty,cut,cols),budget),canonical));
        return Call("Finset.card",Call("Finset.filter",predicate,Typed(Q("Finset.univ"),Call("Finset",arrays))));
    }

    private static Formula CanonicalCount() => All("D",Q("Nat"),All("n",Q("Nat"),
        Eq(Own("canonicalCount",V("D"),V("n")),FilteredCount(V("n"),V("D")))));

    private static Formula Recurrence() {
        Formula a(int j)=>AsInt(Own("a",Add(V("n"),N(j))));
        long[] coefficients=[12, 26, -566, -123, 8804, -4121, -59620, 55115, 183692, -256127, -211910, 498819, -48036, -371692, 214008, 43848, -64656, 8640, 5184, -1296];
        Formula rhs=Mul(N(coefficients[0]),a(22));
        for(int i=1;i<coefficients.Length;i++)
            rhs=coefficients[i]<0 ? Sub(rhs,Mul(N(-coefficients[i]),a(22-i)))
                : Add(rhs,Mul(N(coefficients[i]),a(22-i)));
        return All("n",Q("Nat"),Eq(a(23),rhs));
    }

    private static Formula Le(Formula x,Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Residual() => All("p",Column(),All("d",Q("Nat"),
        Eq(Typed(Own("residual",V("p"),V("d")),Call("Sum",Column(),Column())),
            If(Eq(V("d"),N(0)),Call("Sum.inr",V("p")),Call("Sum.inl",V("p"))))));
    private static Formula TransitionEntry() {
        var p=V("p");var q=V("q");var d=V("d");var s=V("s");
        var cost=Own("cost",p,q);
        var left=If(And(Le(cost,d),Eq(Own("residual",q,Sub(d,cost)),s)),N(1),N(0));
        var rhs=If(Eq(Call("Sum.elim",Q("id"),Q("id"),s),q),Own("transfer",Own("residual",p,d),s),N(0));
        return All("p",Column(),All("q",Column(),All("d",Q("Nat"),Imp(Le(d,N(1)),
            All("s",Call("Sum",Column(),Column()),Eq(AsInt(left),rhs))))));
    }
    private static Formula LabelledScale() {
        var m=V("m");var d=V("D");var n=Add(m,N(1));
        var empty=Typed(Q("Finset.empty"),Call("Finset",Product(Fin(5),Fin(5))));
        var cut=CutEdges();
        var labelled=App(new Formula.Subscript(Q("DefectTransfer.literalCount"),N(3)),empty,cut,d,n);
        return All("D",Q("Nat"),All("m",Q("Nat"),Imp(Le(N(1),m),Imp(Lt(d,N(3)),
            Eq(labelled,Mul(N(6),Own("canonicalCount",d,n)))))));
    }

    private static Formula SumOver(string n,Formula t,Formula body) =>
        Seq(F.Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(body));
    private static Formula Pow(Formula a,Formula b) => Seq(Parenthesized(a),Caret,Grp(b));


    private static Formula VectorLiteral(long[] entries)
    {
        Formula tail = Q("Matrix.vecEmpty");
        for (int i = entries.Length - 1; i >= 0; i--)
            tail = Call("Matrix.vecCons", N(entries[i]), tail);
        return tail;
    }
    private static Formula Columns() => Call("Sum",Column(),Column());
    private static Formula M(Formula index) => Call("Matrix",index,index,Q("Int"));
    private static Formula C(string n,params Formula[] a) => Call("HardinA233178Chromatic."+n,a);

    private static Formula Coefficients() =>
        Eq(Typed(Own("coefficients538"),Arrow(Fin(20),Q("Int"))),VectorLiteral([-1296, 5184, 8640, -64656, 43848, 214008, -371692, -48036, 498819, -211910, -256127, 183692, 55115, -59620, -4121, 8804, -123, -566, 26, 12]));
    private static Formula Polynomial() {
        Formula Power(Formula n)=>Call("Matrix.mulVec",Pow(Own("transfer"),n),Own("terminal"));
        return Eq(Power(N(22)),SumOver("k",Fin(20),
            Call("SMul.smul",Own("coefficients538",V("k")),Power(Add(N(2),Val(V("k")))))));
    }

    private static Formula CountCut() {
        var p=V("p");var q=V("q");
        var bonds=new[]{new[]{0,0},new[]{0,1},new[]{1,0},new[]{1,1},new[]{1,2},new[]{2,1},new[]{2,2},new[]{2,3},new[]{3,2},new[]{3,3},new[]{3,4},new[]{4,3},new[]{4,4}};
        var terms=bonds.Select(e=>If(Eq(C("colour",p,N(e[0])),C("colour",q,N(e[1]))),N(1),N(0)));
        return All("p",Column(),All("q",Column(),Eq(Typed(Own("countCut",p,q),Q("Nat")),terms.Aggregate(Add))));
    }
    private static Formula CutEquality() => All("p",Column(),All("q",Column(),Eq(Own("cost",V("p"),V("q")),
        Own("countCut",V("p"),V("q")))));
    private static Formula Moves()
    {
        var p = V("p");
        var q = V("q");
        var predicate = Parenthesized(Seq(LambdaLower, Sp, Typed(q, Column()), Mapsto, Sp,
            Call("decide", Eq(Own("cost", p, q), N(1)))));
        return All("p", Column(), Eq(Typed(Own("movesOne", p), Call("List", Column())),
            Call("List.filter", predicate, Call("List.finRange", N(243)))));
    }
    private static Formula StepOne() => All("w",Arrow(Column(),Q("Int")),All("p",Column(),
        Eq(App(Call("Matrix.mulVec",Own("oneDefect"),V("w")),V("p")),
            Call("List.sum",Call("List.map",V("w"),Own("movesOne",V("p")))))));
    private static Formula Weights()
    {
        var n = V("n");
        var j = V("j");
        var h = V("h");
        var k = V("k");
        var exponent = Val(n);
        var identity = Typed(N(1), M(Fin(12)));
        var initial = App(identity, Call("Fin.castLT", n, h), j);
        var atTwelve = App(Call("Fin.append", Typed(N(0), Arrow(Fin(2), Q("Int"))),
            C("coefficients")), j);
        var previousExponent = Add(new Formula.Binary(exponent, FormulaBinaryOperator.Subtract, N(10)), Val(k));
        var later = SumOver("k", Fin(10), Mul(C("coefficients", k),
            Own("weights", Call("Fin.ofNat", N(23), previousExponent), j)));
        var value = If(Typed(h, Lt(exponent, N(12))), initial,
            If(Eq(exponent, N(12)), atTwelve, later));
        return All("n", Fin(23), All("j", Fin(12), Eq(AsInt(Own("weights", n, j)), value)));
    }

    private static Formula ClassIndex()
    {
        var p = V("p");
        var decoded = Call("HardinA233178Recurrence.columnEquiv", p);
        var digits = Parenthesized(Seq(App(decoded, N(0)), Comma, Sp, App(decoded, N(1)),
            Comma, Sp, App(decoded, N(2)), Comma, Sp, App(decoded, N(3)), Comma, Sp, App(decoded, N(4))));
        var colorClass = Call("HardinA233260Literal.cls", digits);
        var reversalClass = Typed(VectorLiteral([0, 1, 2, 3, 4, 5, 6, 7, 8, 3, 9, 10, 11, 12, 2, 13, 14, 15, 6, 16, 17, 18, 11, 8, 13, 19, 20, 1, 21, 22, 14, 9, 10, 23, 18, 24, 7, 16, 22, 19, 4]),
            Arrow(Fin(41), Fin(25)));
        return All("p", Column(), Eq(Typed(Own("classIndex", p), Fin(25)), App(reversalClass, colorClass)));
    }

    private static Formula TableOne()
    {
        var n = V("n");
        var p = V("p");
        var continuation = Call("Matrix.mulVec", Pow(Own("transfer"), Val(n)), Own("terminal"));
        return All("n", Fin(23), All("p", Column(),
            Eq(AsInt(Own("tableOne", n, p)), App(continuation, Call("Sum.inl", p)))));
    }

    private static Formula Expansion() => SumOver("j",Fin(12),
        Mul(Own("weights",V("n"),V("j")),C("table",V("j"),V("p"))));
    private static Formula ZeroValues() => All("n",Fin(23),All("p",Column(),Eq(AsInt(Own("zeroValues",V("n"),V("p"))),
        If(Typed(V("h"),Lt(Val(V("n")),N(12))),C("table",Call("Fin.castLT",V("n"),V("h")),V("p")),Expansion()))));
    private static Formula WeightEquality() => All("n",Fin(23),Eq(Own("zeroValues",V("n")),
        SumOver("j",Fin(12),Call("SMul.smul",Own("weights",V("n"),V("j")),C("table",V("j"))))));
    private static Formula OldPower(Formula n) => Call("Matrix.mulVec",Pow(C("T"),n),Typed(N(1),Arrow(Column(),Q("Int"))));
    private static Formula PowerZero() => All("n",Fin(23),Eq(Own("zeroValues",V("n")),OldPower(Val(V("n")))));
    private static Formula TablePowers() {
        var n=V("n");
        return All("n",Fin(23),Eq(Call("Matrix.mulVec",Pow(Own("transfer"),Val(n)),Own("terminal")),
            Call("Sum.elim",Own("tableOne",n),OldPower(Val(n)))));
    }

    private static Formula Edges() {
        var pairs = Product(Fin(5),Fin(5));
        var r = Call("Fin.val",V("r"));
        var s = Call("Fin.val",V("s"));
        var adjacent = new Formula.Logic(Eq(s,Add(r,N(1))),FormulaLogicOperator.Or,Eq(r,Add(s,N(1))));
        var predicate = new Formula.Logic(Eq(s,r),FormulaLogicOperator.Or,adjacent);
        var filter = Parenthesized(Seq(LambdaLower,Sp,Typed(Pair(V("r"),V("s")),pairs),
            Mapsto,Sp,Parenthesized(predicate)));
        var universe = Typed(Q("Finset.univ"),Call("Finset",pairs));
        return Eq(Typed(Own("edges"),Call("Finset",pairs)),Call("Finset.filter",filter,universe));
    }
    private static Formula Cost() {
        Formula Decode(string n)=>Call("HardinA233178Recurrence.columnEquiv",V(n));
        return All("p",Column(),All("q",Column(),Eq(Typed(Own("cost",V("p"),V("q")),Q("Nat")),
            Call("DefectTransfer.bondDefects",Own("edges"),Decode("p"),Decode("q")))));
    }
    private static Formula BondDefectsEmpty() {
        var row = V("r");
        var empty = Typed(Q("Finset.empty"),Call("Finset",Product(Fin(5),Fin(5))));
        return All("r",Arrow(Fin(5),Fin(3)),Eq(Call("DefectTransfer.bondDefects",empty,row,row),N(0)));
    }
    private static Formula ZeroCost() => All("p",Column(),All("q",Column(),
        new Formula.Logic(Parenthesized(Eq(Own("cost",V("p"),V("q")),N(0))),
            FormulaLogicOperator.Iff,Parenthesized(C("Bond",V("p"),V("q"))))));
    private static Formula ZeroCostEntry() => All("p",Column(),All("q",Column(),
        Eq(If(Eq(Own("cost",V("p"),V("q")),N(0)),AsInt(N(1)),N(0)),C("T",V("p"),V("q")))));
    private static Formula OneDefect() => All("p",Column(),All("q",Column(),
        Eq(AsInt(Own("oneDefect",V("p"),V("q"))),If(Eq(Own("cost",V("p"),V("q")),N(1)),N(1),N(0)))));
    private static Formula Transfer() => Eq(Typed(Own("transfer"),M(Columns())),
        Call("Matrix.fromBlocks",C("T"),Own("oneDefect"),Typed(N(0),M(Column())),C("T")));
    private static Formula Terminal() => Eq(Typed(Own("terminal"),Arrow(Columns(),Q("Int"))),
        Call("Sum.elim",Typed(N(0),Arrow(Column(),Q("Int"))),Typed(N(1),Arrow(Column(),Q("Int")))));

    private static Formula TransferReadout() {
        var state=V("S");var matrix=V("M");var u=V("u");var v=V("v");
        var d=V("d");var b=V("b");var n=V("n");var j=V("j");
        var index=Call("Fin",d);
        var vectors=Arrow(state,Q("Int"));
        Formula power(Formula k)=>Call("Matrix.mulVec",Pow(matrix,k),u);
        Formula coefficient()=>new Formula.Apply(V("c"),[j]);
        Formula read(Formula k)=>Call("dotProduct",v,power(k));
        var premise=Eq(power(Add(b,d)),SumOver("j",index,
            Call("SMul.smul",coefficient(),power(Add(b,Call("Fin.val",j))))));
        var shifted=Add(n,b);
        var conclusion=Eq(read(Add(shifted,d)),SumOver("j",index,
            Mul(coefficient(),read(Add(shifted,Call("Fin.val",j))))));
        var implication=new Formula.Logic(Parenthesized(premise),FormulaLogicOperator.Implies,
            Parenthesized(All("n",Q("Nat"),conclusion)));
        var parameters=All("M",M(state),All("u",vectors,All("v",vectors,All("d",Q("Nat"),
            All("b",Q("Nat"),All("c",Arrow(index,Q("Int")),implication))))));
        return All("S",Seq(Q("Type"),Star),Seq(OpenBracket,Call("Fintype",state),CloseBracket,Sp,
            OpenBracket,Call("DecidableEq",state),CloseBracket,Sp,parameters));
    }
}
