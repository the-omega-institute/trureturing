using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a;

internal sealed class HardinA229641StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641Strip.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical two-defect colourings of five-row HDA arrays", H("Canonical two-defect colourings of five-row HDA arrays"), Blocks(
            Paragraph(Text("Colours are introduced in row-major order. At the widths used in the recurrence, each canonical array has six distinct label permutations.")),
            Node("a",Count(),false,"The filter counts all literal five-by-n arrays with exactly two monochromatic horizontal, diagonal or antidiagonal bonds and canonical colour introduction."),
            Paragraph(Text("Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.")),
            Node("twoDefect", TwoDefect(), false, "This entry is one exactly when a cut contains two monochromatic bonds."),
            Node("transfer", Transfer(), false, "The left summand has budget two. The inherited right summand has budgets one and zero."),
            Node("terminal", Terminal(), false, "An empty continuation requires a remaining budget of zero."),
            Node("coefficients641",Coefficients(),false,"The entries are ordered from the smallest shift of the recurrence to the largest."),
            Node("vector_polynomial",Polynomial(),true,"The relation holds simultaneously for all boundary columns and all three residual budgets."),
            Node("result",Recurrence(),true,"The order-thirty recurrence holds for every width at least thirty-four. Each natural count is cast to the integers before coefficients are applied."))));

    private static DocumentBlock Node(string name, Formula statement, bool theorem, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(name), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229641")),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Subtract,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Multiply,Parenthesized(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula AsInt(Formula a) => Typed(a,Q("Int"));
    private static Formula Own(string n,params Formula[] a) => Call("HardinA229641Strip."+n,a);
    private static Formula Count() => All("n",Q("Nat"),
        Eq(Own("a",V("n")),FilteredCount(V("n"),N(2))));
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula Pair(Formula a,Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Product(Formula a,Formula b) => Seq(Parenthesized(a),Times,Parenthesized(b));
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Ex(string n,Formula t,Formula b) => Seq(Exists,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Fn(string n,Formula t,Formula b) => Parenthesized(Seq(LambdaLower,Sp,Typed(V(n),t),Mapsto,Sp,Parenthesized(b)));

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

    private static Formula Recurrence() {
        Formula a(int j)=>AsInt(Own("a",Add(V("n"),N(j))));
        long[] coefficients=[18, -15, -1191, 3468, 31983, -108707, -424479, 1614489, 2851598, -13478352, -7797810, 66347438, -12632640, -190067859, 147888798, 287096430, -412178619, -138135927, 522690894, -168525432, -273411640, 227616084, 9610272, -73617984, 21460464, 7359984, -4611168, 186624, 279936, -46656];
        Formula rhs=Mul(N(coefficients[0]),a(33));
        for(int i=1;i<coefficients.Length;i++)
            rhs=coefficients[i]<0 ? Sub(rhs,Mul(N(-coefficients[i]),a(33-i)))
                : Add(rhs,Mul(N(coefficients[i]),a(33-i)));
        return All("n",Q("Nat"),Eq(a(34),rhs));
    }

    private static Formula If(Formula c,Formula a,Formula b) =>
        Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,a,Sp,Q("else"),Sp,b));
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
    private static Formula Column() => Q("HardinA233178Chromatic.Column");
    private static Formula M(Formula s) => Call("Matrix",s,s,Q("Int"));
    private static Formula D(string n,params Formula[] a) => Call("HardinA229538Strip."+n,a);
    private static Formula C(string n,params Formula[] a) => Call("HardinA233178Chromatic."+n,a);

    private static Formula Coefficients() =>
        Eq(Typed(Own("coefficients641"),Arrow(Fin(30),Q("Int"))),VectorLiteral([-46656, 279936, 186624, -4611168, 7359984, 21460464, -73617984, 9610272, 227616084, -273411640, -168525432, 522690894, -138135927, -412178619, 287096430, 147888798, -190067859, -12632640, 66347438, -7797810, -13478352, 2851598, 1614489, -424479, -108707, 31983, 3468, -1191, -15, 18]));
    private static Formula Polynomial() {
        Formula Power(Formula n)=>Call("Matrix.mulVec",Pow(Own("transfer"),n),Own("terminal"));
        return Eq(Power(N(33)),SumOver("k",Fin(30),
            Call("SMul.smul",Own("coefficients641",V("k")),Power(Add(N(3),Val(V("k")))))));
    }

    private static Formula Budgets01() => Call("Sum",Column(),Column());
    private static Formula Budgets012() => Call("Sum",Column(),Budgets01());
    private static Formula TwoDefect() => All("p",Column(),All("q",Column(),
        Eq(AsInt(Own("twoDefect",V("p"),V("q"))),If(Eq(D("cost",V("p"),V("q")),N(2)),N(1),N(0)))));
    private static Formula Transfer() => Eq(Typed(Own("transfer"),M(Budgets012())),
        Call("Matrix.fromBlocks",C("T"),Call("Matrix.fromCols",D("oneDefect"),Own("twoDefect")),
            Typed(N(0),Call("Matrix",Budgets01(),Column(),Q("Int"))),D("transfer")));
    private static Formula Terminal() => Eq(Typed(Own("terminal"),Arrow(Budgets012(),Q("Int"))),
        Call("Sum.elim",Typed(N(0),Arrow(Column(),Q("Int"))),D("terminal")));
}
