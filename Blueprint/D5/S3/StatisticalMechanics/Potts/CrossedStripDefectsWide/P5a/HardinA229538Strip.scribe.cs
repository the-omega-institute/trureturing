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
            Node("a",Count(),false,"The defect budget is one."),
            Node("residual",Residual(),false,"Budgets zero and one select the right and left summands respectively."),
            Node("transition_entry",TransitionEntry(),true,"A successor entry has the value one only for the column and residual budget produced by the cut."),
            Node("labelled_scale",LabelledScale(),true,"At widths at least two and with fewer than three defects, each canonical array has six labelled representatives. The subscript on literalCount gives the palette size."),
            Node("result",Recurrence(),true,"The order-twenty recurrence holds for every width at least twenty-three. Each natural count is cast to the integers before coefficients are applied."))));

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
    private static Formula D(string n,params Formula[] a) => Call("HardinA229538StripData."+n,a);
    private static Formula Own(string n,params Formula[] a) => Call("HardinA229538Strip."+n,a);
    private static Formula Count() => All("n",Q("Nat"),
        Eq(Own("a",V("n")),Own("canonicalCount",N(1),V("n"))));

    private static Formula CanonicalCount() {
        var n=V("n");var a=V("A");var cells=Product(Fin(5),Fin(n));
        Formula idx(Formula p)=>Add(Mul(Val(Call("Prod.fst",p)),n),Val(Call("Prod.snd",p)));
        var canonical=All("p",cells,All("c",Fin(3),Imp(Lt(V("c"),App(a,V("p"))),Ex("q",cells,And(Lt(idx(V("q")),idx(V("p"))),Eq(App(a,V("q")),V("c")))))));
        var cols=Call("List.ofFn",Fn("j",Fin(n),Fn("i",Fin(5),App(a,Pair(V("i"),V("j"))))));
        var empty=Typed(Q("Finset.empty"),Call("Finset",Product(Fin(5),Fin(5))));
        var arrays=Arrow(cells,Fin(3));
        var predicate=Fn("A",arrays,And(Eq(Call("DefectTransfer.defects",empty,D("edges"),cols),V("D")),canonical));
        var count=Call("Finset.card",Call("Finset.filter",predicate,Typed(Q("Finset.univ"),Call("Finset",arrays))));
        return All("D",Q("Nat"),All("n",Q("Nat"),Eq(Own("canonicalCount",V("D"),n),count)));
    }

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
        var cost=D("cost",p,q);
        var left=If(And(Le(cost,d),Eq(Own("residual",q,Sub(d,cost)),s)),N(1),N(0));
        var rhs=If(Eq(Call("Sum.elim",Q("id"),Q("id"),s),q),D("transfer",Own("residual",p,d),s),N(0));
        return All("p",Column(),All("q",Column(),All("d",Q("Nat"),Imp(Le(d,N(1)),
            All("s",Call("Sum",Column(),Column()),Eq(AsInt(left),rhs))))));
    }
    private static Formula LabelledScale() {
        var m=V("m");var d=V("D");var n=Add(m,N(1));
        var empty=Typed(Q("Finset.empty"),Call("Finset",Product(Fin(5),Fin(5))));
        var labelled=App(new Formula.Subscript(Q("DefectTransfer.literalCount"),N(3)),empty,D("edges"),d,n);
        return All("D",Q("Nat"),All("m",Q("Nat"),Imp(Le(N(1),m),Imp(Lt(d,N(3)),
            Eq(labelled,Mul(N(6),Own("canonicalCount",d,n)))))));
    }
}
