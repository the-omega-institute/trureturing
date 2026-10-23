using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class ScalarCycleRowErrorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.";

    public DocumentDefinition Create()
    {
        Formula v=V("V"), bset=V("B"), t=V("T"), p=V("p"), q=V("Q"),
            x=V("x"), y=V("y"), a=V("a"), b=V("b"), f=V("f"), g=V("g"),
            eta=V("eta"), k=V("k"), hk=V("hk"), he=V("he"), r=C("Real");
        Formula mass=Call("mass",t,x), c=Call("conductance",t,x,y), kill=Call("killing",t,x);
        Formula adj=Call("Adj",Call("graph",t),x,y), px=App(p,x);
        Formula rate=Call("labelRate",t,p,x,b), qr=Call("rate",q,px,b);
        Formula error=Abs(Sub(rate,qr));
        Formula gen=Sub(SumOver("y",v,If(adj,Mul(Div(c,mass),Sub(App(f,y),App(f,x))),D(0))),Mul(kill,App(f,x)));
        Formula label=SumOver("y",v,If(And(adj,Eq(App(p,y),b)),Div(c,mass),D(0)));
        Formula nu=SumOver("x",v,If(Eq(px,a),mass,D(0)));
        Formula conductance=SumOver("x",v,If(Eq(px,a),SumOver("y",v,
            If(And(adj,Eq(App(p,y),b)),c,D(0))),D(0)));
        Formula compressed=Call("compression",t,p);
        Formula compressedRates=And(All("a",bset,All("b",bset,Eq(Call("rate",compressed,a,b),
            Div(SumOver("x",v,If(Eq(px,a),Mul(mass,rate),D(0))),Call("inducedMass",t,p,a))))),
            All("a",bset,Eq(Call("killing",compressed,a),
                Div(SumOver("x",v,If(Eq(px,a),Mul(mass,kill),D(0))),Call("inducedMass",t,p,a)))));
        Formula cycle=Ex("n",C("Nat"),Ex("i",Fn(Call("Fin",Add(V("n"),D(3))),bset),
            And(Call("Injective",V("i")),All("a",Call("Fin",Add(V("n"),D(3))),
                All("b",Call("Fin",Add(V("n"),D(3))),Imp(Call("Adj",Call("cycleGraph",Add(V("n"),D(3))),a,b),
                    Le(eta,Call("rate",q,App(V("i"),a),App(V("i"),b)))))))));
        Formula lower=FiniteBind(All("T",Call("TreeData",v),All("p",Fn(v,bset),
            Imp(Call("Surjective",p),All("Q",Call("KilledGenerator",bset),All("eta",r,
                Imp(And(Lt(D(0),eta),Call("CycleRates",q,eta)),Le(eta,Call("delta",t,p,q)))))))));
        Formula path=Call("sharpPath",k,eta), fold=Call("endpointFold",k), pq=Call("compression",path,fold);
        Formula cyc=Call("Adj",Call("cycleGraph",k),a,b);
        Formula allSharp=Eq(Call("delta",path,fold,pq),eta);
        allSharp=And(All("f",Fn(Call("Fin",k),r),All("a",Call("Fin",k),Eq(Call("coarseAction",pq,f,a),Call("massAverage",path,fold,Call("generator",path,Compose(f,fold)),a)))),allSharp);
        allSharp=And(All("b",Call("Fin",k),Eq(Call("labelRate",path,fold,Call("last",k),b),If(Eq(Add(Call("val",b),D(1)),k),Mul(D(2),eta),D(0)))),allSharp);
        allSharp=And(All("b",Call("Fin",k),Eq(Call("labelRate",path,fold,D(0),b),If(Eq(Call("val",b),D(1)),Mul(D(2),eta),D(0)))),allSharp);
        allSharp=And(All("a",Call("Fin",k),All("b",Call("Fin",k),Imp(Ne(a,D(0)),Eq(Call("labelRate",path,fold,Call("castSucc",a),b),Call("rate",pq,a,b))))),allSharp);
        allSharp=And(All("x",Call("Fin",Add(k,D(1))),All("b",Call("Fin",k),Le(Abs(Sub(Call("labelRate",path,fold,x,b),Call("rate",pq,App(fold,x),b))),eta))),allSharp);
        allSharp=And(Ex("a",Call("Fin",k),Ex("b",Call("Fin",k),And(cyc,Eq(Call("rate",pq,a,b),eta)))),allSharp);
        allSharp=And(Call("CycleRates",pq,eta),allSharp);
        allSharp=And(All("a",Call("Fin",k),Eq(Call("killing",pq,a),D(0))),allSharp);
        allSharp=And(All("a",Call("Fin",k),All("b",Call("Fin",k),Eq(Call("rate",pq,a,b),If(cyc,If(Eq(a,D(0)),eta,Mul(D(2),eta)),D(0))))),allSharp);
        allSharp=And(All("a",Call("Fin",k),All("b",Call("Fin",k),Eq(Call("inducedConductance",path,fold,a,b),If(cyc,Mul(D(2),eta),D(0))))),allSharp);
        allSharp=And(All("a",Call("Fin",k),Eq(Call("inducedMass",path,fold,a),If(Eq(a,D(0)),D(2),D(1)))),allSharp);
        allSharp=And(Call("Surjective",fold),allSharp);
        Formula sharp=All("k",C("Nat"),All("hk",Le(D(3),k),All("eta",r,All("he",Lt(D(0),eta),allSharp))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual rows of a positively weighted finite tree cannot uniformly approximate a positive bidirectional simple cycle below its least directed rate; endpoint folding attains the bound for every cycle size.",
            H("Weighted-tree cycle row error and sharp constant one"),Blocks(
            Node("tree","Original positive tree data","TreeData",All("V",C("Type"),
                Seq(Call("TreeData",v),Colon,C("Type"))),
                "TreeData consists of an actual simple tree, positive real mass at each original vertex, symmetric conductances positive on every edge, and arbitrary nonnegative killing. Conductance values off edges are unused. The theorem concerns finite carriers; connectedness supplies nonemptiness. Fibres need not be connected.",DescribeRole.Definition),
            Node("coarse","Killed coarse generators","KilledGenerator",All("B",C("Type"),
                Seq(Call("KilledGenerator",bset),Colon,C("Type"))),
                "A killed generator stores arbitrary nonnegative off-diagonal rates and nonnegative killing. Its diagonal rate field has no effect on its action, since it multiplies a zero difference.",DescribeRole.Definition),
            Node("generator","The original backward generator","generator",FiniteBind(All("T",Call("TreeData",v),All("f",Fn(v,r),All("x",v,Eq(Call("generator",t,f,x),gen))))),
                "Only actual neighbours contribute. Division is by the original vertex mass, with no time rescaling; killing is subtracted in the same clock.",DescribeRole.Definition),
            Node("rows","Actual off-label row sums","labelRate",DataBind(All("x",v,All("b",bset,Eq(rate,label)))),
                "The sum runs over every original vertex, retaining exactly actual neighbours with the requested label. No quotient-edge multiplicity or displayed proxy matrix replaces these rows.",DescribeRole.Definition),
            Node("delta","Uniform off-label error","delta",DataBind(All("Q",Call("KilledGenerator",bset),
                Eq(Call("delta",t,p,q),Seq(new Formula.Subscript(Max,Seq(Mem(x,v),Comma,Mem(b,bset))),Sp,If(Ne(b,px),error,D(0)))))),
                "The finite maximum contains every original vertex row. Same-label entries are assigned zero; the nonnegative finite supremum has bottom zero, so an empty off-label maximum is zero.",DescribeRole.Definition),
            Node("mass","Induced masses","inducedMass",DataBind(All("a",bset,Eq(Call("inducedMass",t,p,a),nu))),
                "Each label mass is the sum of the original positive masses in its fibre.",DescribeRole.Definition),
            Node("conductance","Induced conductances","inducedConductance",DataBind(All("a",bset,All("b",bset,Eq(Call("inducedConductance",t,p,a,b),conductance)))),
                "Actual conductances are summed over ordered edges from the first class to the second. No missing edge is inserted.",DescribeRole.Definition),
            Node("compression","Literal mass-weighted compression","compression",DataBind(compressedRates),
                "Rates average the actual original row sums with original masses; killing is averaged with the same masses. The generator action identity in the sharpness theorem proves that this is the literal compression of G on pulled-back label functions. Empty fibres are permitted in the definition; all theorem label maps are onto.",DescribeRole.Definition),
            Node("action","Coarse backward action","coarseAction",FiniteBind(All("Q",Call("KilledGenerator",bset),All("f",Fn(bset,r),All("a",bset,
                Eq(Call("coarseAction",q,f,a),Sub(SumOver("b",bset,Mul(Call("rate",q,a,b),Sub(App(f,b),App(f,a)))),Mul(Call("killing",q,a),App(f,a)))))))),
                "Diagonal rates cancel. This action includes the complete killed diagonal through the rate differences and killing term.",DescribeRole.Definition),
            Node("average","Original mass average","massAverage",DataBind(All("g",Fn(v,r),All("a",bset,
                Eq(Call("massAverage",t,p,g,a),Div(SumOver("x",v,If(Eq(px,a),Mul(mass,App(g,x)),D(0))),Call("inducedMass",t,p,a)))))),
                "This is the original-mass average of a vertex function on a label class.",DescribeRole.Definition),
            Node("cycle","Every direction of a full simple cycle","CycleRates",FiniteBind(All("Q",Call("KilledGenerator",bset),All("eta",r,
                Iff(Call("CycleRates",q,eta),cycle)))),
                "An injective cyclic list has length n+3, hence at least three. Both ordered directions of every cycle edge satisfy the lower bound, while all other labels and rates remain arbitrary.",DescribeRole.Definition),
            Node("lower","Universal actual-tree lower bound","cycle_row_error_lower_bound",lower,
                "Restrict the original tree to vertices carrying cycle labels. If every such vertex had a neighbour of each adjacent cycle label, cycle degree two and injectivity would give two distinct actual neighbours at every vertex of this induced forest. A finite nonempty forest component has a leaf, a contradiction. Thus an actual original row misses an adjacent cycle class, has row sum zero there, and differs from its specified coarse rate by at least eta. No missing-neighbour hypothesis, connected-fibre hypothesis, diagonal condition or killing equality is assumed.",DescribeRole.Theorem),
            Node("path","The entire sharp path family","sharpPath",All("k",C("Nat"),All("eta",r,All("he",Lt(D(0),eta),
                And(Eq(Call("graph",path),Call("pathGraph",Add(k,D(1)))),
                    All("x",Call("Fin",Add(k,D(1))),And(Eq(Call("mass",path,x),D(1)),And(
                        Eq(Call("killing",path,x),D(0)),All("y",Call("Fin",Add(k,D(1))),
                            Eq(Call("conductance",path,x,y),Mul(D(2),eta)))))))))),
                "There are k+1 original vertices and k edges. Every original mass is one, every edge conductance is 2 eta, and killing vanishes. Positivity follows for every real eta>0.",DescribeRole.Definition),
            Node("fold","Endpoint-folding labels","endpointFold",All("k",C("Nat"),All("hk",Lt(D(0),k),All("x",Call("Fin",Add(k,D(1))),
                Eq(App(fold,x),If(Lt(Call("val",x),k),Call("val",x),D(0)))))),
                "Vertices zero through k-1 retain their indices; vertex k receives label zero. The zero fibre consists of the two endpoints and is disconnected for k>=3.",DescribeRole.Definition),
            Node("sharp","All sizes and scales attain the bound","endpoint_folding_sharpness",sharp,
                "For each integer k>=3 and real eta>0, the indicated literal compression has mass two at zero and one elsewhere, conductance 2 eta on every cycle edge, rate eta out of zero and 2 eta out of every other label. Every directed cycle rate is at least eta and a rate out of zero equals eta. Every internal original row agrees with Q. At the first endpoint the only nonzero row entry is 2 eta toward label one; at the last it is 2 eta toward label k-1. Both endpoint errors are bounded by eta, as are all rows, and the universal lower bound gives exact delta=eta. The full operator compression identity is included. This establishes sharpness in the unrestricted weighted-tree comparison class; it makes no fixed native orbit, native-operation, physical-space, or arbitrary memory/encoding assertion.",DescribeRole.Theorem),
            Node("complete","The complete cycle obstruction and optimal constant","cycle_row_error_and_sharpness",And(lower,sharp),
                "The complete statement combines the universal lower bound with the full endpoint-folding construction for every k>=3 and every eta>0. Both clauses use the same original generator, actual row norm, masses and clock described above.",DescribeRole.Theorem))));
    }
    private static DocumentBlock Node(string id,string title,string name,Formula formula,string prose,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("scalar-cycle-"+id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);
    private static Formula Mem(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula V(string s)=>F.Id(s);
    private static Formula C(string s)=>Seq(Operatorname,Grp(V(s)));
    private static Formula Call(string s,params Formula[] a)=>new Formula.Apply(C(s),[..a]);
    private static Formula App(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula Fn(Formula a,Formula b)=>new Formula.TypeArrow(a,b);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Ex(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Lt(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Div(Formula a,Formula b)=>Seq(Frac,Grp(a),Grp(b));
    private static Formula Abs(Formula a)=>Seq(Lvert,a,Rvert);
    private static Formula If(Formula h,Formula a,Formula b)=>Call("ite",h,a,b);
    private static Formula Compose(Formula a,Formula b)=>Seq(a,Circ,b);
    private static Formula SumOver(string s,Formula t,Formula body)=>Seq(new Formula.Subscript(Sum,Mem(V(s),t)),Sp,body);
    private static Formula FiniteBind(Formula body)=>All("V",C("Type"),All("B",C("Type"),
        Seq(OpenBracket,Call("Fintype",V("V")),CloseBracket,Sp,OpenBracket,Call("Fintype",V("B")),CloseBracket,Sp,body)));
    private static Formula DataBind(Formula body)=>FiniteBind(All("T",Call("TreeData",V("V")),All("p",Fn(V("V"),V("B")),body)));
}
