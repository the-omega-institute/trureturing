using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class UnboundedReturnCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], p);
    private static Formula And(params Formula[] p) { var r=p[^1]; for(var k=p.Length-2;k>=0;--k) r=new Formula.Logic(p[k],FormulaLogicOperator.And,r); return r; }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Add(Formula a, Formula b) => Call("add",a,b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply",a,b);
    private static Formula Pow(Formula a, Formula b) => Call("power",a,b);
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula If(Formula p, Formula a, Formula b) => Call("ifThenElse",p,a,b);
    private static Formula Card(Formula a) => Call("card",a);
    private static Formula Half(Formula a) => Call("halfWeight",a);
    private static Formula Words(Formula a) => Call("middleWords",a);
    private static Formula Count(Formula a) => Call("returnCount",a);
    private static Formula Cast(Formula a) => Call("toReal",a);
    private static Formula Lam(string n, Formula t, Formula p) => F.Seq(Open,I(n),Sp,Colon,Sp,t,Sp,Mapsto,Sp,p,Close);
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Word => Call("List",I("CuLetter"));
    private static Formula Lists => Call("List",I("Return"));
    private static Formula Empty => Call("nil",I("CuLetter"));
    private static Formula Alpha => I("alphaInfinity");
    private static Formula Log(Formula n) => Call("logb",D(2),Cast(Count(n)));
    private static Formula Term(int delay, Formula n) => delay == 3
        ? If(Le(D(3),n),Count(Sub(n,D(3))),D(0))
        : If(Le(D(1,0),n),Count(Sub(n,D(1,0))),D(0));
    private static DocumentBlock Node(string name, Formula p, string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("fib-unbounded-"+name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),
            H(name.Replace('_',' ')),StatementSource.FromAuthor(Disp(p)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create()
    {
        var n=I("n"); var w=I("w"); var x=I("x"); var xs=I("xs");
        var root=And(Lt(D(0),x),Lt(x,D(1)),Equal(Add(Pow(x,D(3)),Pow(x,D(1,0))),D(1)));
        var fiber=Call("subtype",Lam("xs",Lists,And(Call("ne",xs,Call("nil",I("Return"))),
            Equal(Call("listWeight",xs),Mul(D(2),n)))));
        var delayedWords=Call("union",If(Equal(n,D(0)),Call("singleton",Empty),Call("emptyFinset",Word)),
            Call("union",If(Le(D(3),n),Call("image",Lam("w",Word,Call("cons",I("u"),w)),Words(Sub(n,D(3)))),Call("emptyFinset",Word)),
            If(Le(D(1,0),n),Call("image",Lam("w",Word,Call("cons",I("c"),w)),Words(Sub(n,D(1,0)))),Call("emptyFinset",Word))));
        var window=And(All(Le(Mul(Cast(Count(n)),Pow(x,n)),Pow(x,D(1,3))),B("n",Nat)),
            All(Imp(Le(D(3,1),n),Le(Pow(x,D(4,0)),Mul(Cast(Count(n)),Pow(x,n)))),B("n",Nat)));
        var logBounds=And(Lt(D(0),Alpha),All(Imp(Le(D(3,1),n),And(Lt(D(0),Cast(Count(n))),
            Le(Sub(Mul(Mul(D(2),Alpha),Cast(n)),Mul(D(8,0),Alpha)),Log(n)),
            Le(Log(n),Sub(Mul(Mul(D(2),Alpha),Cast(n)),Mul(D(2,6),Alpha))))),B("n",Nat)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Positive return lists are in bijection with their weighted binary middle words.",H("Unbounded positive return counts"),Blocks(
            Paragraph(Text("A return has positive integer exponents m and r and contributes six m plus twenty r original windows. Execution order reverses the external source order: the nonempty execution word has the form c W u, corresponding to U W C externally. The existing maximal-run parser identifies every such word with exactly one positive return list. No bound on either exponent, block boundaries supplied to a decoder, or finite-memory language is assumed.")),
            Node("halfWeight",And(Equal(Half(Empty),D(0)),All(Equal(Half(Call("cons",I("c"),w)),Add(D(1,0),Half(w))),B("w",Word)),
                All(Equal(Half(Call("cons",I("u"),w)),Add(D(3),Half(w))),B("w",Word))),
                "The half length gives weight ten to c and three to u.",DescribeRole.Definition),
            Node("middleWords",All(Equal(Words(n),delayedWords),B("n",Nat)),
                "The finite set enumerates exactly the binary words with the specified half length. Its three branches distinguish the empty word and the first letter.",DescribeRole.Definition),
            Node("ReturnFiber",All(Equal(Call("ReturnFiber",n),fiber),B("n",Nat)),
                "Only nonempty actual positive return lists with original length twice n belong to this fiber.",DescribeRole.Definition),
            Node("returnCount",All(Equal(Count(n),Call("NatCard",Call("ReturnFiber",n))),B("n",Nat)),
                "The count is the cardinality of the original list fiber, independently of its word enumeration.",DescribeRole.Definition),
            Node("actual_count_middle",All(And(Call("Finite",Call("ReturnFiber",n)),Equal(Count(n),
                If(Le(D(1,3),n),Card(Words(Sub(n,D(1,3)))),D(0)))),B("n",Nat)),
                "The forced endpoints have half length thirteen. Removing them preserves weight and gives the finite middle-word dictionary; the inverse uses complete run decomposition."),
            Node("actual_count_recurrence",All(Equal(Count(n),Add(Add(Term(3,n),Term(10,n)),If(Equal(n,D(1,3)),D(1),D(0)))),B("n",Nat)),
                "The disjoint first-middle-letter partition subtracts three or ten. The empty middle contributes the pulse at thirteen. The guards implement zero extension, including indices below a delay."),
            Node("actual_count_support",All(Iff(Lt(D(0),Count(n)),Ex(Equal(n,Add(Add(D(1,3),Mul(D(3),I("a"))),Mul(D(1,0),I("b")))),B("a",Nat),B("b",Nat))),B("n",Nat)),
                "The exact support is thirteen plus the semigroup generated by three and ten. In particular thirty is unsupported, whereas every index from thirty-one onward is supported."),
            Node("actual_count_window",All(Imp(root,window),B("x",Real)),
                "Scaling the recurrence by x to the index gives a convex combination. All indices thirty-one through forty are positive; the complete ten-index window has lower bound x to the fortieth power, which strong induction preserves. The upper bound starts at the pulse x to the thirteenth power."),
            Node("criticalX",Equal(I("criticalX"),Call("choose",Ex(root,B("x",Real)))),
                "The radius is chosen in the open unit interval where its third and tenth powers sum to one. Continuity and the endpoint values zero and two establish existence.",DescribeRole.Definition),
            Node("alphaInfinity",Equal(Alpha,Call("divide",Call("negate",Call("logb",D(2),I("criticalX"))),D(2))),
                "Dividing the negative base-two radius logarithm by two converts half lengths to original-window lengths.",DescribeRole.Definition),
            Node("actual_count_log_bounds",logBounds,
                "The count is positive from thirty-one onward. Its base-two logarithm lies between twice alpha times n minus eighty alpha and twice alpha times n minus twenty-six alpha. These fixed errors apply on the even original-length lattice."),
            Node("actual_even_rate",And(Call("IsBigO",I("atTop"),Lam("n",Nat,Sub(Log(n),Mul(Mul(D(2),Alpha),Cast(n)))),
                Call("constantFunction",Nat,Real,D(1))),
                Call("Tendsto",Lam("n",Nat,Call("divide",Log(n),Mul(D(2),Cast(n)))),I("atTop"),Call("nhds",Alpha))),
                "The logarithmic error is bounded by a constant. Dividing the two explicit logarithmic bounds by twice n gives the limit alpha along the even original-length lattice. This limit counts the specified actual family."))));
    }
}
