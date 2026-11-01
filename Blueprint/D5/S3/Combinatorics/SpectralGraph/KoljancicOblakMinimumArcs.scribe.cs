using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class KoljancicOblakMinimumArcsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/koljancicoblak2026nssp");
    public DocumentDefinition Create()
    {
        Formula n=V("n"), e=V("E"), a=V("A"), x=V("X"), i=V("i"), j=V("j"), p=V("p");
        Formula obstruction=All("X", Mat(n), Imp(All("i", Fin(n), All("j", Fin(n),
            Eqn(Mul(App(a,i,j),App(x,i,j)),D(0)))), Imp(
            Eqn(Sub(Mul(a,Tr(x)),Mul(Tr(x),a)),D(0)),Eqn(x,D(0)))));
        Formula nssp=All("n",Nat(),All("A",Mat(n),Iff(Call("HasNSSP",a),obstruction)));
        Formula exact=All("n",Nat(),All("E",Edges(n),All("A",Mat(n),
            Iff(Call("ExactSupport",e,a),All("i",Fin(n),All("j",Fin(n),
                Iff(Ne(App(a,i,j),D(0)),Mem(Pair(i,j),e))))))));
        Formula requires=All("n",Nat(),All("E",Edges(n),Iff(Call("Requires",e),
            All("A",Mat(n),Imp(Call("ExactSupport",e,a),Call("HasNSSP",a))))));
        Formula whole=All("n",Nat(),Imp(Le(D(1),n),And(
            All("E",Edges(n),Imp(Call("Requires",e),Le(Min(n),Card(e)))),
            Exists("E",Edges(n),And(Call("Requires",e),Eqn(Card(e),Min(n)))))));
        Formula connection=All("n",Nat(),All("E",Edges(n),Iff(Call("ConnectedSupport",e),
            All("p",Fn(Fin(n),C("Real")),Imp(All("u",e,
                Eqn(App(p,Call("fst",V("u"))),App(p,Call("snd",V("u"))))),
                All("i",Fin(n),All("j",Fin(n),Eqn(App(p,i),App(p,j)))))))));
        Formula incidence=All("n",Nat(),All("E",Edges(n),All("i",Fin(n),All("u",e,
            Eqn(App(Call("incidence",e),i,V("u")),Sub(
                If(Eqn(i,Call("snd",V("u"))),D(1),D(0)),
                If(Eqn(i,Call("fst",V("u"))),D(1),D(0))))))));
        Formula cycle=All("n",Nat(),All("E",Edges(n),All("A",Mat(n),
            Imp(Call("ExactSupport",e,a),Imp(Call("HasNSSP",a),
                Le(Add(n,Call("rank",Call("incidence",e))),Card(e)))))));
        Formula bound=All("n",Nat(),Imp(Le(D(1),n),All("E",Edges(n),
            Imp(Call("ConnectedSupport",e),All("A",Mat(n),
                Imp(Call("ExactSupport",e,a),Imp(Call("HasNSSP",a),Le(Min(n),Card(e)))))))));
        Formula path=All("n",Nat(),All("i",Fin(n),All("j",Fin(n),
            Iff(Mem(Pair(i,j),Call("endpointSupport",n)),Or(
                And(Eqn(Call("val",i),D(0)),Eqn(Call("val",j),D(0))),Or(
                Eqn(Add(Call("val",i),D(1)),Call("val",j)),
                Eqn(Add(Call("val",j),D(1)),Call("val",i))))))));
        Formula upper=All("n",Nat(),Imp(Le(D(1),n),Call("Requires",Call("endpointSupport",n))));
        Formula attainment=All("n",Nat(),Imp(Le(D(1),n),Exists("E",Edges(n),
            And(Call("Requires",e),Eqn(Card(e),Min(n))))));
        Formula level=All("n",Nat(),All("E",Edges(n),Imp(Call("Requires",e),
            All("p",Fn(Fin(n),C("Real")),Imp(All("u",e,
                Eqn(App(p,Call("fst",V("u"))),App(p,Call("snd",V("u"))))),
                All("r",Fin(n),Exists("i",Fin(n),And(Eqn(App(p,i),App(p,V("r"))),
                    Mem(Pair(i,i),e)))))))));
        Formula connectedRequired=All("n",Nat(),All("E",Edges(n),Imp(
            Call("Requires",e),Call("ConnectedSupport",e))));
        Formula plant=All("n",Nat(),All("E",Edges(n),All("r",Fin(n),
            Imp(Mem(Pair(V("r"),V("r")),e),Exists("A",Mat(n),And(
                Call("ExactSupport",e,a),Eqn(Call("det",Sub(D(1),a)),D(0))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Real centralizers and directed cycle spaces constrain exact nSSP supports.",
            H("Directed support obstructions for nSSP"),Blocks(
                Node("nssp","The non-symmetric strong spectral property","HasNSSP",nssp,
                    "Every real obstruction matrix X is tested. Hadamard annihilation uses the same ordered entries, and the commutator uses X transposed. There is no extra identity-Hadamard or trace condition.",DescribeRole.Definition,true),
                Node("support","Exact directed support","ExactSupport",exact,
                    "The support is a finite set of ordered pairs on Fin n. Nonzero entries are equivalent to membership, so all prescribed arc weights are nonzero and all other entries vanish. Loops are counted once.",DescribeRole.Definition,true),
                Node("requires","A support requiring nSSP","Requires",requires,
                    "The quantifier ranges over every real matrix with precisely this support, including all assignments of nonzero weights of either sign.",DescribeRole.Definition,true),
                Node("event","The minimum-arcs assertion","MinimumArcs",Iff(Call("MinimumArcs"),whole),
                    "For each positive order, the assertion contains both the lower bound for every requiring support and existence of a requiring support attaining equality. The two clauses use the same order n.",DescribeRole.Definition,true),
                Node("incidence","The real signed incidence matrix","incidence",incidence,
                    "Each arc column is the target coordinate vector minus the source coordinate vector. This is the real cast of the integer signed incidence matrix. A loop column is zero; opposite arcs are separate columns.",DescribeRole.Definition,false),
                Node("connected","Constancy along every arc","ConnectedSupport",connection,
                    "A real function equal at the endpoints of every directed arc must be constant on all vertices. This is the algebraic connectivity condition used in the incidence-rank estimate.",DescribeRole.Definition,false),
                Node("cycle","The centralizer injects into the cycle space","nssp_centralizer_cycle_bound",cycle,
                    "View A as a linear operator over the reals and use its polynomial module. The classical PID structure theorem gives a finite product of cyclic quotient rings. Conjugated coordinatewise multiplication is injective and commutes with A, giving centralizer dimension at least n. The map F ↦ (A_ij F_ji) over the actual arc set lies in the signed incidence kernel because its boundary is the diagonal of FA−AF. If this map vanishes, nSSP applied to F transposed gives F=0. Rank-nullity therefore bounds n plus the incidence rank by the number of arcs. No positivity, diagonalizability or irreducibility is used.",DescribeRole.Theorem,false),
                Node("bound","The connected-support lower bound","nssp_arc_bound_of_connected",bound,
                    "The kernel of the transposed incidence matrix consists of functions constant along every arc. Under ConnectedSupport, evaluation at any one vertex is injective on that kernel, so its dimension is at most one. Transpose invariance of rank and rank-nullity give incidence rank at least n−1. Combining this with the centralizer-cycle bound gives 2n−1 arcs. Connectivity is an explicit hypothesis of this theorem.",DescribeRole.Theorem,false),
                Node("path","The endpoint-looped double path","endpointSupport",path,
                    "At positive order there is one loop at vertex zero and two opposite arcs between consecutive vertices. All other ordered pairs are absent.",DescribeRole.Definition,true),
                Node("upper","Universal real attainment construction","endpoint_requires",upper,
                    "Let F be the transpose of an obstruction. Its entries at the loop and both neighbouring diagonals vanish. Commutation along each odd offset, read from the terminal end of the path, forces that entire offset to vanish. Apply the same argument to the transposed matrices for the lower odd offsets. The endpoint loop then forces the remaining entries in the first column to vanish. Commutation propagates the zero column successively along every nonzero path arc. Thus F, and hence the obstruction, is zero. This is the construction of Theorem 5.5 of Koljančić and Oblak, formalized for arbitrary nonzero real weights.",DescribeRole.Theorem,true),
                Node("attainment","Exactly 2n−1 arcs","endpoint_attainment",attainment,
                    "The support is in bijection with one loop together with two copies of Fin(n−1). Its cardinality is 1+2(n−1)=2n−1 at every positive order. Combining this count with the universal real path argument gives the upper clause of the minimum-arcs assertion.",DescribeRole.Theorem,true),
                Node("level","A loop in every constant level","requires_level_has_loop",level,
                    "Take the diagonal indicator of any nonempty level of a function constant along every arc. It commutes with a matrix of that exact support because no arc crosses the level. If that level contained no loop, its diagonal indicator would also satisfy Hadamard annihilation, contradicting nSSP. In particular a component without a loop cannot occur in a requiring support.",DescribeRole.Theorem,false),
                Node("plant","A loop permits a real eigenvalue","loop_support_eigenvalue_one",plant,
                    "Give all prescribed entries other than a selected loop the same small nonzero real weight t. Write N(t)=I−tB, with the selected loop removed from B. Both det N(t) and the determinant obtained by replacing its selected row by the corresponding unit row equal one at t=0. Continuity makes both nonzero for some nonzero t. Choose the loop weight as their ratio. Multilinearity in that row then gives det(I−A)=0, while every prescribed entry remains nonzero. This supplies a real eigenvalue-one realization without any sign or genericity condition in the requiring property.",DescribeRole.Theorem,false),
                Node("required-connected","A requiring support is connected","requires_connected",connectedRequired,
                    "Suppose a function is constant along every arc but has two different vertex values. Its corresponding level and its complement have no arcs between them. The diagonal obstruction gives a loop in each part. Realize eigenvalue one on each restricted support, and choose a nonzero right eigenvector on the first part and a nonzero left eigenvector on the second. Their outer product is a nonzero matrix in an off-diagonal block that commutes with the block diagonal support matrix. Its transpose is Hadamard-annihilated by that support matrix. This contradicts the requirement that every exact-support matrix have nSSP, so the vertex function must be constant.",DescribeRole.Theorem,false),
                Node("result","The all-positive-order minimum","result",whole,
                    "Every requiring support is connected. Apply the centralizer and incidence lower bound to its matrix with every prescribed entry equal to one. This gives at least 2n−1 arcs. The endpoint-looped double path has exactly that many arcs and requires nSSP for every exact real weighting. Both conclusions hold at each positive order, including order one.",DescribeRole.Theorem,false,
                    new OpenProblemResolutionClaim(ProblemSlugRef.Create("koljancic-oblak-2026-nssp-minimum-arcs-problem-1-8"),ResolutionKind.Proved)))));

    }
    private static DocumentBlock Node(string id,string title,string name,Formula formula,string prose,DescribeRole role,bool literature,OpenProblemResolutionClaim? resolution=null) =>
        Describe.Lean(DescribeId.Create("nssp-min-arcs-"+id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(formula)),literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),role,resolution);
    private static Formula V(string s)=>F.Id(s);
    private static Formula C(string s)=>Seq(Operatorname,Grp(V(s)));
    private static Formula App(Formula f,params Formula[] a)=>new Formula.Apply(f,[..a]);
    private static Formula Call(string s,params Formula[] a)=>App(C(s),a);
    private static Formula All(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Exists(string s,Formula t,Formula b)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Fn(Formula a,Formula b)=>new Formula.TypeArrow(a,b);
    private static Formula Rel(Formula a,FormulaRelationOperator op,Formula b)=>new Formula.Relation(a,op,b);
    private static Formula Eqn(Formula a,Formula b)=>Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b)=>Rel(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Le(Formula a,Formula b)=>Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Mem(Formula a,Formula b)=>Rel(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Or(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Or,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Nat()=>C("Nat");
    private static Formula Fin(Formula n)=>Call("Fin",n);
    private static Formula Mat(Formula n)=>Call("Matrix",Fin(n),Fin(n),C("Real"));
    private static Formula Edges(Formula n)=>Call("Finset",Seq(Fin(n),Sp,Times,Sp,Fin(n)));
    private static Formula Card(Formula e)=>Call("card",e);
    private static Formula Min(Formula n)=>Sub(Mul(D(2),n),D(1));
    private static Formula Tr(Formula x)=>Call("transpose",x);
    private static Formula Pair(Formula a,Formula b)=>Seq(Open,a,Comma,Sp,b,Close);
    private static Formula If(Formula h,Formula a,Formula b)=>Seq(Open,C("if"),Sp,Open,h,Close,Sp,C("then"),Sp,a,Sp,C("else"),Sp,b,Close);
}
