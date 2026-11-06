using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class LinearKTreeResistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/LinearKTreeResistance.";
    private static LibraryNoteRef Source() => LibraryNoteRef.Create("D5/L/Eigenstructure/barrettevansfrancis2017resistance");
    public DocumentDefinition Create()
    {
        Formula n=V("n"), k=V("k"), i=V("i"), j=V("j"), r=V("R");
        Formula graph=All("n",Nat(),All("k",Nat(),Eqn(Call("graph",n,k),
            App(Q("SimpleGraph","fromRel"),Lam("i",Fin(n),Lam("j",Fin(n),
                LeqOf(App(Q("Nat","dist"),Val(i),Val(j)),k)))))));
        Formula sequence=All("k",Nat(),All("R",Fn(Nat(),Real()),
            Eqn(Call("IsResistanceSequence",k,r),SequenceBody())));
        return DocumentDefinition.Create(ScribeNode.Create("Endpoint resistance in powers of a finite path.",
            H("The straight linear k-tree resistance increment limit"),Blocks(
                Node("graph","Straight linear k-tree","graph",graph,
                    "Definition 43 (arXiv:1712.05883v1, p. 20): A straight linear k-tree is a graph Gₙ with n vertices with adjacency matrix that is symmetric, banded, with the first through kth subdiagonals equal to one and first through kth superdiagonals equal to one, and all other entries equal to zero. In other words Gₙ is the graph whose (0,1)-adjacency matrix is defined by aᵢⱼ=1 if 0<|i-j|≤ k, and aᵢⱼ=0 otherwise. The vertex i in Fin n represents source vertex i+1; fromRel removes loops and symmetrizes the relation.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source())),
                Node("sequence","Kirchhoff resistance sequence","IsResistanceSequence",sequence,
                    "The potential difference vᵢ - vⱼ between nodes i and j needed to maintain this current is the effective resistance or resistance distance between i and j since by Ohm's law, the resistance, r_G(i,j) is r_G(i,j) = (vᵢ-vⱼ)/1 = vᵢ-vⱼ. The source vector of currents is s = eᵢ -eⱼ. Then by Kirchoff's law and Ohm's law, L(G)v = s. This is the unit-current equation in section 2, p. 3 of arXiv:1712.05883v1. Unit edge weights give the graph Laplacian. The index t represents size t+2, and the resistance is the first voltage minus the last voltage.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source())),
                Node("claim","Conjecture 44","claim",Eqn(Call("claim"),ClaimBody()),
                    "Conjecture 44 (arXiv:1712.05883v1, p. 20): Let G be the straight linear k-tree, k ≥ 1, with n vertices and H be the straight linear k-tree with n+1 vertices. Then limₙ→∞ r_H(1,n+1) − r_G(1,n) = 6/(k(k+1)(2k+1)). Evans and Francis restate this as Conjecture 4.5 in arXiv:2108.07942v2. Each k is fixed before the size tends to infinity. Existence is included, and every solution of the Kirchhoff equation has the asserted increment limit.",DescribeRole.Definition,AssessedProvenance.FromLiterature(Source())),
                Node("result","The increment limit for every positive k","result",ClaimBody(),
                    "The interval Gram matrix Q satisfies I ≤ Q ≤ D I, where D is the sum of the first k squares. Its defect c = D 1 - Q 1 is supported at the two endpoints. Finite propagation stabilizes every polynomial endpoint moment, and geometric approximation to the inverse makes the inverse quadratic correction converge. The identity R = N/D + (1ᵀc + cᵀQ⁻¹c)/D² then yields the increment limit. The sum-of-squares identity gives the displayed slope, including k=1.",DescribeRole.Theorem,AssessedProvenance.FromRepo(Source())))));
    }
    private static Formula SequenceBody()
    {
        Formula k=V("k"), r=V("R"), t=V("t"), v=V("V"), size=Add(t,D(2));
        Formula last=App(Q("Fin","last"),Add(t,D(1)));
        return All("t",Nat(),Ex("V",Fn(Fin(size),Real()),And(
            Eqn(App(Q("Matrix","mulVec"),App(Q("SimpleGraph","lapMatrix"),Call("graph",size,k),Real()),v),
                Sub(App(Q("Pi","single"),D(0),Typed(D(1),Real())),App(Q("Pi","single"),last,Typed(D(1),Real())))),
            Eqn(App(r,t),Sub(App(v,D(0)),App(v,last))))));
    }
    private static Formula ClaimBody()
    {
        Formula k=V("k"), r=V("R"), t=V("t"), kr=Typed(k,Real());
        Formula slope=new Formula.Fraction(Typed(D(6),Real()),Mul(Mul(kr,Add(kr,D(1))),Add(Mul(D(2),kr),D(1))));
        return All("k",Nat(),Imp(LeqOf(D(1),k),And(
            Ex("R",Fn(Nat(),Real()),Call("IsResistanceSequence",k,r)),
            All("R",Fn(Nat(),Real()),Imp(Call("IsResistanceSequence",k,r),
                App(Q("Filter","Tendsto"),Lam("t",Nat(),Sub(App(r,Add(t,D(1))),App(r,t))),
                    Q("Filter","atTop"),Call("nhds",slope)))))));
    }
    private static DocumentBlock Node(string id,string title,string name,Formula formula,string prose,DescribeRole role,AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("linear-k-tree-resistance-"+id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(formula)),provenance,Blocks(Paragraph(Text(prose))),role);
    private static Formula Parenthesized(Formula f) => Seq(Open,f,Close);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s) => Seq(Operatorname,Grp(V(s)));
    private static Formula Q(string a,string b) => Seq(C(a),Dot,C(b));
    private static Formula Call(string s,params Formula[] a) => a.Length==0?C(s):App(C(s),a);
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Nat() => C("Nat");
    private static Formula Real() => C("Real");
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Val(Formula i) => Call("val",i);
    private static Formula Typed(Formula x,Formula t) => Parenthesized(Seq(x,Colon,Sp,t));
    private static Formula Fn(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula All(string n,Formula t,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula Ex(string n,Formula t,Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),t,b);
    private static Formula Lam(string n,Formula t,Formula b) => Parenthesized(Seq(LambdaLower,Sp,V(n),Colon,Sp,t,Sp,Mapsto,Sp,b));
    private static Formula Eqn(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula LeqOf(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
}
