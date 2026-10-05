using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class CliffordLeafOrbitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Clifford leaf product has exactly six distinct canonical phases.",
        H("Exact Clifford Leaf Observation Fibers"), Blocks(
            Paragraph(Text("Let Q(a,b)=a*a+a*b-b*b on the real coordinate plane, and let C be its Clifford algebra with v*v=Q(v)1. "
                + "Write A and B for the canonical images of (1,0) and (0,1). Sources are the existing ordered Boolean leaf trees; "
                + "alpha is true and beta is false. The existing substitution sends alpha to beta and beta to (beta,alpha).")),
            Def("Q", "Quadratic form", "The quadratic form is the sum of the first-coordinate square and the coordinate product, minus the second-coordinate square."),
            Def("E", "Ordered leaf product", "The free-magma homomorphism sends alpha to A and beta to B. Its value is the leaf product in source order."),
            Def("X", "Canonical observation", "X(j)=E(rho^j(alpha)) for every natural index j."),
            Def("phases", "Six chronological phases", "The six values are A, B, BA, A+B, -B, AB, in that order."),
            Def("Factors", "Reader on the canonical image", "A target g factors when a function on the range of X takes X(j) to g(j) for every natural j. The reader receives only the algebra element."),
            Describe.Lean(DescribeId.Create("clifford-leaf-orbit-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Exact fibers and canonical successor"), StatementSource.FromAuthor(Formula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here c is the existing composition, M(a,b)=(b,a+b), T(j)=rho^j(alpha), and P denotes the displayed six-element phase list. "
                    + "For every type Y and every g from the natural numbers to Y, a reader exists exactly when g is six-periodic. "
                    + "This includes the successor target g(j)=X(j+1).")),
                    Paragraph(Text("The Clifford square and polar relations give A*A=1, B*B=-1 and AB+BA=1. "
                        + "The ordered source recursion gives X(j+2)=X(j+1)X(j). These relations produce the six phases. "
                        + "A two-by-two real matrix representation separates all six, so equality of observations is precisely equality of indices modulo six.")),
                    Paragraph(Text("Let t2=(alpha,alpha) and t4=(t2,t2). Both leaf products are 1, while their substituted products are -1 and 1. "
                        + "No reader on the full source image can therefore perform substitution. The unequal trees p=((alpha,alpha),alpha) and q=(alpha,(alpha,alpha)) "
                        + "have equal composition (3,0), equal ordered leaf labels, and equal Clifford observations. Here leafLabels(t) is the list of the indexedEquiv leaf-position function. "
                        + "For each Y and target g, a reader can fit g on all indices j<6, because these observations are distinct."))), DescribeRole.Theorem),
            Paragraph(Text("The Clifford construction and its universal property are standard; see Lundholm and Svensson, Clifford algebra, geometric algebra, and applications, arXiv:0907.5356v1, sections 2.1-2.3.")))));
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("clifford-leaf-orbit-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula EqOf(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Mod(Formula x) => Call("mod", x, D(6));
    private static Formula All(string vars, Formula x) => Seq(Forall, Sp,
        Seq(vars.Split(',').Select((s,i) => i==0 ? V(s) : Seq(Comma,Sp,V(s))).ToArray()),Comma,Sp,Par(x));
    private static Formula Ex(string vars, Formula x) => Seq(Exists, Sp,
        Seq(vars.Split(',').Select((s,i) => i==0 ? V(s) : Seq(Comma,Sp,V(s))).ToArray()),Comma,Sp,Par(x));
    private static Formula And(Formula x, Formula y) => Seq(Par(x), Sp, Land, Sp, Par(y));
    private static Formula Formula()
    {
        Formula j=V("j"), k=V("k"), g=V("g");
        Formula add(Formula x, int y) => Seq(x, Plus, D(y));
        Formula iff(Formula x, Formula y) => Seq(Par(x), Sp, Leftrightarrow, Sp, Par(y));
        Formula c=All("j", EqOf(Call("c",Call("T",j)),Call("atomicBlock",j)));
        Formula p=All("j", EqOf(Call("X",j),Call("P",Mod(j))));
        Formula fibers=All("j,k",iff(EqOf(Call("X",j),Call("X",k)),EqOf(Mod(j),Mod(k))));
        Formula readers=All("Y,g",iff(Call("Factors",g),All("j",EqOf(Call("g",add(j,6)),Call("g",j)))));
        Formula successor=Call("Factors",Seq(j,Sp,Mapsto,Sp,Call("X",add(j,1))));
        Formula t=V("t"), s=V("p"), r=V("q");
        Formula noAll=Seq(Neg,Ex("R",All("t",EqOf(Call("R",Call("E",t)),Call("E",Call("rho",t))))));
        Formula collision=And(EqOf(Call("E",V("t2")),D(1)),And(EqOf(Call("E",V("t4")),D(1)),
            And(EqOf(Call("E",Call("rho",V("t2"))),Seq(Minus,D(1))),EqOf(Call("E",Call("rho",V("t4"))),D(1)))));
        Formula bracket=Ex("p,q",And(EqOf(Call("c",s),Par(Seq(D(3),Comma,D(0)))),And(EqOf(Call("c",r),Par(Seq(D(3),Comma,D(0)))),
            And(EqOf(Call("leafLabels",s),Call("leafLabels",r)),And(Seq(s,Neq,r),EqOf(Call("E",s),Call("E",r)))))));
        Formula finite=All("Y,g",Ex("f",All("j",Seq(Par(Seq(j,Lt,D(6))),Implies,Par(EqOf(Call("f",Call("X",j)),Call("g",j)))))));
        return Disp(And(c,And(p,And(fibers,And(readers,And(successor,And(noAll,And(collision,And(bracket,finite)))))))));
    }
}
