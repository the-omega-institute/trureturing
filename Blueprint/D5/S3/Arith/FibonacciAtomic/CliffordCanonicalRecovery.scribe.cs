using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class CliffordCanonicalRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete infinite canonical Clifford orbit permits exactly the stated modular readers.",
        H("Sharp Clifford Canonical Recovery"), Blocks(
            Paragraph(Text("Use the Clifford algebra and leaf observation E from CliffordLeafOrbit. The canonical source is T(j)=rho^j(alpha), "
                + "its observation is X(j), and its composition is z(j)=M^j(1,0), with M(a,b)=(b,a+b). "
                + "A factorizing reader is a function on the range of X; it receives the algebra element alone. The residueTarget(D) maps j to z(j) modulo D.")),
            Def("low", "Standard low representatives", "For positive d, low(d,j) is the pair of standard representatives of z(j) modulo d."),
            Paragraph(Text("The integer carry kappa(d,j) is floor((low(d,j)[0]+low(d,j)[1])/d), using the standard residue-pair carry. It is zero or one for positive d.")),
            Def("K", "Next-step carry output", "K(d,e,j)=(0,kappa(d,j)) modulo e."),
            Def("H", "Current high output", "H(d,e,j) is the pair of quotients of the coordinates of z(j) by d, reduced modulo e."),
            Def("L", "Complete current target", "L(d,e,j) pairs low(d,j) with H(d,e,j). Both components come from the same source."),
            Describe.Lean(DescribeId.Create("clifford-canonical-recovery-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Sharp recovery and source obstructions"), StatementSource.FromAuthor(Formula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All moduli D,d,e are natural numbers. The first classification assumes D>=1. "
                    + "The carry classification assumes d>=1 and e>=2. The complete-target classification assumes d,e>=1. "
                    + "The high-only classification additionally assumes d divides 4. For e=1 the carry output is identically zero for every positive d; "
                    + "for d=1 both low and the integer carry vanish, so the carry output vanishes for every positive e.")),
                    Paragraph(Text("Observation equality is index equality modulo six. Modular composition is six-periodic precisely when the modulus divides 4. "
                        + "A periodic carry forces the difference of low representatives at indices j+6 and j to satisfy a bounded integer Fibonacci recursion. "
                        + "For such a difference a(j), the product a(j)a(j+1) increases by a(j+1)^2. Its bounded integer range has a greatest element; "
                        + "the sequence is then zero on a tail, and the reversible recursion forces every difference to vanish. This yields the carry necessity for all moduli. "
                        + "The standard quotient-remainder identities identify the complete target with composition modulo d*e.")),
                    Paragraph(Text("The same actual sources at indices zero and six have equal Clifford observation A and compositions (1,0) and (5,8). "
                        + "Their quantities are 2 and 34. At d=3 their low pairs are (1,0) and (2,2), with carry outputs (0,0) and (0,1) for every e>=2. "
                        + "At d=4,e=2 the low pairs agree at (1,0), both next-step carry outputs vanish, and current highs are (0,0) and (1,0).")),
                    Paragraph(Text("The canonical successor has a reader. On all source trees, no function R on the image of E satisfies R(E(t))=E(rho(t)) for every t. "
                        + "Let t2=(alpha,alpha) and t4=(t2,t2). Both have observation 1, but their substituted observations are -1 and 1. "
                        + "The trees p=((alpha,alpha),alpha) and q=(alpha,(alpha,alpha)) have equal composition (3,0) and the same ordered leaf-label list, "
                        + "yet p and q are unequal and their observations agree. Thus the observation also fails to recover parentheses on a fixed composition and leaf order. "
                        + "For every type Y and target g, a reader can fit g on the initial indices j<6."))), DescribeRole.Theorem),
            Paragraph(Text("The statements concern the complete infinite orbit. They do not impose the same necessary conditions on arbitrary finite source subsets. "
                + "The standard Clifford construction is described in Lundholm and Svensson, arXiv:0907.5356v1, sections 2.1-2.3. "
                + "Flaut, DOI:10.1186/1687-1847-2014-279, concerns a different Clifford construction associated with generalized Fibonacci quaternions.")))));
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("clifford-canonical-recovery-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. args]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula Pair(Formula x, Formula y) => Par(Seq(x,Comma,Sp,y));
    private static Formula EqOf(Formula x, Formula y) => Seq(x,Sp,Eq,Sp,y);
    private static Formula NeOf(Formula x, Formula y) => Seq(x,Sp,Neq,Sp,y);
    private static Formula Divides(Formula x, Formula y) => Seq(x,Sp,Mid,Sp,y);
    private static Formula IffOf(Formula x, Formula y) => Seq(Par(x),Sp,Leftrightarrow,Sp,Par(y));
    private static Formula All(string vars, Formula x) => Seq(Forall,Sp,
        Seq(vars.Split(',').Select((s,i) => i == 0 ? V(s) : Seq(Comma,Sp,V(s))).ToArray()),Comma,Sp,Par(x));
    private static Formula Ex(string vars, Formula x) => Seq(Exists,Sp,
        Seq(vars.Split(',').Select((s,i) => i == 0 ? V(s) : Seq(Comma,Sp,V(s))).ToArray()),Comma,Sp,Par(x));
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x),Sp,Implies,Sp,Par(y));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x,i) => i == 0 ? Par(x) : Seq(Sp,Land,Sp,Par(x))).ToArray());
    private static Formula Positive(Formula x) => Seq(D(1),Leq,x);
    private static Formula Formula()
    {
        Formula d=V("d"),e=V("e"),n=V("D"),j=V("j"),t=V("t"),p=V("p"),q=V("q");
        Formula modular=All("D",Imp(Positive(n),IffOf(Call("Factors",Call("residueTarget",n)),Divides(n,D(4)))));
        Formula carry=All("d,e",Imp(And(Positive(d),Seq(D(2),Leq,e)),IffOf(Call("Factors",Call("K",d,e)),Divides(d,D(4)))));
        Formula eone=All("d",Imp(Positive(d),And(Call("Factors",Call("K",d,D(1))),All("j",EqOf(Call("K",d,D(1),j),D(0))))));
        Formula done=All("e",Imp(Positive(e),And(Call("Factors",Call("K",D(1),e)),All("j",And(EqOf(Call("low",D(1),j),D(0)),
            EqOf(Call("kappa",D(1),j),D(0)),EqOf(Call("K",D(1),e,j),D(0)))))));
        Formula complete=All("d,e",Imp(And(Positive(d),Positive(e)),IffOf(Call("Factors",Call("L",d,e)),Divides(Seq(d,e),D(4)))));
        Formula high=All("d,e",Imp(And(Positive(d),Positive(e),Divides(d,D(4))),IffOf(Call("Factors",Call("H",d,e)),Divides(Seq(d,e),D(4)))));
        Formula doneComplete=All("e",Imp(Positive(e),IffOf(Call("Factors",Call("L",D(1),e)),Divides(e,D(4)))));
        Formula collision=And(EqOf(Call("X",D(0)),V("A")),EqOf(Call("X",D(6)),V("A")),
            EqOf(Call("z",D(0)),Pair(D(1),D(0))),EqOf(Call("z",D(6)),Pair(D(5),D(8))),
            EqOf(Call("quantity",Call("z",D(0))),D(2)),EqOf(Call("quantity",Call("z",D(6))),D(34)),
            EqOf(Call("low",D(3),D(0)),Pair(D(1),D(0))),EqOf(Call("low",D(3),D(6)),Pair(D(2),D(2))),
            All("e",Imp(Seq(D(2),Leq,e),And(EqOf(Call("K",D(3),e,D(0)),Pair(D(0),D(0))),
                EqOf(Call("K",D(3),e,D(6)),Pair(D(0),D(1))),NeOf(Call("K",D(3),e,D(0)),Call("K",D(3),e,D(6)))))),
            EqOf(Call("low",D(4),D(0)),Pair(D(1),D(0))),EqOf(Call("low",D(4),D(6)),Pair(D(1),D(0))),
            EqOf(Call("K",D(4),D(2),D(0)),D(0)),EqOf(Call("K",D(4),D(2),D(6)),D(0)),
            EqOf(Call("H",D(4),D(2),D(0)),D(0)),EqOf(Call("H",D(4),D(2),D(6)),Pair(D(1),D(0))));
        Formula successor=Call("Factors",Seq(j,Sp,Mapsto,Sp,Call("X",Seq(j,Plus,D(1)))));
        Formula noAllTree=Seq(Neg,Ex("R",All("t",EqOf(Call("R",Call("E",t)),Call("E",Call("rho",t))))));
        Formula treeCollision=And(EqOf(Call("E",V("t2")),D(1)),EqOf(Call("E",V("t4")),D(1)),
            EqOf(Call("E",Call("rho",V("t2"))),Seq(Minus,D(1))),EqOf(Call("E",Call("rho",V("t4"))),D(1)));
        Formula brackets=Ex("p,q",And(EqOf(Call("c",p),Pair(D(3),D(0))),EqOf(Call("c",q),Pair(D(3),D(0))),
            EqOf(Call("leafLabels",p),Call("leafLabels",q)),NeOf(p,q),EqOf(Call("E",p),Call("E",q))));
        Formula finite=All("Y,g",Ex("f",All("j",Imp(Seq(j,Lt,D(6)),EqOf(Call("f",Call("X",j)),Call("g",j))))));
        var rows=new [] { modular,carry,eone,done,complete,high,doneComplete,collision,And(successor,noAllTree,treeCollision,brackets,finite) };
        return Disp(Seq(Begin,Grp(V("gathered")),Seq(rows.Select((x,i) => i==0 ? Par(x) : Seq(RowBreak,Grp(),Land,Sp,Par(x))).ToArray()),End,Grp(V("gathered"))));
    }
}
