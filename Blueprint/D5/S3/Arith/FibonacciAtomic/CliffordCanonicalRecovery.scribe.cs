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
                + "A factorizing reader is a function on the range of X; it receives the algebra element alone.")),
            Def("low", "Standard low representatives", "For positive d, low(d,j) is the pair of standard representatives of z(j) modulo d."),
            Def("carry", "Next-step integer carry", "carry(d,j) is floor((low(d,j)[0]+low(d,j)[1])/d). It is zero or one for positive d."),
            Def("K", "Next-step carry output", "K(d,e,j)=(0,carry(d,j)) modulo e."),
            Def("H", "Current high output", "H(d,e,j) is the pair of quotients of the coordinates of z(j) by d, reduced modulo e."),
            Def("L", "Complete current target", "L(d,e,j) pairs low(d,j) with H(d,e,j). Both components come from the same source."),
            Describe.Lean(DescribeId.Create("clifford-canonical-recovery-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Modulus, carry, and digit classification"), StatementSource.FromAuthor(Formula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All moduli D,d,e are natural numbers. The first classification assumes D>=1. "
                    + "The carry classification assumes d>=1 and e>=2. The complete-target classification assumes d,e>=1. "
                    + "The high-only classification additionally assumes d divides 4. For e=1 the carry output is identically zero for every positive d; "
                    + "for d=1 both low and the integer carry vanish, so the carry output vanishes for every positive e.")),
                    Paragraph(Text("Observation equality is index equality modulo six. Modular composition is six-periodic precisely when the modulus divides 4. "
                        + "A periodic carry forces the difference of low representatives at indices j+6 and j to satisfy a bounded integer Fibonacci recursion. "
                        + "For such a difference a(j), the product a(j)a(j+1) increases by a(j+1)^2. Its bounded integer range has a greatest element; "
                        + "the sequence is then zero on a tail, and the reversible recursion forces every difference to vanish. This yields the carry necessity for all moduli. "
                        + "The standard quotient-remainder identities identify the complete target with composition modulo d*e."))), DescribeRole.Theorem),
            Paragraph(Text("The statements concern the complete infinite orbit. They do not impose the same necessary conditions on arbitrary finite source subsets. "
                + "The standard Clifford construction is described in Lundholm and Svensson, arXiv:0907.5356v1, sections 2.1-2.3. "
                + "Flaut, DOI:10.1186/1687-1847-2014-279, concerns a different Clifford construction associated with generalized Fibonacci quaternions.")))));
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("clifford-canonical-recovery-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. args]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula Divides(Formula x, Formula y) => Seq(x, Sp, Mid, Sp,y);
    private static Formula IffOf(Formula x, Formula y) => Seq(Par(x),Sp,Leftrightarrow,Sp,Par(y));
    private static Formula And(Formula x, Formula y) => Seq(Par(x),Sp,Land,Sp,Par(y));
    private static Formula Formula()
    {
        Formula d=V("d"), e=V("e"), n=V("D");
        Formula modular=IffOf(Call("Factors",Call("residueTarget",n)),Divides(n,D(4)));
        Formula carry=IffOf(Call("Factors",Call("K",d,e)),Divides(d,D(4)));
        Formula complete=IffOf(Call("Factors",Call("L",d,e)),Divides(Seq(d,e),D(4)));
        Formula high=Seq(Divides(d,D(4)),Sp,Implies,Sp,IffOf(Call("Factors",Call("H",d,e)),Divides(Seq(d,e),D(4))));
        return Disp(And(modular,And(carry,And(complete,high))));
    }
}
