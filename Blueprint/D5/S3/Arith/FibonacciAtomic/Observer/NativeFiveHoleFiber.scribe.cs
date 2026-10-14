using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFiveHoleFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeFiveHoleFiber", H("Whole guarded five-hole fibers and complete labels"), Blocks(
            Describe.Lean(DescribeId.Create("five-hole-raw"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.Raw"), H("The complete guarded raw record"),
                StatementSource.FromAuthor(Disp(RawFormula())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Source is the finite free magma on the two native leaves. Addresses are Boolean words, false for L and true for R. F(y) pairs alpha with the actual substitution of y. V(x,y,z) pairs x with the successive holes y, z, F(y), F(z). Q consists of L, RL, RRL, RRRL and RRRR.")),
                    Paragraph(Text("RootLabel is the complete one-hole row at the empty address. GuardedEqual requires presence at both supplied endpoints and equality of the entire transformed subtrees. All original literals and both positive copies concern the same finite source."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-hole-root-record"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.root_record"),
                H("The complete root row is constant"),
                StatementSource.FromAuthor(Disp(All("u",Source,EqOf(Call("literalRecord",Call("singleton",Call("nil")),V("u")),Call("rootLabel"))))),
                AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Every nonempty finite source is hidden by the root hole. Its literal exterior is the empty-address hole and its complete partition has one class. This equality keeps the entire row, including the partition, rather than only a point reply."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-hole-raw-fiber-iff"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.raw_fiber_iff"), H("Every raw source has the full source shape"),
                StatementSource.FromAuthor(Disp(All("u",Source,IffOf(Call("Raw",V("u")),Some("x,y,z",Source,EqOf(V("u"),Call("V",V("x"),V("y"),V("z")))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The four branch replies extract the full outer skeleton. The alpha replies force branches in its last two holes. Transport at epoch one and the guarded copies identify their right children with the substitutions of y and z. Conversely every source of this shape satisfies the root row, every literal, both endpoint guards and both copied equalities. The parameterization covers the entire raw fiber."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-hole-epoch-hole"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.epoch_hole"), H("All cut endpoints remain reached at every epoch"),
                StatementSource.FromAuthor(Disp(All("a",Nat,All("x,y,z",Source,All("i",Call("Fin",D(5)),EqOf(Call("subtree",Call("position",V("i")),Rho(V("a"),Call("V",V("x"),V("y"),V("z")))),Call("some",Rho(V("a"),Call("hole",V("x"),V("y"),V("z"),V("i")))))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Original present transport applies at each already reached cut address. Arbitrary supplied natural epochs retain both guards of every negative record. The comparison is between entire transformed holes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-hole-distinct"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.Distinct"), H("All six class comparisons"),
                StatementSource.FromAuthor(Disp(All("y,z",Source,IffOf(Call("Distinct",V("y"),V("z")),AndOf(NeOf(V("y"),V("z")),NeOf(V("y"),Call("F",V("y"))),NeOf(V("y"),Call("F",V("z"))),NeOf(V("z"),Call("F",V("y"))),NeOf(V("z"),Call("F",V("z"))),NeOf(Call("F",V("y")),Call("F",V("z")))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Both labels contain the same complete four-branch exterior. The false label has partition blocks {L,RL}, {RRL}, {RRRL}, {RRRR}. The true label has blocks {L,RRRL}, {RL}, {RRL}, {RRRR}. Label compares every ordered pair in Q, including reflexive and reversed pairs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-hole-complete-label-iff"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.complete_label_iff"), H("The entire exterior and partition determine the parameters"),
                StatementSource.FromAuthor(Disp(All("s",Bool,All("x,y,z",Source,IffOf(EqOf(Call("literalRecord",Call("Q"),Call("V",V("x"),V("y"),V("z"))),Call("label",V("s"))),AndOf(EqOf(V("x"),Call("ite",V("s"),Call("F",V("y")),V("y"))),Call("Distinct",V("y"),V("z")))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The forward direction extracts the repeated block and all six inequalities from the complete partition. The reverse checks every pair of holes and the whole exterior. No chosen representative narrows the fiber."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-hole-raw-stratum-iff"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleFiber.raw_stratum_iff"), H("Exact membership in each original whole stratum"),
                StatementSource.FromAuthor(Disp(All("s",Bool,All("H",Hist,All("u",Source,IffOf(Call("Stratum",V("s"),V("H"),V("u")),Some("y,z",Source,AndOf(EqOf(V("u"),Call("source",V("s"),V("y"),V("z"))),Call("Distinct",V("y"),V("z")),Call("Protected",V("H"),Call("source",V("s"),V("y"),V("z"))))))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("History is any finite list of negative records between Q endpoints, at arbitrary supplied natural epochs. Supported constrains only endpoints. IndexedHistory reconstructs the original list exactly, retaining order and repetitions. Negative contains both guards and the whole-subtree disequality. Protected conjoins every original occurrence. D is Raw intersected with Protected; Stratum additionally fixes the full literal record. Other labels of D remain part of D."))), DescribeRole.Theorem)
        )));

    private static Formula RawFormula()
    {
        Formula Read(string p,string r) => EqOf(Call("readout",Call(p),V("u")),Call(r));
        Formula Guard(string p,string q) => Call("GuardedEqual",D(0),Call(p),D(1),Call(q),V("u"));
        return All("u",Source,IffOf(Call("Raw",V("u")),AndOf(
            EqOf(Call("literalRecord",Call("singleton",Call("nil")),V("u")),Call("rootLabel")),
            Read("nil","branch"),Read("R","branch"),Read("RR","branch"),Read("RRR","branch"),
            Read("RRRLL","alpha"),Read("RRRRL","alpha"),Guard("RRRLR","RL"),Guard("RRRRR","RRL"))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula AndOf(params Formula[] xs) => xs.Length == 1 ? xs[0] :
        Seq(Par(xs[0]),Sp,Land,Sp,Par(AndOf(xs.Skip(1).ToArray())));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall,Sp,
        Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()),
        Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists,Sp,
        Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()),
        Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Source => V("Source");
    private static Formula Nat => V("Nat");
    private static Formula Bool => V("Bool");
    private static Formula Hist => V("History");
    private static Formula Rho(Formula n, Formula a) => Call("iterate",Call("substitution"),n,a);
}
