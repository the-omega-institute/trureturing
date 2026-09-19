using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class ZeckendorfFutureKernelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Arith/ZeckendorfFutureKernel.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual legal continuations determine the unit-scaling quotient of a Fibonacci residue state.",
        H("Constructive Zeckendorf Future Equivalence"),
        Blocks(
            Paragraph(Text("Words are read least-significant first, with no adjacent true bits. "
                + "Arbitrary high zero padding and the empty word are allowed. The modular theorem "
                + "uses ZMod M for M at least two, including composite moduli. The two weight "
                + "rows have explicit Bezout certificates, as actual consecutive Fibonacci rows do.")),
            Describe.Lean(DescribeId.Create("zk-future-advance"), DeclarationHandle.Create(Owner+"advance"),
                H("Consecutive-weight clock"), StatementSource.FromAuthor(AdvanceFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("advance 0 is the identity "
                    + "and advance (n+1) at (u,v) is advance n at (v,u+v). This definition requires "
                    + "only addition in its coefficient type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zk-future-value"), DeclarationHandle.Create(Owner+"value"),
                H("Actual weighted value of the remaining word"), StatementSource.FromAuthor(ValueFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The empty word has value zero. "
                    + "A first bit b contributes u when true and zero otherwise, and the remaining "
                    + "word uses weights (v,u+v). Starting at (F_2,F_3) gives the ordinary "
                    + "least-significant-first Fibonacci value, reduced in the coefficient ring."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zk-future-legal"), DeclarationHandle.Create(Owner+"legal"),
                H("Boundary-aware admissibility"), StatementSource.FromAuthor(LegalFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The incoming previous bit "
                    + "is part of the state. An empty continuation is legal; a nonempty word "
                    + "is legal exactly when its first bit does not form eleven with the incoming "
                    + "bit and its tail is legal with that first bit as the new boundary."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zk-future-equivalence"), DeclarationHandle.Create(Owner+"sameFuture"),
                H("The complete divisibility future"), StatementSource.FromAuthor(FutureFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a common incoming bit, "
                    + "two triples (r,u,v) and (r',u',v') are equivalent when every finite "
                    + "continuation has the same legal-and-zero-residue acceptance answer. "
                    + "This is an entire future-language condition, not equality of a current output."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zk-future-unit-scaling-result"), DeclarationHandle.Create(Owner+"result"),
                H("Constructive saturation and exact fixed-boundary quotient"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For M at least two and T at least three, assume the literal "
                        + "Fibonacci return F_T=0,F_(T+1)=1 in ZMod M, and e*u+f*v=1 and "
                        + "e'*u'+f'*v'=1. First, every pair of coefficient residues A,B is realized "
                        + "by one actual word legal after either incoming bit, with value A*x+B*y "
                        + "for every initial weight row (x,y). Second, the full future equivalence "
                        + "holds exactly when a single unit scales all three residue coordinates.")),
                    Paragraph(Text("The proof derives the full weight-clock return from the actual "
                        + "Fibonacci recurrence. Two guarded words of length 2T place their only "
                        + "one at position T or T+1, then return the clock. Concatenating their "
                        + "powers programs every coefficient pair while respecting admissibility. "
                        + "Three resulting affine zero tests construct the common scalar, and "
                        + "the second Bezout row constructs its inverse. Homogeneity of the "
                        + "original word evaluation proves the reverse implication.")),
                    Paragraph(Text("The common incoming bit is explicit. The separate-boundary "
                        + "distinction, reachability, exact state count, probability-law lift and "
                        + "WSS rank-growth consequences are ordinary proofs in the existing "
                        + "Wieferich interface note. They are not extra kernel-certified conclusions "
                        + "of this declaration. No initial-depth-one hypothesis is supplied."))), DescribeRole.Theorem))));

    private static Formula V(string s)=>F.Id(s);
    private static Formula C(string s,params Formula[] xs)=>new Formula.Apply(Seq(Operatorname,Grp(V(s))),xs);
    private static Formula Eqn(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula All(string s,Formula type,Formula body)=>Seq(Forall,Sp,V(s),Sp,InMacro,Sp,type,Comma,Sp,body);
    private static Formula Ex(string s,Formula type,Formula body)=>Seq(Exists,Sp,V(s),Sp,InMacro,Sp,type,Comma,Sp,body);
    private static Formula Many(string[] names,Formula type,Formula body)
    { for(var j=names.Length-1;j>=0;--j)body=All(names[j],type,body);return body; }
    private static Formula And(params Formula[] xs)
    { var r=xs[^1];for(var j=xs.Length-2;j>=0;--j)r=C("And",xs[j],r);return r; }
    private static Formula R()=>C("ZMod",V("M"));
    private static Formula N()=>Seq(Mathbb,Grp(V("N")));
    private static Formula Bits()=>C("List",C("Bool"));
    private static Formula Read(Formula u,Formula v,Formula w)=>C("value",u,v,w);
    private static Formula Leg(Formula b,Formula w)=>C("legal",b,w);
    private static Formula Fib(Formula n)=>C("castToZMod",V("M"),C("Nat.fib",n));
    private static Formula Future()=>C("sameFuture",V("previous"),V("r"),V("u"),V("v"),V("rp"),V("up"),V("vp"));
    private static Formula AdvanceFormula()=>Disp(All("z",C("Prod",V("R"),V("R")),And(
        Eqn(C("advance",D(0),V("z")),V("z")),All("n",N(),Eqn(C("advance",Add(V("n"),D(1)),V("z")),
            C("advance",V("n"),C("pair",C("snd",V("z")),Add(C("fst",V("z")),C("snd",V("z"))))))))));
    private static Formula ValueFormula()=>Disp(Many(new[]{"u","v"},V("R"),And(
        Eqn(Read(V("u"),V("v"),C("nil")),D(0)),All("b",C("Bool"),All("w",Bits(),
            Eqn(Read(V("u"),V("v"),C("cons",V("b"),V("w"))),Add(C("ite",V("b"),V("u"),D(0)),
                Read(V("v"),Add(V("u"),V("v")),V("w")))))))));
    private static Formula LegalFormula()=>Disp(All("previous",C("Bool"),And(
        Leg(V("previous"),C("nil")),All("b",C("Bool"),All("w",Bits(),C("Iff",
            Leg(V("previous"),C("cons",V("b"),V("w"))),And(C("Not",And(Eqn(V("previous"),C("true")),
                Eqn(V("b"),C("true")))),Leg(V("b"),V("w")))))))));
    private static Formula FutureFormula()=>Disp(All("previous",C("Bool"),Many(new[]{"r","u","v","rp","up","vp"},R(),
        C("Iff",Future(),All("w",Bits(),C("Iff",And(Leg(V("previous"),V("w")),
            Eqn(Add(V("r"),Read(V("u"),V("v"),V("w"))),D(0))),And(Leg(V("previous"),V("w")),
            Eqn(Add(V("rp"),Read(V("up"),V("vp"),V("w"))),D(0)))))))));
    private static Formula ResultFormula()
    {
        var assumptions=And(C("Le",D(2),V("M")),C("Le",D(3),V("T")),Eqn(Fib(V("T")),D(0)),
            Eqn(Fib(Add(V("T"),D(1))),D(1)),Eqn(Add(Mul(V("e"),V("u")),Mul(V("f"),V("v"))),D(1)),
            Eqn(Add(Mul(V("ep"),V("up")),Mul(V("fp"),V("vp"))),D(1)));
        var program=Many(new[]{"A","B"},R(),Ex("w",Bits(),And(All("b",C("Bool"),Leg(V("b"),V("w"))),
            Many(new[]{"x","y"},R(),Eqn(Read(V("x"),V("y"),V("w")),Add(Mul(V("A"),V("x")),Mul(V("B"),V("y"))))))));
        var scaled=Ex("a",R(),Ex("aInv",R(),And(Eqn(Mul(V("a"),V("aInv")),D(1)),
            Eqn(V("rp"),Mul(V("a"),V("r"))),Eqn(V("up"),Mul(V("a"),V("u"))),Eqn(V("vp"),Mul(V("a"),V("v"))))));
        return Disp(Many(new[]{"M","T"},N(),All("previous",C("Bool"),
            Many(new[]{"r","u","v","rp","up","vp","e","f","ep","fp"},R(),
                C("Implies",assumptions,And(program,C("Iff",Future(),scaled)))))));
    }
}
