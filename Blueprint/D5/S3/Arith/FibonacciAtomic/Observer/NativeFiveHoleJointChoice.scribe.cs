using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFiveHoleJointChoiceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeFiveHoleJointChoice", H("Total finite joint choice on the whole source fiber"), Blocks(
            Describe.Lean(DescribeId.Create("five-hole-agree"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.Agree"), H("Inclusive absent-aware agreement"),
                StatementSource.FromAuthor(Disp(All("h",Nat,All("u,v",Source,IffOf(Call("Agree",V("h"),V("u"),V("v")),All("a",Addr,Imp(Seq(Call("length",V("a")),Sp,Le,Sp,V("h")),EqOf(Call("readout",V("a"),V("u")),Call("readout",V("a"),V("v")))))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Agreement compares every address through the inclusive depth and all four replies: alpha, beta, branch and absent. It includes early leaves and their absent descendants. Constructor locality and original prefix locality preserve agreement under pairs and every fixed native substitution iterate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-hole-approximation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.approximation"), H("Finite contact uses actual iterates"),
                StatementSource.FromAuthor(Disp(All("n",Nat,EqOf(Call("approximation",V("n")),Call("iterate",Call("F"),V("n"),Alpha))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The finite base at depth h is the iterate at h+1. It agrees through h with its F image, by root agreement at zero and one-level constructor locality in the inductive step. Its right spine of length h+1 reaches the substitution iterate of alpha at that exponent. Original present transport is applied only to an already reached address. Substitution is never commuted with F."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-hole-witness"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.Witness"), H("Actual finite sources in both whole strata"),
                StatementSource.FromAuthor(Disp(All("H",Hist,All("h",Nat,EqOf(Call("Witness",V("H"),V("h")),Call("Subtype",Lam("p",Call("Prod",Source,Source),AndOf(Call("Stratum",V("false"),V("H"),Call("fst",V("p"))),Call("Stratum",V("true"),V("H"),Call("snd",V("p"))),Call("Agree",V("h"),Call("fst",V("p")),Call("snd",V("p"))))))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Both tables use the same independent live patterns at depth h+1: the contact iterate and a full branch tree of that depth. Reached spines and frontier_geometry prove liveness. Existing patternTerm, pattern_deep, original_fill_reply, pattern_evaluate and depthEquiv directly supply equality of readouts at every shorter address.")),
                    Paragraph(Text("Simultaneous prefix separation supplies one explicit prefixTuple for each complete table in these common patterns. The two y values agree with the contact iterate, and the two z values with the branch base. Finite contact and locality give agreement between the first y and F of the second. Pairing all five holes yields the original sources with their complete labels and every protected-history occurrence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-hole-j"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.J"), H("Existence at a supplied finite depth"),
                StatementSource.FromAuthor(Disp(All("H",Hist,All("h",Nat,IffOf(Call("J",V("H"),V("h")),Call("Nonempty",Call("Witness",V("H"),V("h")))))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("JointWitness contains the computed source pair and both original membership proofs. Its data use finite iterates, depth decompositions, finite separators and explicit frontier numbering. No noncomputable choice over an existence theorem selects the sources."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("five-hole-joint-finite-choice"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.joint_finite_choice"), H("Whole-stratum emptiness or joint witnesses at every depth"),
                StatementSource.FromAuthor(Disp(ChoiceFormula())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Choose computes both finite separator tests. Failure proves an entire original stratum empty. Success returns the explicit function from each supplied natural depth to JointWitness. The empty case excludes J at zero. Arbitrary epochs, repetitions, both guards, all six class comparisons, the full exterior and both complete partitions are retained.")),
                    Paragraph(Text("This structural conclusion concerns the entire original raw/history fiber. It asserts no physical acquisition, resource bound, general solver, infinite completion interpretation or conclusion about other row pairs."))), DescribeRole.Theorem)
        )));

    private static Formula ChoiceFormula()
    {
        var history = Call("subtype",V("H"),V("supported"));
        var empty = Some("s",Bool,AndOf(All("u",Source,NotOf(Call("Stratum",V("s"),history,V("u")))),
            NotOf(Call("J",history,D(0)))));
        return All("H",V("OriginalHistory"),All("supported",Call("Supported",V("H")),
            OrOf(empty,All("h",Nat,Call("J",history,V("h"))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula AndOf(params Formula[] xs) => xs.Length == 1 ? xs[0] :
        Seq(Par(xs[0]),Sp,Land,Sp,Par(AndOf(xs.Skip(1).ToArray())));
    private static Formula OrOf(Formula a, Formula b) => Seq(Par(a),Sp,Lor,Sp,Par(b));
    private static Formula NotOf(Formula a) => Seq(Neg,Sp,Par(a));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall,Sp,
        Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()),
        Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists,Sp,
        Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()),
        Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(LambdaLower,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Source => V("Source");
    private static Formula Addr => V("Address");
    private static Formula Nat => V("Nat");
    private static Formula Bool => V("Bool");
    private static Formula Hist => V("History");
    private static Formula Alpha => Call("of",V("true"));
}
