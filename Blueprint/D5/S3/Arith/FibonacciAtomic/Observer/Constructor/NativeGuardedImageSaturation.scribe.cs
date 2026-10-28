using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeGuardedImageSaturationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "NativeGuardedImageSaturation",H("Joint actual-image saturation for guarded native systems"),Blocks(
            Describe.Lean(DescribeId.Create("native-guarded-image-saturation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedImageSaturation.normalized_saturation"),
                H("One canonical same-mode extension tests all retained image filters"),Statement(),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("Let S be an arbitrary finite optional-definition system in the actual native completion. All state-dependent right sides have explicit pair roots. Expressions retain finite grounds, finite parameter atoms with fixed natural offsets, Omega, nonnegative powers of states and ordered pairs. The parameter tuple p is fixed and arbitrary. A filter is any expression C together with a natural threshold t, interpreted as membership of its whole actual value in range(rho(t)). The finite filter list retains every conjunct, including repetitions.")),
                    Paragraph(Text("Set s to the maximum of zero and all thresholds in that list. A free-state mode chooses, for each undefined state, either one actual exceptional atom atomic(j) with j in Fin(s+2), or the requirement that its value is unequal to every atomic(j) with j at most s+1. These are fixed and live conditions on whole unrestricted completed values, rather than on token labels or finite prefixes. A mode entry at a defined state has no effect.")),
                    Paragraph(Text("The canonical free assignment retains each selected fixed atom and assigns the actual leafless Omega to every live state. The previously established unique guarded extension defines its entire state tuple K. The theorem proves that K satisfies all definitions and its specified mode, and proves the joint equivalence: there exists a simultaneous solution of S in that mode passing the entire filter list if and only if that same canonical tuple K passes the entire list. The right-to-left implication uses K itself. This concerns existence in a mode; different live solutions need not be equal.")),
                    Paragraph(Text("For the forward implication, compare the given solution and K at the same p. Any free value that is atomic(j) with j at most s+1 must be in the fixed alternative, and is preserved. The bounded atomic replacement theorem then preserves every expression terminal atomic(t) or atomic(t+1) used at a threshold t at most s. At an explicit pair, the exact native image decomposition either selects one of those unchanged terminals or sends image obligations to both actual children.")),
                    Paragraph(Text("A positive decorator a at threshold t either supplies an image immediately when a is at least t, or cancels injectively to threshold t-a. Strong induction on the threshold handles this decrease. A zero-decorated state unfolds its actual defining equation, whose guarded root is constant or a pair; an undefined state is unchanged or replaced by Omega. Omega belongs to every actual image because it is fixed by every native iterate.")),
                    Paragraph(Text("The collected canonical obligations form a post-fixed relation for the actual image grammar. A corecursor chooses source leaves for its two terminal alternatives and source pairs for its pair alternatives. Induction at every cutoff depth proves that applying rho(t) to this unrestricted source tree gives the stipulated canonical value. Equality of all four-valued replies proves exact completed equality. Thus infinite parses have actual preimages, including non-rational ones; they are not replaced by finite-depth acceptance.")),
                    Paragraph(Text("This theorem starts with a normalized pair-guarded system. It does not construct root-link normalization, its original-state reconstruction maps, the two original-to-normalized solution correspondences, or the transport of additional original filters and affine parameter guards. Applying the result to an unnormalized system requires those correspondences with every filter and reconstruction retained. No bound on source size, depth, rank or rationality is imposed by the guarded result itself."))
                ),DescribeRole.Theorem)
        )));
    private static StatementSource Statement()
    {
        var k=V("k"); var m=V("m"); var s=V("S"); var p=V("p"); var f=V("filters"); var mode=V("mode");
        var height=Call("threshold",f); var tuple=Arr(Call("Fin",m),V("CompletionTree"));
        var canonical=Call("canonical",s,p,V("guarded"),mode);
        Formula InModeOf(Formula x)=>Call("InMode",s,height,mode,x);
        Formula Pass(Formula x)=>Call("Passes",p,x,f);
        var existence=Some("v",tuple,And(Call("Satisfies",s,p,V("v")),And(InModeOf(V("v")),Pass(V("v")))));
        var body=And(Call("Satisfies",s,p,canonical),And(InModeOf(canonical),IffOf(existence,Pass(canonical))));
        return StatementSource.FromAuthor(Disp(All("k",V("Nat"),All("m",V("Nat"),
            All("S",Call("System",k,m),All("p",Arr(Call("Fin",k),V("Nat")),
                All("guarded",Call("Guarded",s),All("filters",Call("List",Call("Filter",k,m)),
                    All("mode",Call("Mode",height,m),body)))))))));
    }
    private static Formula V(string n)=>F.Id(n);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] args)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..args]);
    private static Formula And(Formula a,Formula b)=>Seq(Par(a),Sp,Land,Sp,Par(b));
    private static Formula IffOf(Formula a,Formula b)=>Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Arr(Formula a,Formula b)=>Seq(a,Sp,To,Sp,b);
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b)=>Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
