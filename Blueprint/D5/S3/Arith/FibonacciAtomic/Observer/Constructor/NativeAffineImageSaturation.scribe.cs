using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeAffineImageSaturationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "NativeAffineImageSaturation",H("Original image saturation with guarded affine atomic indices"),Blocks(
            Describe.Lean(DescribeId.Create("native-affine-original-image-saturation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeAffineImageSaturation.affine_original_saturation"),
                H("The exact original parameter map and joint canonical test"),Statement(),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("An input has n original natural parameters, k finite symbolic atomic terminals and m original state names. It contains an arbitrary optional-definition system and its full list of actual-image filters, a list q of integer affine expressions for the finite terminal indices, and an original Presburger formula Gamma. Affine expressions use the existing constant and coefficient-list syntax; negative coefficients and constants are permitted. Missing coefficients evaluate to zero. The original parameter tuple p is embedded, in order, into the integer valuation list.")),
                    Paragraph(Text("Legal means that Gamma holds on this same valuation and every listed terminal index q(j)(p) is nonnegative. These are the original syntactic parameter guards. The derived terminal-rank map is r(j) = toNat(q(j)(p)). The theorem proves int(r(j)) = q(j)(p) for every j using the nonnegativity guard. Thus no clipping occurs on a legal input, and the terminal ranks are functions of the original p rather than additional independent variables. A token with fixed natural offset c denotes exactly the finite atom T(r(j)+c); an arbitrary affine index can be listed with offset zero. Repeated uses of a terminal name share the same affine value, and coincident affine values remain permitted.")),
                    Paragraph(Text("SourceSatisfies, SourcePasses and SourceInMode specialize the original equations, actual-image filters and normalized free-list mode at this exact rank map. The last expression token denotes the actual infinite Omega and has no affine rank. Finite grounds, fixed state powers, ordered pairs, original names and all repeated filter occurrences remain unchanged. No parameter value is enumerated, and the guard is not replaced by an assumed normalization property.")),
                    Paragraph(Text("Apply the constructed two-sided original-system normalization and its simultaneous saturation theorem at r. The resulting sourceCanonical satisfies every original equation and the specified mode. There is an original solution in that mode passing every original image filter if and only if sourceCanonical passes every one of them. This establishes the NIS.15 existence equivalence at every fixed legal p, while retaining the exact affine-to-natural correspondence. Arbitrarily infinite and non-rational completed state values remain in scope; this conclusion does not assert uniqueness among live original solutions or compute the separate Presburger acceptance predicate of NIS.16."))
                ),DescribeRole.Theorem)
        )));
    private static StatementSource Statement()
    {
        var n=V("n"); var k=V("k"); var m=V("m"); var input=V("I"); var p=V("p"); var mode=V("mode");
        var canonical=Call("sourceCanonical",input,p,mode);
        Formula Sat(Formula x)=>Call("SourceSatisfies",input,p,x);
        Formula InModeOf(Formula x)=>Call("SourceInMode",input,p,mode,x);
        Formula Pass(Formula x)=>Call("SourcePasses",input,p,x);
        var parameterMap=All("j",Call("Fin",k),EqOf(Call("Int.ofNat",Call("ranks",input,p,V("j"))),
            Call("Affine.eval",Call("indices",input,V("j")),Call("environment",p))));
        var existence=Some("v",Arr(Call("Fin",m),V("CompletionTree")),
            And(Sat(V("v")),And(InModeOf(V("v")),Pass(V("v")))));
        var body=And(parameterMap,And(Sat(canonical),And(InModeOf(canonical),IffOf(existence,Pass(canonical)))));
        return StatementSource.FromAuthor(Disp(All("n",V("Nat"),All("k",V("Nat"),All("m",V("Nat"),
            All("I",Call("Input",n,k,m),All("p",Arr(Call("Fin",n),V("Nat")),
                All("legal",Call("Legal",input,p),All("mode",Call("FreeMode",Call("equations",input),
                    Call("threshold",Call("filters",input))),body)))))))));
    }
    private static Formula V(string n)=>F.Id(n);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] args)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..args]);
    private static Formula EqOf(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula And(Formula a,Formula b)=>Seq(Par(a),Sp,Land,Sp,Par(b));
    private static Formula IffOf(Formula a,Formula b)=>Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Arr(Formula a,Formula b)=>Seq(a,Sp,To,Sp,b);
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b)=>Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
