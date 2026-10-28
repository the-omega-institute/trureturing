using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeOriginalReconstructionBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact epoch transport, canonical original rigidity and executable original prefixes.",
        H("Original coordinates of a passing native image mode"), Blocks(
            Paragraph(Text("An EpochInput I has n original natural parameters, k affine atomic indices, m state names, an optional equation at each name, a head power a(i), the original Presburger guard, and every original actual-image filter. A defined equation is rho to power a(i) of X(i) equal to its stored right side. Expressions contain arbitrary finite grounds, finite parameter atoms with fixed offsets, the explicit Omega token, decorated state occurrences and ordered pairs. A Potential s is a natural tuple satisfying a(i) at most s(i) and s(j) at most b+s(i)-a(i) at each occurrence rho to power b of X(j). These are the natural form of NIS.11 supplied by Theorem 3.3. No semantic identity or inverse is a field of the input.")),
            Paragraph(Text("imageValues(s,v)(i) is rho to power s(i) of v(i). transport(s,t,E) distributes a shift t through finite grounds, token offsets and pairs, replacing an occurrence rho to power b of X(j) by rho to power b+t-s(j) of Y(j). ShiftLegal checks every exponent before its use. commonShift(s) is the maximum of zero and all s(i), computed by a finite fold; it works for every reconstruction and additional filter and is independent of the requested depth and parameters.")),
            Describe.Lean(DescribeId.Create("epoch-full-solution-correspondence"),
                DeclarationHandle.Create(Prefix + "epoch_solution_correspondence"),
                H("The entire decorated solution relation is transported in both directions"),
                StatementSource.FromAuthor(Disp(Epoch())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("functionalInput applies the head shift s(i)-a(i) to each defined equation. It retains a state-image filter Y(i) in L at threshold s(i) for every name, including undefined states. An original filter C in L at threshold r becomes transport(s,t,C) in L at threshold r+t with t=commonShift(s). Every occurrence and repetition remains in the list. The affine indices and original legal domain are unchanged. OriginalAdmissible means the original legal domain, every decorated equation, and every original image filter, jointly.")),
                    Paragraph(Text("Structural induction proves the literal evaluation identity for transport on every legal shift. Native injectivity recovers the original decorated equations from the shifted equations. The state-image filters provide every actual preimage, and injectivity makes their joint tuple unique. Applying injectivity once more proves both directions for every additional shifted filter. The result concerns entire completed assignments; arbitrary infinite and non-rational values are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-shift-original-reconstruction"),
                DeclarationHandle.Create(Prefix + "reconstruction_transport"),
                H("Every original reconstruction has its actual common-shift image"),
                StatementSource.FromAuthor(Disp(Transport())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every finite native expression E and every original assignment v, the distributed expression is exactly rho to power commonShift(s) of the original evaluation. Its actual-image membership is proved by that original evaluation as witness. This includes zero states, zero shift, mixed pairs, repeated names, arbitrary grounds and the explicit Omega. The expression identity and image membership are conclusions of the syntax induction, rather than assumptions about a reconstruction context."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-actual-reconstruction-image"),
                DeclarationHandle.Create(Prefix + "canonical_reconstruction_image"),
                H("The finite guarded evaluator denotes the actual original image"),
                StatementSource.FromAuthor(Disp(CanonicalImage())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("presentation is the existing executable root-link normalization of functionalInput, retaining both reconstruction and projection maps. reconstructionImages substitutes its retained reconstruction into the distributed common-shift expression. canonicalSystem fixes each exceptional finite normalized free atom by a ground equation and leaves live free names undefined. Its existing leaf-limit canonicalSolution therefore assigns Omega to live names. Guarded uniqueness identifies this solution with the saturation canonical extension.")),
                    Paragraph(Text("Passing is the actual computed originalImageGuard of functionalInput at the same original parameter tuple. The existing exact image-guard theorem supplies legality and every retained filter. The epoch correspondence then supplies canonicalOriginal as the unique original preimage of effectiveCanonical. The displayed equality connects the symbolic finite-forcing and finite prefix APIs to this actual original reconstruction. No rational presentation is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-canonical-rigidity-prefix"),
                DeclarationHandle.Create(Prefix + "original_classification_rigidity_prefix"),
                H("Decidable canonical finiteness, same-parameter rigidity and effective original prefixes"),
                StatementSource.FromAuthor(Disp(Rigidity())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("finiteReconstructions is the existing finite symbolic pass, applied to canonicalSystem and reconstructionImages. It is executable and independent of p. Native powers preserve and reflect finiteness, so membership decides exactly the finiteness of each canonical original reconstruction. For each finite member the theorem produces one finite Source g equal to that reconstruction and to the reconstruction in every original admissible solution whose shifted assignment belongs to the same projected normalized mode. All such solutions use the same original p.")),
                    Paragraph(Text("Only exceptional finite free values are fixed in canonicalSystem. Every original alternative in that mode satisfies these equations; live free states remain unrestricted. Existing symbolic_finite_forcing therefore fixes the common-shift image, and injectivity fixes its original value. This clause does not say that an alternative value of a canonically infinite coordinate is infinite. Symbolic finite inversion with an original-parameter Presburger partition is supplied by NativeFiniteNormalInversion.original_symbolic_finite_value.")),
                    Paragraph(Text("originalPrefixProgram runs the existing finite guarded image prefix program at inclusive depth H(t)+h and decodes its result at output cutoff h+1. Pattern d observes addresses of length strictly less than d; hence the image cutoff is H(t)+h+1=H(t)+(h+1). The existing decoder proves equality with the original cutoff for every supplied h and p, including h=0 and t=0. This constructs prefixes offline and asserts no physical inverse port, query cost or uniform runtime bound."))), DescribeRole.Theorem)
        )));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [..xs]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,V(s),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists,Sp,V(s),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a),Sp,Land,Sp,Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula Nat => V("Nat");
    private static Formula Values => Arr(C("Fin",V("m")),V("CompletionTree"));
    private static Formula Ranks => C("ranks",C("base",V("I")),V("p"));
    private static Formula J => C("functionalInput",V("I"),V("s"));
    private static Formula Shift => C("commonShift",V("s"));
    private static Formula K => C("canonicalOriginal",V("I"),V("s"),V("valid"),V("mode"),V("p"),V("passing"));
    private static Formula Eval(Formula v) => C("evaluate",Ranks,v,C("R",V("i")));
    private static Formula SameMode(Formula v) => C("EffectiveInMode",J,V("mode"),V("p"),C("imageValues",V("s"),v));
    private static Formula Admissible(Formula v) => C("OriginalAdmissible",V("I"),V("p"),v);
    private static Formula Power(Formula t, Formula x) => C("rhoPower",t,x);
    private static Formula Dims(Formula b, bool r=false) => All("n",Nat,All("k",Nat,All("m",Nat,
        r ? All("r",Nat,b) : b)));
    private static Formula Context(Formula b, bool reconstruction) => Dims(All("I",C("EpochInput",V("n"),V("k"),V("m")),
        All("s",Arr(C("Fin",V("m")),Nat),All("valid",C("Potential",V("I"),V("s")),
        All("mode",C("EffectiveMode",J), reconstruction ? All("R",Arr(C("Fin",V("r")),C("Expression",V("k"),V("m"))),b) : b)))),reconstruction);
    private static Formula AtPassing(Formula b) => All("p",Arr(C("Fin",V("n")),Nat),
        All("passing",C("holds",C("originalImageGuard",J,V("mode")),C("environment",V("p"))),b));
    private static Formula Epoch()
    {
        var rhs=Some("v",Values,And(And(Admissible(V("v")),EqOf(C("imageValues",V("s"),V("v")),V("w"))),
            All("u",Values,Imp(And(Admissible(V("u")),EqOf(C("imageValues",V("s"),V("u")),V("w"))),EqOf(V("u"),V("v"))))));
        var lhs=And(C("Legal",J,V("p")),And(C("SourceSatisfies",J,V("p"),V("w")),C("SourcePasses",J,V("p"),V("w"))));
        return Dims(All("I",C("EpochInput",V("n"),V("k"),V("m")),All("s",Arr(C("Fin",V("m")),Nat),
            All("valid",C("Potential",V("I"),V("s")),All("p",Arr(C("Fin",V("n")),Nat),All("w",Values,IffOf(lhs,rhs)))))));
    }
    private static Formula Transport()
    {
        var original=C("evaluate",V("p"),V("v"),V("E"));
        var image=C("evaluate",V("p"),C("imageValues",V("s"),V("v")),C("transport",V("s"),Shift,V("E")));
        return All("k",Nat,All("m",Nat,All("s",Arr(C("Fin",V("m")),Nat),
            All("p",Arr(C("Fin",V("k")),Nat),All("v",Values,All("E",C("Expression",V("k"),V("m")),
                And(EqOf(image,Power(Shift,original)),C("NativeImage",Shift,image))))))));
    }
    private static Formula CanonicalImage() => Context(AtPassing(All("i",C("Fin",V("r")),
        EqOf(C("value",C("tokenKind",V("k")),C("tokenRank",Ranks),
            C("canonicalSolution",C("canonicalSystem",V("I"),V("s"),V("mode")),C("tokenKind",V("k")),C("tokenRank",Ranks)),
            C("reconstructionImages",V("I"),V("s"),V("R"),V("i"))),Power(Shift,Eval(K))))),true);
    private static Formula Rigidity()
    {
        var finite=Seq(V("i"),Sp,InMacro,Sp,C("finiteReconstructions",V("I"),V("s"),V("mode"),V("R")));
        var fixedValue=Some("g",V("Source"),And(EqOf(Eval(K),C("embed",V("g"))),
            All("v",Values,Imp(Admissible(V("v")),Imp(SameMode(V("v")),EqOf(Eval(V("v")),C("embed",V("g"))))))));
        var prefixes=All("h",Nat,EqOf(C("originalPrefixProgram",V("I"),V("s"),V("mode"),V("p"),V("R"),V("h"),V("i")),
            C("cutoff",Seq(V("h"),Plus,F.D(1)),Eval(K))));
        return Context(AtPassing(And(Admissible(K),All("i",C("Fin",V("r")),
            And(IffOf(C("IsFinite",Eval(K)),finite),And(Imp(finite,fixedValue),prefixes))))),true);
    }
}
