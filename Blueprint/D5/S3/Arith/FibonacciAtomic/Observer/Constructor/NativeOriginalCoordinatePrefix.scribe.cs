using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeOriginalCoordinatePrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalCoordinatePrefix.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Additive finite lookahead and executable decoding of actual native image prefixes.",
        H("Original prefixes from finite native image data"), Blocks(
            Paragraph(Text("A completed native tree is either an alpha leaf, a beta leaf, or an ordered pair. Arbitrary infinite and non-rational trees are included. An address is a finite list of Bool child choices. Its reply is alpha, beta, branch, or absent. Descendants of a leaf are absent. The native substitution rho maps alpha to beta, beta to the pair (beta,alpha), and preserves pairs. The finite Source substitution has the same action. Powers include zero.")),
            Paragraph(Text("Put H(s)=max(height(substitution^s(alpha)),height(substitution^s(beta))). These are actual finite terminal trees; the height of a leaf is zero and the height of a pair is one plus the larger child height. Thus H(0)=0. cutoff(d,X) retains all replies strictly above depth d, with holes only at reached positions of depth d. Inclusive depth h therefore uses cutoff h+1.")),
            Describe.Lean(DescribeId.Create("original-additive-prefix-agreement"),
                DeclarationHandle.Create(Prefix + "inverse_prefix_agreement"),
                H("Additive image agreement determines original agreement"),
                StatementSource.FromAuthor(Disp(Agreement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The quantifiers range over every natural s,h and arbitrary completed originals U,V. Image agreement is required at every address of length at most h+H(s). The conclusion is agreement of the originals at every address of length at most h, including absent descendants. Equivalently the images can be any two members of the actual language L_s, with U,V their unique actual preimages.")),
                    Paragraph(Text("Agreement through the finite height of a terminal forces a completed tree to equal that terminal. Applying this to the two actual leaf images, then using injectivity of rho^s, distinguishes leaves from each other and from a pair. If both originals are pairs, their images are pairs with exactly the images of the original children. Descending to a child consumes one level on both sides. H(s) is added once at the root, rather than at every ancestor."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-finite-prefix-decoder"),
                DeclarationHandle.Create(Prefix + "decode_prefix_correct"),
                H("A finite decoder recovers every promised-image prefix"),
                StatementSource.FromAuthor(Disp(Decoder())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("decodePrefix(s,d) has only a finite pattern of depth H(s)+d as input and returns a finite original pattern of depth d. It takes no completed tree, infinite image oracle, choice function or inverse service as an argument. At zero output depth it returns the single hole. At positive depth it compares the current finite image pattern against the actual finite alpha and beta image terminals. terminalMatch visits only the finite terminal's own addresses, stopping at each terminal leaf; a terminal of height at most H(s) needs no reply deeper than H(s) below the current address. A successful comparison returns the corresponding original leaf. Otherwise a pair pattern is decoded recursively on its two child patterns. An off-image leaf pattern has a total fallback, with no correctness claim outside promised actual images.")),
                    Paragraph(Text("Terminal isolation and native injectivity prove that on an actual image a successful comparison occurs exactly for the corresponding original leaf. A true original pair therefore takes the recursive case. Induction on requested output depth proves the displayed equality for every completed original X. Recovered leaves encode absent descendants without exploring them. The statement includes s=0, output depth zero, inclusive h=0 by d=1, and completed outputs that have no finite rational presentation.")),
                    Paragraph(Text("Application to an actual canonical image uses NativeFunctionalEffectivePrefix.prefixProgram(S,mode,p,R,H(s)+h,i) at supplied shared parameters p and inclusive depth H(s)+h, followed by decodePrefix(s,h+1). The existing effective_prefix theorem identifies this finite image program with the cutoff of the canonical value of R(i). Once the actual normalization/reconstruction bridge identifies that same canonical value as rho^s of the desired original, the decoder equality gives its original cutoff h+1. This composition introduces no infinite-tree oracle. The current module supplies the decoder; it does not establish the missing common-shift reconstruction bridge, the finite symbolic inverse q+s=n, a Presburger partition, or canonical finite rigidity for every normalized original coordinate. The full source theorem and unrestricted acquired-input obligations remain open. No runtime inverse port or physical query-cost theorem is asserted."))), DescribeRole.Theorem)
        )));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [..xs]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula All(string n, Formula type, Formula body) => Seq(Forall,Sp,V(n),Colon,Sp,type,Comma,Sp,Par(body));
    private static Formula Equal(Formula x, Formula y) => Seq(x,Sp,Eq,Sp,y);
    private static Formula Add(Formula x, Formula y) => Seq(x,Plus,y);
    private static Formula ReplyAgreement(Formula u, Formula v, Formula depth) =>
        All("p",V("Address"),Seq(Call("length",V("p")),Le,Sp,depth,Sp,Implies,Sp,
            Equal(Call("reply",V("p"),u),Call("reply",V("p"),v))));
    private static Formula Agreement() => All("s",V("Nat"),All("h",V("Nat"),
        All("U",V("CompletionTree"),All("V",V("CompletionTree"),Seq(
            Par(ReplyAgreement(Call("rhoPower",V("s"),V("U")),Call("rhoPower",V("s"),V("V")),Add(V("h"),Call("H",V("s"))))),
            Sp,Implies,Sp,Par(ReplyAgreement(V("U"),V("V"),V("h"))))))));
    private static Formula Decoder() => All("s",V("Nat"),All("d",V("Nat"),
        All("X",V("CompletionTree"),Equal(
            Call("decodePrefix",V("s"),V("d"),Call("cutoff",Add(Call("H",V("s")),V("d")),Call("rhoPower",V("s"),V("X")))),
            Call("cutoff",V("d"),V("X"))))));
}
