using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeRootLinkNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "NativeRootLinkNormalization",H("Root-link normalization on the unrestricted native completion"),Blocks(
            Describe.Lean(DescribeId.Create("native-root-link-normalization"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRootLinkNormalization.root_link_normalization"),
                H("Inverse solution maps with every original reconstruction"),Statement(),
                AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("An input S has finitely many named states and at most one optional definition for each. An absent definition imposes no constraint. Its finite expressions contain finite grounds, finite symbolic atomic terminals, Omega, fixed nonnegative native powers of states, and ordered pairs. A defining root may be a decorated state reference. State assignments range over the entire polynomial-functor completion, including infinite trees without finite descriptions.")),
                    Paragraph(Text("A presentation T contains a new optional-definition system on the same finite index set and two lists of finite expressions: project maps original solutions to normalized solutions, while reconstruct recovers every original named state. Correct means that, for every finite terminal-rank tuple p, each map sends a solution to a solution and both composites equal the identity on their respective full solution sets. The theorem constructs T with no decorated state reference at a defining root. It assumes neither guardedness nor uniqueness of extension for S.")),
                    Paragraph(Text("For a root equation Xi = rho(a)(Xj) with distinct indices, substitute its right side at every occurrence of Xi, distributing decorators through finite syntax. Replace the eliminated coordinate by the fixed ground alpha in the new system. Projection sets that slot to alpha; reconstruction sets its original value to rho(a)(Xj). The other coordinates and all their ordered occurrences are retained. These explicit maps are inverse on solutions. The fixed ground slot supplies no new free value and does not assert that the original Xi was alpha.")),
                    Paragraph(Text("For Xi = Xi, remove only the defining equation, making that coordinate genuinely free. For Xi = rho(a)(Xi) with positive a, replace the definition by Xi = Omega. Iterating the original period gives arbitrarily deep full branch prefixes: rho(2n) makes every prefix above depth n a branch. Equality of every reply therefore forces the actual leafless Omega; conversely every native iterate fixes Omega. This uses the interpreted native substitution rather than treating its symbol as a free constructor.")),
                    Paragraph(Text("Each step strictly decreases the finite set of defining root links. Substitution preserves a ground, symbolic terminal or explicit pair root, so it cannot introduce a root link at a previously non-link definition. Strong induction constructs a guarded presentation. Composing the finite expression maps composes the exact solution correspondences, retaining all original names, shared references, repetitions and ordered pairs. The normalization is uniform in finite terminal ranks; no rank values are enumerated."))
                ),DescribeRole.Theorem)
        )));
    private static StatementSource Statement()
    {
        var k=V("k"); var m=V("m"); var s=V("S"); var t=V("T");
        var body=Some("T",Call("Presentation",k,m),And(Call("Guarded",Call("equations",t)),Call("Correct",s,t)));
        return StatementSource.FromAuthor(Disp(All("k",V("Nat"),All("m",V("Nat"),
            All("S",Call("System",k,m),body)))));
    }
    private static Formula V(string n)=>F.Id(n);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] args)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..args]);
    private static Formula And(Formula a,Formula b)=>Seq(Par(a),Sp,Land,Sp,Par(b));
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b)=>Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
