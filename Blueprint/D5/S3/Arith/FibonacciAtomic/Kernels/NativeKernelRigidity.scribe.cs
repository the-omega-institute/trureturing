using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Kernels;

internal sealed class NativeKernelRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Kernels/NativeKernelRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every Hermitian complex kernel preserved by native Fibonacci substitution and exactly multiplicative on all ordered constructor pairs takes only zero and one.",
        H("Exact Kernel Rigidity on All Native Source Trees"),
        Blocks(
            Paragraph(Text("T is GenealogicalFiberTransport.Source, namely FreeMagma Bool: all nonempty finite ordered binary trees. "
                + "Alpha is the leaf true, beta is the leaf false, and pair(s,t) is the internal node with ordered children s,t. "
                + "The native substitution rho sends alpha to beta, beta to pair(beta,alpha), and pair(s,t) to pair(rho(s),rho(t)). "
                + "No quotient or bound on shape, height or leaf count is imposed. Complex is the complex scalar field and conj is complex conjugation.")),
            Describe.Lean(DescribeId.Create("native-kernel-zero-or-one"),
                DeclarationHandle.Create(Prefix + "kernel_zero_or_one"),
                H("The Full-Tree Zero-or-One Theorem"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("K is any total function T to T to Complex. The three premises are Hermitian symmetry for every source pair, "
                        + "preservation of every comparison by rho, and exact constructor multiplicativity for every source quadruple, "
                        + "including different tree shapes and repeated labels. The conclusion holds for every source pair. "
                        + "Positivity, diagonal normalization, faithfulness and regularity are not premises.")),
                    Paragraph(Text("Write R(n,u)=rho^n(u), f(n,u)=K(alpha,R(n,u)), and a(n)=f(n,alpha). "
                        + "The alpha-orbit part of SourceTransportCentralizer.source_transport_centralizer gives "
                        + "rho(rho(R(n,alpha)))=pair(rho(R(n,alpha)),R(n,alpha)). It is used only on that orbit. "
                        + "Two transport steps and multiplicativity give a(n)=a(n)*a(n), so the scalar idempotence theorem gives a(n)=0 or a(n)=1.")),
                    Paragraph(Text("For arbitrary s,t and every natural n, the same two transport steps give "
                        + "f(n,pair(s,t))=f(n+1,s)*f(n+2,t). The leaf beta gives f(n,beta)=a(n+1). "
                        + "Structural induction on the entire tree u, with n universally quantified, therefore gives f(n,u)=0 or f(n,u)=1.")),
                    Paragraph(Text("For beta in the first argument, Hermitian symmetry and transport settle the two leaves. "
                        + "The orbit identity at beta and exact multiplicativity give "
                        + "K(beta,pair(s,t))=K(alpha,s)*K(alpha,rho(t)), also zero or one. "
                        + "Finally, structural induction on the first tree handles all comparisons. A leaf first argument uses these two rows; "
                        + "an internal first argument against a leaf uses Hermitian symmetry; two internal arguments reduce by multiplicativity "
                        + "to comparisons with strictly smaller first trees. Conjugation and multiplication preserve zero and one."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Map(Formula a, Formula b) => Seq(a, Sp, To, Sp, Par(b));

    private static Formula ResultFormula()
    {
        Formula tree = V("T"), complex = Call("Complex");
        Formula s = V("s"), t = V("t"), u = V("u"), v = V("v");
        Formula K(Formula a, Formula b) => Call("K", a, b);
        Formula R(Formula a) => Call("rho", a);
        Formula Pair(Formula a, Formula b) => Call("pair", a, b);
        Formula hermitian = All("s", tree, All("t", tree,
            EqOf(K(t, s), Call("conj", K(s, t)))));
        Formula transport = All("s", tree, All("t", tree,
            EqOf(K(R(s), R(t)), K(s, t))));
        Formula multiplicative = All("s", tree, All("t", tree, All("u", tree, All("v", tree,
            EqOf(K(Pair(s, t), Pair(u, v)), Seq(K(s, u), Sp, Cdot, Sp, K(t, v)))))));
        Formula conclusion = All("s", tree, All("t", tree,
            Seq(Par(EqOf(K(s, t), D(0))), Sp, Lor, Sp, Par(EqOf(K(s, t), D(1))))));
        return Disp(All("K", Map(tree, Map(tree, complex)),
            Imp(hermitian, Imp(transport, Imp(multiplicative, conclusion)))));
    }
}
