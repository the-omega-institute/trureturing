using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualImageSevenLeafSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct equal-size three-step Fibonacci tree images have at least seven unshared leaves.",
        H("Seven-Leaf Separation of Actual Tree Images"), Blocks(
            Paragraph(Text("Sources are nonempty finite ordered full binary trees with alpha and beta leaves. "
                + "The substitution rho sends alpha to beta and beta to (beta,alpha), and preserves pairing. "
                + "I is the range of rho cubed on these complete sources. L(P) is the existing leaf-address set, "
                + "with root-first Boolean paths: false means left and true means right. Composition counts alpha and beta leaves.")),
            Def("n", "Leaf count", "n(P) is the cardinality of L(P)."),
            Def("s", "Shared leaf count", "s(P,Q) is the cardinality of the intersection of L(P) and L(Q)."),
            Def("nu", "Unshared leaf count", "nu(P,Q)=n(P)-s(P,Q), the number of leaves of P whose addresses are not leaves of Q."),
            Def("NC", "Nonconflicting leaf labels", "NC(P,Q) means that the existing endpoint observations agree at every shared leaf address. "
                + "A leaf of one tree may be a branch or absent in the other; such addresses impose no agreement condition."),
            Def("E", "Terminal pair", "E=(beta,alpha)."),
            Def("A", "Alpha image", "A=(E,beta)=rho cubed(alpha), with three leaves."),
            Def("C", "Beta image", "C=(A,E)=rho cubed(beta), with five leaves."),
            Def("B", "Smallest compatible compound", "B=(C,A), with eight leaves."),
            Describe.Lean(DescribeId.Create("actual-image-seven-leaf-separation-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Sharp separation and the smallest pair"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("P13=(C,(A,C)) and Q13=((A,C),C). Their respective literal preimages are "
                        + "(beta,(alpha,beta)) and ((alpha,beta),beta). They are distinct nonconflicting actual images, "
                        + "both have composition (5,8) and thirteen leaves, and they share six leaf addresses. "
                        + "Thus each has exactly seven unshared leaves. These equalities and preimages are included in the theorem.")),
                    Paragraph(Text("Every actual image is A, C, or a pair of actual images. In a nonconflicting atom-compound comparison, "
                        + "the atom has fewer leaves, the two leaf counts are at least three and eight, and the unshared counts "
                        + "are at least two and five. Shared and unshared counts add across the two child addresses. "
                        + "Recursive comparison therefore either retains one strict orientation or encounters opposite orientations, "
                        + "which contribute at least eleven leaves and seven unshared leaves on each side. Equal total sizes require the latter case.")),
                    Paragraph(Text("The actual images of at most eight leaves are A, C, (A,A), (A,C), and (C,A). "
                        + "An eleven-leaf image has two children in that list. The resulting six ordered possibilities have exactly "
                        + "one distinct nonconflicting unordered pair: (A,B) and (B,A). This pair has no shared leaves. "
                        + "Every finite pairwise nonconflicting family of eleven-leaf actual images consequently has at most two members.")),
                    Paragraph(Text("Substitution trees, Fibonacci trees and their leaf-induced subtrees are established neighboring subjects. "
                        + "Patera's Generating the Fibonacci Chain in O(log n) Space and O(n) Time studies generation of substitution words; "
                        + "Legendre's Labeled Fibonacci Trees studies integer labels; Dossou-Olory's Leaf-Induced Subtrees of Leaf-Fibonacci Trees "
                        + "counts induced subtree shapes. The statement here concerns fixed address intersections and label compatibility of complete ordered substitution images."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-image-seven-leaf-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string x) => F.Id(x);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(
        Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
    private static Formula In(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x,i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, Par(y));
    private static Formula All(string x, Formula domain, Formula body) =>
        Seq(Forall, Sp, V(x), Sp, InMacro, Sp, domain, Comma, Sp, Par(body));
    private static Formula ResultFormula()
    {
        Formula p=V("P"), q=V("Q"), np=Call("n",p), nq=Call("n",q);
        Formula distinct=Seq(Neg,Par(Equal(p,q)));
        Formula hypotheses=And(distinct,Equal(np,nq),Call("NC",p,q));
        Formula bound=All("P",V("I"),All("Q",V("I"),Imp(hypotheses,And(
            Le(D(1,1),np),Equal(Call("nu",p,q),Call("nu",q,p)),Le(D(7),Call("nu",p,q)),
            Le(Call("s",p,q),Seq(np,Sp,Minus,Sp,D(7)))))));
        Formula p13=V("P13"),q13=V("Q13");
        Formula psrc=Call("pair",V("beta"),Call("pair",V("alpha"),V("beta")));
        Formula qsrc=Call("pair",Call("pair",V("alpha"),V("beta")),V("beta"));
        Formula attained=Seq(Exists,Sp,p13,Comma,Sp,q13,Comma,Sp,Par(And(
            Equal(p13,Call("pair",V("C"),Call("pair",V("A"),V("C")))),
            Equal(q13,Call("pair",Call("pair",V("A"),V("C")),V("C"))),
            Equal(p13,Call("rho3",psrc)),Equal(q13,Call("rho3",qsrc)),
            In(p13,V("I")),In(q13,V("I")),Seq(Neg,Par(Equal(p13,q13))),
            Call("NC",p13,q13),Equal(Call("c",p13),Call("pair",D(5),D(8))),
            Equal(Call("c",q13),Call("pair",D(5),D(8))),Equal(Call("n",p13),D(1,3)),
            Equal(Call("n",q13),D(1,3)),Equal(Call("s",p13,q13),D(6)),
            Equal(Call("nu",p13,q13),D(7)),Equal(Call("nu",q13,p13),D(7)))));
        Formula x=Call("pair",V("A"),V("B")),y=Call("pair",V("B"),V("A"));
        Formula classify=All("P",V("I"),All("Q",V("I"),Imp(And(distinct,Equal(np,D(1,1)),
            Equal(nq,D(1,1)),Call("NC",p,q)),Equal(Call("set",p,q),Call("set",x,y)))));
        Formula converse=And(In(x,V("I")),In(y,V("I")),Seq(Neg,Par(Equal(x,y))),
            Equal(Call("n",x),D(1,1)),Equal(Call("n",y),D(1,1)),Call("NC",x,y));
        Formula family=All("F",Call("Finset",V("Source")),Imp(And(
            All("P",V("F"),And(In(p,V("I")),Equal(np,D(1,1)))),
            All("P",V("F"),All("Q",V("F"),Imp(distinct,Call("NC",p,q))))),Le(Call("card",V("F")),D(2))));
        return Disp(And(bound,attained,classify,converse,family));
    }
}
