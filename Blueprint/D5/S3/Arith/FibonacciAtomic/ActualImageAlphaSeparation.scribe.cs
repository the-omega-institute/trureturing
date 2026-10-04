using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualImageAlphaSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp alpha separation and the complete eleven-leaf classification of actual Fibonacci tree images.",
        H("Alpha Separation and Literal Two-Hole Equality"), Blocks(
            Paragraph(Text("Sources are nonempty finite ordered full binary trees with alpha and beta leaves. "
                + "The substitution rho sends alpha to beta and beta to (beta,alpha), and preserves pairing. "
                + "I is the range of rho cubed on these complete sources. L(P) is the existing leaf-address set, "
                + "with root-first Boolean paths: false means left and true means right. Composition counts alpha and beta leaves.")),
            Paragraph(Text("The leaf length n is FreeMagma.length. Shared leaves, unshared leaves, Nonconflict, E, A and C use ActualImageSevenLeafSeparation. "
                + "Its seven_leaf_separation theorem supplies the exact address semantics and Theorem 30.4. "
                + "A is pair(E,beta), C is pair(A,E), and E is pair(beta,alpha).")),
            Def("B", "Smallest compatible compound", "B=(C,A), with eight leaves."),
            Def("delta", "Directed alpha deficit", "delta(P,Q) is the cardinality of the set difference of the original alpha-leaf address sets. The prose notation μ(P) denotes the cardinality of the original alpha-leaf address set."),
            Def("OneHole", "One source hole", "A context has one hole, and is built by attaching complete fixed source trees on its left or right. "
                + "OneHole.fill(g,H,X) inserts X and applies g to each fixed source sibling. Using g=rho cubed makes all fixed siblings actual images; using the identity retains the preimage. "
                + "OneHole.address records every ordered left or right choice from the root."),
            Def("TwoHole", "Two source holes", "The outer one-hole context leads to the lowest common ancestor. Its left and right one-hole contexts lead to the two distinct holes. A Boolean records their naming order. "
                + "TwoHole.fill(J,g,X,Y) inserts the named trees exactly once, retaining the entire outer context and each fixed sibling. "
                + "TwoHole.addresses gives two addresses with the same outer prefix and opposite next bits, and hence neither is a prefix of the other."),
            Def("frontier", "Canonical divergence frontier", "Comparison is performed on complete preimages. Equal subtrees stop; two branches recurse into the ordered children; an atom-compound comparison records the current address."),
            Def("forwardCount", "Atomic-side hole count", "forwardCount(S,T) counts frontier holes whose S side is atomic and T side is compound."),
            Def("NormalForm", "Literal double-hole normal form", "NormalForm(S,T) retains a complete source context J and y equal to beta or (alpha,alpha), with S=fill(id,J,beta,(alpha,y)) and T=fill(id,J,(alpha,y),beta). "
                + "Its frontier is exactly the two named, mutually nonprefix addresses. Writing Y=rho cubed(y) and K=rho cubed(fill(id,J,beta,beta)), the actual trees are literally replace(replace(K,u,C),v,(A,Y)) and replace(replace(K,u,(A,Y)),v,C). Thus every fixed sibling has an actual preimage."),
            Describe.Lean(DescribeId.Create("actual-image-alpha-separation-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Eleven-Leaf Classification and Sharp Alpha Separation"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The actual images of at most eight leaves are A, C, (A,A), (A,C), and (C,A). "
                        + "An eleven-leaf image has two children in that list. The resulting six ordered possibilities have exactly "
                        + "one distinct nonconflicting unordered pair: (A,B) and (B,A). This pair has no shared leaves. "
                        + "Every finite pairwise nonconflicting family of eleven-leaf actual images consequently has at most two members.")),
                    Paragraph(Text("For all complete preimages S,T, put P=rho cubed(S) and Q=rho cubed(T). Distinct equal-leaf nonconflicting images have at least three alpha addresses missing in each direction. "
                        + "Either deficit equals three precisely when NormalForm(S,T) holds. The same Y is C or (A,A) at both holes. Equality implies identical compositions of both the actual trees and their preimages.")),
                    Paragraph(Text("Every complete two-hole source context and each permitted y produce distinct equal-leaf nonconflicting actual images with both directed alpha deficits equal to three. "
                        + "The canonical preimage frontier consists of exactly their two independent holes, and the actual tree equalities retain both address replacements. The total unshared leaf counts, denoted unsharedCount(y), are seven when y is beta, and eight when y is (alpha,alpha).")),
                    Paragraph(Text("At every atom-compound hole, the atomic side contributes at least one alpha deficit and the compound side at least two. Equal total leaf counts force both orientations to occur. "
                        + "A deficit of three forces exactly one hole in each orientation. A compound-side deficit of two forces the comparison C versus (A,Y), with Y=C or (A,A); its leaf increase is three or four. "
                        + "The other hole must balance this increase, excluding the alpha-atom comparison, whose increase is at least five. The unique five- and six-leaf images force the same Y at both holes. "
                        + "Deficits and compatibility add over distinct child addresses and are preserved by each common fixed sibling."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-image-alpha-" + name.ToLowerInvariant().Replace('.', '-')), DeclarationHandle.Create(Prefix + name),
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
        Formula x=Call("pair",V("A"),V("B")),y=Call("pair",V("B"),V("A"));
        Formula classify=All("P",V("I"),All("Q",V("I"),Imp(And(distinct,Equal(np,D(1,1)),
            Equal(nq,D(1,1)),Call("NC",p,q)),Equal(Call("set",p,q),Call("set",x,y)))));
        Formula converse=And(In(x,V("I")),In(y,V("I")),Seq(Neg,Par(Equal(x,y))),
            Equal(Call("n",x),D(1,1)),Equal(Call("n",y),D(1,1)),Call("NC",x,y));
        Formula family=All("F",Call("Finset",V("Source")),Imp(And(
            All("P",V("F"),And(In(p,V("I")),Equal(np,D(1,1)))),
            All("P",V("F"),All("Q",V("F"),Imp(distinct,Call("NC",p,q))))),Le(Call("card",V("F")),D(2))));
        Formula ss=V("S"),tt=V("T"),pp=Call("rho3",ss),qq=Call("rho3",tt);
        Formula dpq=Call("delta",pp,qq),dqp=Call("delta",qq,pp),nf=Call("NormalForm",ss,tt);
        Formula alphaHypotheses=And(Seq(Neg,Par(Equal(pp,qq))),
            Equal(Call("n",pp),Call("n",qq)),Call("NC",pp,qq));
        Formula alphaConclusions=And(
            Le(D(3),dpq),Le(D(3),dqp),Seq(Par(Equal(dpq,D(3))),Sp,Leftrightarrow,Sp,Par(nf)),
            Seq(Par(Equal(dqp,D(3))),Sp,Leftrightarrow,Sp,Par(nf)),Imp(Equal(dpq,D(3)),And(
                Equal(Call("c",pp),Call("c",qq)),Equal(Call("c",ss),Call("c",tt)))));
        Formula alpha=All("S",V("Source"),All("T",V("Source"),Imp(alphaHypotheses,alphaConclusions)));
        Formula j=V("J"),yy=V("y"),small=Seq(Par(Equal(yy,V("beta"))),Sp,Lor,Sp,
            Par(Equal(yy,Call("pair",V("alpha"),V("alpha")))));
        Formula sx=Call("fill",Call("id"),j,V("beta"),Call("pair",V("alpha"),yy));
        Formula tx=Call("fill",Call("id"),j,Call("pair",V("alpha"),yy),V("beta"));
        Formula px=Call("rho3",sx),qx=Call("rho3",tx),count=Call("unsharedCount",yy);
        Formula alphaConverse=All("J",V("TwoHole"),All("y",V("Source"),Imp(small,And(
            In(px,V("I")),In(qx,V("I")),Call("NormalForm",sx,tx),Seq(Neg,Par(Equal(px,qx))),
            Equal(Call("n",px),Call("n",qx)),Call("NC",px,qx),
            Equal(Call("delta",px,qx),D(3)),Equal(Call("delta",qx,px),D(3)),
            Equal(Call("c",px),Call("c",qx)),Equal(Call("c",sx),Call("c",tx)),
            Equal(Call("nu",px,qx),count),Equal(Call("nu",qx,px),count)))));
        return Disp(And(And(classify,converse,family),alpha,alphaConverse));
    }
}
