using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourExitRawDominationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every original strategy on the full four-exit family lies above a raw endpoint and has at most one zero-excess row.",
        H("Full Four-Exit Raw Endpoint Domination"),
        Blocks(
            Paragraph(Text("For k at least one, I(k) is Unit plus Fin(k) times Fin(4). The Unit row is the baseline. "
                + "Rows zero through three in an exceptional slot are A, Y, H, Z. F(k,i) is the literal family "
                + "from FourExitRawEndpointSpectrum, with n(k)=8k+16. Its tree substitution, complete leaf list, "
                + "four-valued readout and Strategy are those of ActualTreeReadoutAcquisition. Cost counts distinct "
                + "addresses actually requested from empty initial history by the same globally correct strategy.")),
            Paragraph(Text("M(k) is the existing endpoint menu. It contains the vector with zero at the baseline "
                + "or any Y, H, Z row and one elsewhere; for each A row it contains three vectors with zero there, "
                + "two at a sibling Y, H, Z row and one elsewhere. NC means that any shared literal leaf address "
                + "has the same label in both trees.")),
            Describe.Lean(DescribeId.Create("four-exit-raw-domination"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FourExitRawDomination.result"),
                H("Full Family Structure and Strategy Lower Bound"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The substitution respects every ordered pair in the right comb. The displayed "
                        + "preimages therefore prove positivity. Each ordinary block has eight leaves; an exceptional "
                        + "block and its compensation have twenty-four. Equality of two combs implies equality at "
                        + "each slot, so the exceptional location and block recover the row index. Pairwise label "
                        + "compatibility of the finite block tables extends along the comb to the entire family.")),
                    Paragraph(Text("The compulsory-leaf certificate gives every strategy cost at least n(k). "
                        + "If two rows both cost n(k), their paid address sets equal their complete leaf sets. "
                        + "Induction on the two actual executions shows that the same selector sees identical "
                        + "histories: at each shared query both replies are leaf labels, and NC equates them. "
                        + "The runs and complete labelled leaf sets coincide. Leaf rigidity then equates the trees "
                        + "and hence their indices.")),
                    Paragraph(Text("With no zero-excess row all coordinates exceed the baseline and dominate a "
                        + "baseline endpoint. A zero at the baseline or a Y, H, Z row selects its one-zero endpoint. "
                        + "A zero at A invokes the local zero-to-two obstruction to select a sibling of excess at "
                        + "least two. Uniqueness of the zero gives excess at least one at every remaining row. "
                        + "These cases prove domination for every original Strategy, including adaptive and repeated queries."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs) =>
        Seq(V(name), Par(F.Join(SepBy(Comma, Sp), xs)));
    private static Formula And(params Formula[] xs) => F.Join(Spaced(Wedge), xs.Select(Par).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula ResultFormula()
    {
        Formula k=V("k"), i=V("i"), j=V("j"), p=V("pi"), v=V("v");
        Formula indices=Call("I",k), n=Call("n",k);
        Formula Tree(Formula x) => Call("F",k,x);
        Formula Cost(Formula x) => Call("cost",p,Tree(x));
        Formula structure=All("i",indices,And(Call("Positive",Tree(i)),
            EqOf(Call("length",Tree(i)),n),EqOf(Call("leafLength",Tree(i)),n)));
        Formula nc=All("i",indices,All("j",indices,Call("NC",Tree(i),Tree(j))));
        Formula unique=All("i",indices,All("j",indices,
            Implies(And(EqOf(Cost(i),n),EqOf(Cost(j),n)),EqOf(i,j))));
        Formula domination=Some("v",Call("NatVector",indices),And(
            MemberOf(v,Call("M",k)),All("i",indices,LeOf(Add(n,Call("at",v,i)),Cost(i)))));
        Formula strategies=All("pi",V("Strategy"),And(All("i",indices,LeOf(n,Cost(i))),unique,domination));
        return Disp(All("k",V("Nat"),Implies(LeOf(D(1),k),And(structure,
            Call("Injective",Call("F",k)),nc,strategies))));
    }
}
