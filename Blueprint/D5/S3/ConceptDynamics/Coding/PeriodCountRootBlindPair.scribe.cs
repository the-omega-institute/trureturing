using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class PeriodCountRootBlindPairDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/PeriodCountRootBlindPair.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,[..v],f);
    private static DocumentBlock Item(string selector,string title,Formula f,string text,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("period-count-"+selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+selector),H(title),StatementSource.FromAuthor(Disp(f)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);
    private static Formula Imp(Formula a,Formula b) => Seq(Open,Open,a,Close,Sp,Implies,Sp,Open,b,Close,Close);
    private static Formula LoopHist(Formula g) => Call("History",Call("expandedGraph",Call("loop",g)));
    private static Formula Pure(Formula g) => Q(Equal(Call("minimalPeriod",
        Call("shift",Call("expandedGraph",Call("loop",g))),I("x")),D(2)),B("x",LoopHist(g)));
    private static Formula Count(Formula g) => Call("NatCard",Call("TwistedPeriod",Call("loop",g),D(1),I("j")));
    private static Formula SameCounts => Q(Imp(Call("Positive",I("j")),Equal(Count(I("g")),Count(I("h")))),B("j",I("Nat")));
    private static Formula Claim => Q(Imp(Pure(I("g")),Imp(Pure(I("h")),Imp(SameCounts,
        Seq(Open,Call("HasEquivariantRoot",I("g"),D(2)),Sp,Iff,Sp,Call("HasEquivariantRoot",I("h"),D(2)),Close)))),
        B("g",I("DeckGroup")),B("h",I("DeckGroup")));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary periodic counts do not determine equivariant square roots even with a fixed deck group.",
        H("A same-group pair of actual history systems"),Blocks(
        Item("loop","One original numbered loop",Q(Seq(OpenBracket,Call("Group",I("H")),CloseBracket,
            Q(Equal(Call("loop",I("g")),Call("oneByOneMatrix",Call("single",I("g"),D(1)))),B("g",I("H")))),B("H",I("Type"))),
            "loop(g) is the one-by-one natural group-ring matrix whose only entry is single(g,1). It has one vertex and one numbered edge labelled g. expandedGraph and History are the existing repository structures; no new symbolic dynamics carrier is substituted.",DescribeRole.Definition),
        Item("HasEquivariantRoot","Roots on all actual bilateral histories",Q(Seq(
            OpenBracket,Call("Group",I("H")),CloseBracket,
            Q(Equal(Call("HasEquivariantRoot",I("g"),I("k")),Call("existsDeckEquivariantTimeRoot",Call("loop",I("g")),I("k"))),
                B("g",I("H")),B("k",I("Nat")))),B("H",I("Type"))),
            "existsDeckEquivariantTimeRoot(C,k) means there exists f:History(expandedGraph C)->History(expandedGraph C) such that f(groupHistory(C,a,x))=groupHistory(C,a,f(x)) for every a and x, and f iterated k times equals the original shift. Every base path of loop(g) is the same constant numbered edge. The equivalence from its LiftOrbit at d=1 to all actual histories transports actualAtlas. The exact root criterion therefore reduces to existence of b in H with b^k=g, for this entire system.",DescribeRole.Definition),
        Item("DeckGroup","The same deck group in both systems",Equal(I("DeckGroup"),
            Call("Multiplicative",Call("Prod",Call("ZMod",D(4)),Call("ZMod",D(2))))),
            "DeckGroup is C4 times C2, written multiplicatively. The labels are g=(2,0) and h=(0,1) in additive coordinates. Both have order two. The first is the square of (1,0); the second cannot be a square because the second coordinate of every square is zero.",DescribeRole.Definition),
        Item("claim","The proposed sufficiency of ordinary period data",Equal(I("claim"),
            Claim),
            "The claim universally quantifies g,h in this fixed DeckGroup. It assumes that every actual history in both systems has minimal period two, and asserts that equality of Nat.card(TwistedPeriod(loop(g),1,j)) and Nat.card(TwistedPeriod(loop(h),1,j)) for every positive natural j implies equivalence of HasEquivariantRoot(g,2) and HasEquivariantRoot(h,2). TwistedPeriod with twist 1 is exactly the actual fixed-history subtype for the jth iterate of shift.",DescribeRole.Definition),
        Item("result","Equal periods and different actual square roots",Seq(Neg,Sp,I("claim")),
            "The proof supplies the two labels above and uses the complete actual atlas to prove that every history in each system has minimal period two. The existing twistedPeriod_card theorem counts actual histories, and the one-by-one matrix power has only single(g^j,1). Consequently both systems have eight fixed histories when j is even and zero when j is odd. The exact actual root criterion at d=1 gives a square root in the first system and excludes one in the second. The distinction concerns H-equivariant roots. It makes no claim that the second underlying ordinary permutation lacks a square root, and no claim about maps allowed to move between different base orbits.",DescribeRole.Theorem))));
}
