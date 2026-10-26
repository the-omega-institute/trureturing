using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class CharacteristicThreeOppositeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var formula = Let("M", Seq(D(3), Caret, Grp(Call("finrank", Fthree, F.Id("V"))), Minus, D(3)), Word("V"));
        formula = All("x", F.Id("V"), Seq(F.Id("x"), Neq, Sp, D(0), Rightarrow, Sp, formula));
        formula = Seq(D(2), Le, Sp, Call("finrank", Fthree, F.Id("V")), Rightarrow, Sp, formula);
        formula = All("V", Op("Type"), Seq(Instance("AddCommGroup", F.Id("V")),
            Instance("Module", Fthree, F.Id("V")), Instance("Finite", F.Id("V")), formula));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every finite F3-space with a prescribed opposite hole", H("Every finite F3-space with a prescribed opposite hole"), Blocks(
                Describe.Lean(DescribeId.Create("exact-ordering"),
                    DeclarationHandle.Create("D5/S1/Words/Sequenceability/CharacteristicThreeOpposite.exists_opposite_ordering"),
                    H("Every finite F3-space with a prescribed opposite hole"), StatementSource.FromAuthor(Disp(formula)),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every finite vector space V over ZMod 3 of dimension at least two and every nonzero x in V, put M=3^finrank(V)-3. There is a natural-indexed word whose first M terms enumerate V minus {0,x,-x} exactly once. The first M coefficient-one prefixes, numbered 0 through M-1, are pairwise distinct; the full M-term prefix equals zero. Every proper nonempty interval [a,b) with 0<=a<b<=M and (a,b)!=(0,M) has nonzero sum. The only exempt interval is the whole word. Take r=finrank(V)-1 and the actual field K=GaloisField 3 r. Its cardinality is 3^r and its F3-dimension is r. Equal finite dimension gives an equivalence from K times F3 to V. The image of (0,1) is nonzero. The isomorphism between its one-dimensional span and the span of x extends to an automorphism of V, so composing gives an F3-linear equivalence sending (0,1) exactly to x. Its underlying additive equivalence transports the field ordering. Finally 3*(3^r-1)=3^finrank(V)-3. This includes dimension two with r=1 through the same proof, with no exceptional assumption."))), DescribeRole.Theorem))));
    }

    private static Formula Op(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] xs) =>
        Seq(Op(s), Open, Seq(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x }).ToArray()), Close);
    private static Formula All(string x, Formula ty, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, ty, Close, Comma, body);
    private static Formula Ex(string x, Formula ty, Formula body) =>
        Seq(Exists, Sp, Open, F.Id(x), Colon, ty, Close, Comma, body);
    private static Formula Lam(string x, Formula ty, Formula body) =>
        Seq(Open, F.Id(x), Colon, ty, Mapsto, Sp, body, Close);
    private static Formula Instance(string s, params Formula[] args) =>
        Seq(OpenBracket, Call(s, args), CloseBracket);
    private static Formula Let(string x, Formula v, Formula body) =>
        Seq(Op("let"), Sp, F.Id(x), Eq, v, Semi, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fthree => Call("ZMod", D(3));
    private static Formula Word(string carrier)
    {
        var injective = Call("Injective", Lam("i", Call("Fin", F.Id("M")), Call("w", F.Id("i"))));
        var inventory = Seq(Call("range", Lam("i", Call("Fin", F.Id("M")), Call("w", F.Id("i")))), Eq,
            OpenBrace, F.Id("y"), Colon, F.Id(carrier), Bar,
            F.Id("y"), Neq, Sp, D(0), Land, Sp, F.Id("y"), Neq, Sp, F.Id("x"), Land, Sp,
            F.Id("y"), Neq, Sp, Minus, F.Id("x"), CloseBrace);
        var prefix = Call("Injective", Lam("k", Call("Fin", F.Id("M")), Prefix(F.Id("k"))));
        var interval = Seq(Open, F.Id("a"), Lt, F.Id("b"), Land, Sp, F.Id("b"), Le, Sp, F.Id("M"), Land, Sp,
            Open, F.Id("a"), Neq, Sp, D(0), Lor, Sp, F.Id("b"), Neq, Sp, F.Id("M"), Close, Close,
            Rightarrow, Sp, Sum, Underscore, Grp(F.Id("a"), Le, Sp, F.Id("i"), Lt, F.Id("b")),
            Call("w", F.Id("i")), Neq, Sp, D(0));
        interval = All("a", Nat, All("b", Nat, interval));
        return Ex("w", Seq(Nat, To, Sp, F.Id(carrier)), Seq(injective, Land, Sp,
            inventory, Land, Sp, prefix, Land, Sp, Prefix(F.Id("M")), Eq, D(0), Land, Sp, interval));
    }
    private static Formula Prefix(Formula k) => Seq(Sum, Underscore, Grp(F.Id("i"), Lt, k), Call("w", F.Id("i")));

}
