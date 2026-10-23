using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class CharacteristicThreeOrderingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var formula = Let("M", Seq(D(3), Cdot, Open, Call("card", F.Id("K")), Minus, D(1), Close), Word("A"));
        formula = All("x", F.Id("A"), Seq(Call("f", Pair(D(0), D(1))), Eq, F.Id("x"), Rightarrow, Sp, formula));
        formula = All("f", Call("AddEquiv", Seq(F.Id("K"), Times, Sp, Fthree), F.Id("A")), formula);
        formula = All("A", Op("Type"), Seq(Instance("AddCommGroup", F.Id("A")), formula));
        formula = All("K", Op("Type"), Seq(Instance("Field", F.Id("K")),
            Instance("Fintype", F.Id("K")), Instance("CharP", F.Id("K"), D(3)), formula));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Transport of the exact coefficient-one word", H("Transport of the exact coefficient-one word"), Blocks(
                Describe.Lean(DescribeId.Create("exact-ordering"),
                    DeclarationHandle.Create("D5/S1/Words/Sequenceability/CharacteristicThreeOrdering.exists_transported_ordering"),
                    H("Transport of the exact coefficient-one word"), StatementSource.FromAuthor(Disp(formula)),
                    AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Let K be any finite characteristic-three field, A any additive commutative group, and f an additive equivalence from K times ZMod 3 to A taking (0,1) to x. Put M=3*(card(K)-1). There is a natural-indexed word w whose restriction to Fin M is injective and has range exactly the elements different from 0, x and -x. Its coefficient-one prefixes indexed by Fin M, including the empty prefix and excluding the full prefix, are injective. The full M-term sum is zero. Every nonempty interval [a,b) with 0<=a<b<=M has nonzero sum unless a=0 and b=M. No constraint is placed on values of w beyond the first M terms. The word is the actual successive difference of the field orbit after applying f. Telescoping identifies its n-term prefix with the nth vertex minus the initial vertex. The orbit return proves the full sum is zero, and the orbit bijection separates the first M prefixes. For a terminal interval with b=M and a>0, the terminal vertex is the initial vertex; it cannot equal the proper interior vertex. The label bijection supplies the exact missing-line inventory. A zero first coordinate has row 0, 1 or -1, so f sends that line to exactly 0, x and -x."))), DescribeRole.Theorem))));
    }

    private static Formula Op(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] xs) =>
        Seq(Op(s), Open, Seq(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x }).ToArray()), Close);
    private static Formula All(string x, Formula ty, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, ty, Close, Comma, body);
    private static Formula Ex(string x, Formula ty, Formula body) =>
        Seq(Exists, Sp, Open, F.Id(x), Colon, ty, Close, Comma, body);
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, y, Close);
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
