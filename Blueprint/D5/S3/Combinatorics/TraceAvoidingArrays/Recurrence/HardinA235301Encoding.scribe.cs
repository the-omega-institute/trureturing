using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence;

internal sealed class HardinA235301EncodingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235301Encoding";
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Six = Call("Fin", D(6));

    public DocumentDefinition Create()
    {
        var n = F.Id("n");
        var h = F.Id("h");
        var w = F.Id("w");
        var pair = F.Id("u");
        var codes = Seq(OpenBrace, pair, Colon, Sp, Call("Word", h), Sp, Times, Sp,
            Call("Word", w), Sp, Mid, Sp, Call("CodeOK", Project(pair, 1), Project(pair, 2)), CloseBrace);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Boundary-word encoding of stress-three rectangles.",
            H("Boundary-word encoding"),
            Blocks(
                Entry("word", "Word", "Six-letter words", All("n", Nat,
                    Eqn(Call("Word", n), Seq(Call("Fin", Seq(n, Plus, D(1))), Sp, To, Sp, Six))),
                    "The length includes the initial letter.", DescribeRole.Definition),
                Entry("cross", "Cross", "Legal crossing", Crossing(),
                    "The four residues reconstruct one block. The parity complements use natural subtraction, "
                    + "and the diagonal difference is taken over the integers.", DescribeRole.Definition),
                Entry("code-ok", "CodeOK", "Normalized boundary words", Code(),
                    "The column word starts at zero. Every consecutive row and column edge must cross legally.",
                    DescribeRole.Definition),
                Entry("next-parity", "next_parity", "Parity at the next index",
                    All("n", Nat, Eqn(ModTwo(Seq(Open, n, Plus, D(1), Close)),
                        Seq(D(1), Minus, ModTwo(n)))),
                    "Both sides are natural numbers.", DescribeRole.Lemma),
                Entry("count-codes", "count_codes", "Counting by boundary words",
                    All("h", Nat, All("w", Nat, Seq(D(0), Lt, h, Sp, Implies, Sp,
                        D(0), Lt, w, Sp, Implies, Sp,
                        Eqn(Call("C", D(3), D(3), h, w), Call("card", codes))))),
                    "Here card is Nat.card. Currying identifies the indexed rectangle with a function of "
                    + "two coordinates. Subtracting three times the index product modulo six gives "
                    + "vanishing mixed differences, so the two normalized boundary words determine the grid.",
                    DescribeRole.Theorem),
                Entry("count-symm", "count_symm", "Transposition",
                    All("h", Nat, All("w", Nat,
                        Eqn(Call("C", D(3), D(3), h, w), Call("C", D(3), D(3), w, h)))),
                    "Swapping the row and column preserves the diagonal difference and is its own inverse.",
                    DescribeRole.Theorem))));
    }

    private static Formula Crossing()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("c");
        var d = F.Id("d");
        var x = F.Id("x");
        var y = F.Id("y");
        var z = F.Id("z");
        var t = F.Id("t");
        var definition = Seq(
            Let(x, Residue(p, q, a, c)), Let(y, Residue(p, Complement(q), a, d)),
            Let(z, Residue(Complement(p), q, b, c)), Let(t, Residue(Complement(p), Complement(q), b, d)),
            Seq(x, Lt, D(4), Sp, Land, Sp, y, Lt, D(4), Sp, Land, Sp,
                z, Lt, D(4), Sp, Land, Sp, t, Lt, D(4), Sp, Land, Sp,
                Eqn(Seq(Lvert, Sp, x, Plus, t, Minus, Open, y, Plus, z, Close, Sp, Rvert), D(3))));
        var equivalence = Seq(Call("Cross", p, q, a, b, c, d), Sp, Iff, Sp, Open, definition, Close);
        return All("p", Nat, All("q", Nat, All("a", Six, All("b", Six, All("c", Six, All("d", Six,
            equivalence))))));
    }

    private static Formula Code()
    {
        var h = F.Id("h");
        var w = F.Id("w");
        var r = F.Id("r");
        var c = F.Id("c");
        var i = F.Id("i");
        var j = F.Id("j");
        Formula At(Formula word, string embedding, Formula index) =>
            new Formula.Apply(word, [Call(embedding, index)]);
        var crossing = Call("Cross", ModTwo(Call("val", i)), ModTwo(Call("val", j)),
            At(r, "castSucc", i), At(r, "succ", i), At(c, "castSucc", j), At(c, "succ", j));
        return All("h", Nat, All("w", Nat, All("r", Call("Word", h), All("c", Call("Word", w),
            Seq(Call("CodeOK", r, c), Sp, Iff, Sp, Open,
                Eqn(new Formula.Apply(c, [D(0)]), D(0)), Sp, Land, Sp,
                All("i", Call("Fin", h), All("j", Call("Fin", w), crossing)), Close)))));
    }

    private static Formula Residue(Formula p, Formula q, Formula a, Formula b) =>
        Call("mod", Seq(Call("val", a), Plus, Call("val", b), Plus, D(3), Cdot, Sp, p, Cdot, Sp, q), D(6));
    private static Formula Complement(Formula p) => Seq(Open, D(1), Minus, p, Close);
    private static Formula ModTwo(Formula n) => Call("mod", n, D(2));
    private static Formula Project(Formula pair, byte index) => Seq(pair, Dot, D(index));
    private static Formula Let(Formula name, Formula term) =>
        Seq(Mathrm, Grp(F.Id("let")), Sp, name, Sp, Colon, F.Eq, Sp, term, Semi, Sp);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, F.Eq, Sp, right);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static DocumentBlock Entry(string id, string name, string title, Formula statement, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + "." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
