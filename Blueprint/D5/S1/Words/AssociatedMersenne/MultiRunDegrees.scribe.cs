using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AssociatedMersenne;

internal sealed class MultiRunDegreesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AssociatedMersenne/MultiRunDegrees.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/wei2024associatedmersenne");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Degree enumeration for labelled circular run-constrained words.", H("MultiRunDegrees"), Blocks(
        Node("degree_raw_multi", "degree raw multi", Disp(All(Name("n"), Name("Nat"), All(Name("w"), Seq(Name("Fin"), Sp, Name("n"), Sp, To, Sp, Name("Bool")), All(Name("i"), Seq(Name("Fin"), Sp, Name("n")), All(Name("t"), Seq(Name("List"), Sp, Parenthesized(Seq(Name("Nat"), Sp, Times, Sp, Name("Nat")))), Seq(Parenthesized(Seq(D(2), Sp, Le, Sp, Name("t.length"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Forall, Sp, Name("b"), Sp, InMacro, Sp, Name("t"), Sp, Comma, Sp, D(0), Sp, Lt, Sp, Name("b.1"), Sp, Land, Sp, Name("b.1"), Sp, Lt, Sp, Name("b.2"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Name("linearize"), Sp, Name("w"), Sp, Name("i"), Sp, Eq, Sp, Name("rawWord"), Sp, Name("t"))), Sp, To, Sp, Parenthesized(Seq(Name("degree"), Sp, Name("w"), Sp, Eq, Sp, Sum, Sp, Name("p"), Sp, Colon, Sp, Name("Fin"), Sp, Name("t.length"), Sp, Comma, Sp, Parenthesized(Seq(Name("min"), Sp, Name("t"), Sp, Seq(OpenBracket, Sp, Name("p.val"), Sp, CloseBracket), Sp, Dot, Sp, D(1), Sp, D(2), Sp, Plus, Sp, Parenthesized(Seq(Name("t"), Sp, Seq(OpenBracket, Sp, Name("p.val"), Sp, CloseBracket), Sp, Dot, Sp, D(2), Sp, Minus, Sp, Parenthesized(Seq(Name("t"), Sp, Seq(OpenBracket, Sp, Name("p.val"), Sp, CloseBracket), Sp, Dot, Sp, D(1), Sp, Plus, Sp, D(1))), Sp, Minus, Sp, D(1))), Sp, Plus, Sp, Name("if"), Sp, Name("t"), Sp, Seq(OpenBracket, Sp, Name("p.val"), Sp, CloseBracket), Sp, Dot, Sp, D(1), Sp, Plus, Sp, D(1), Sp, Lt, Sp, Name("t"), Sp, Seq(OpenBracket, Sp, Name("p.val"), Sp, CloseBracket), Sp, Dot, Sp, D(2), Sp, Land, Sp, Parenthesized(Seq(Name("t"), Sp, Seq(OpenBracket, Sp, Seq(Parenthesized(Seq(Name("p.val"), Sp, Plus, Sp, D(1))), Sp, Name("Nat.mod"), Sp, Name("t.length")), Sp, CloseBracket))), Sp, Dot, Sp, D(1), Sp, Plus, Sp, D(1), Sp, Lt, Sp, Parenthesized(Seq(Name("t"), Sp, Seq(OpenBracket, Sp, Seq(Parenthesized(Seq(Name("p.val"), Sp, Plus, Sp, D(1))), Sp, Name("Nat.mod"), Sp, Name("t.length")), Sp, CloseBracket))), Sp, Dot, Sp, D(2), Sp, Name("then"), Sp, D(1), Sp, Name("else"), Sp, D(0))))))))))))))), "Pairwise deletion endpoints, gap extensions and interior singleton insertions partition all legal flips.", DescribeRole.Theorem),
        Node("tupleDegree", "tupleDegree", Disp(All(Name("t"), Seq(Name("List"), Sp, Parenthesized(Seq(Name("Nat"), Sp, Times, Sp, Name("Nat")))), Seq(Name("tupleDegree"), Sp, Name("t"), Sp, Eq, Sp, Parenthesized(Seq(Name("if"), Sp, Name("t.length"), Sp, Eq, Sp, D(1), Sp, Name("then"), Sp, Parenthesized(Seq(Name("t.map"), Sp, Parenthesized(Seq(Name("fun"), Sp, Name("b"), Sp, Mapsto, Sp, Name("min"), Sp, Name("b.1"), Sp, D(2), Sp, Plus, Sp, Name("if"), Sp, D(2), Sp, Le, Sp, Name("b.2"), Sp, Name("then"), Sp, Name("b.2"), Sp, Name("else"), Sp, D(0))))), Sp, Dot, Sp, Name("sum"), Sp, Name("else"), Sp, Sum, Sp, Name("p"), Sp, Colon, Sp, Name("Fin"), Sp, Name("t.length"), Sp, Comma, Sp, Parenthesized(Seq(Name("min"), Sp, Name("t"), Sp, Seq(OpenBracket, Sp, Name("p.val"), Sp, CloseBracket), Sp, Dot, Sp, D(1), Sp, D(2), Sp, Plus, Sp, Parenthesized(Seq(Name("t"), Sp, Seq(OpenBracket, Sp, Name("p.val"), Sp, CloseBracket), Sp, Dot, Sp, D(2), Sp, Minus, Sp, D(1))), Sp, Plus, Sp, Name("if"), Sp, D(1), Sp, Le, Sp, Name("t"), Sp, Seq(OpenBracket, Sp, Name("p.val"), Sp, CloseBracket), Sp, Dot, Sp, D(2), Sp, Land, Sp, D(1), Sp, Le, Sp, Parenthesized(Seq(Name("t"), Sp, Seq(OpenBracket, Sp, Seq(Parenthesized(Seq(Name("p.val"), Sp, Plus, Sp, D(1))), Sp, Name("Nat.mod"), Sp, Name("t.length")), Sp, CloseBracket))), Sp, Dot, Sp, D(2), Sp, Name("then"), Sp, D(1), Sp, Name("else"), Sp, D(0)))))))), "The singleton case includes both circular gap endpoints meeting the same run. Natural subtraction is truncated; it is not integer subtraction.", DescribeRole.Definition),
        Node("degree_wordOfTuple", "degree wordOfTuple", Disp(All(Name("n"), Name("Nat"), All(Name("i"), Seq(Name("Fin"), Sp, Name("n")), All(Name("t"), Seq(Name("GoodTuple"), Sp, Name("n")), Seq(Name("degree"), Sp, Parenthesized(Seq(Name("wordOfTuple"), Sp, Name("i"), Sp, Name("t.val"), Sp, Name("t.property.2.2"))), Sp, Eq, Sp, Name("tupleDegree"), Sp, Name("t.val")))))), "The reconstructed word has its tuple encoding, so the pair-local formula gives its degree.", DescribeRole.Lemma))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, bool literature = false) => Describe.Lean(
        DescribeId.Create("amg-multirundegrees-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Name(string name) {
        var parts = name.Split('.');
        Formula value = Word(parts[0]);
        for (var i = 1; i < parts.Length; i++) value = Seq(value, Dot, Word(parts[i]));
        return value;
    }
    private static Formula Word(string word) {
        if (word == "") return Sp;
        if (word == "0") return D(0);
        if (word == "1") return D(1);
        if (word == "2") return D(2);
        if (word.EndsWith("'", StringComparison.Ordinal)) return Seq(Word(word[..^1]), Apos);
        var parts = word.Split('_');
        Formula value = Seq(Operatorname, Grp(F.Id(parts[0])));
        for (var i = 1; i < parts.Length; i++) value = new Formula.Subscript(value, Seq(Operatorname, Grp(F.Id(parts[i]))));
        return value;
    }
}
