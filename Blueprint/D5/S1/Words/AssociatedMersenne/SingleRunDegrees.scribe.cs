using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AssociatedMersenne;

internal sealed class SingleRunDegreesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AssociatedMersenne/SingleRunDegrees.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/wei2024associatedmersenne");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Degree enumeration for labelled circular run-constrained words.", H("SingleRunDegrees"), Blocks(
        Node("run_interior_delete_illegal", "run interior delete illegal", Disp(All(Name("n"), Name("Nat"), All(Name("w"), Seq(Name("Fin"), Sp, Name("n"), Sp, To, Sp, Name("Bool")), All(Name("a"), Seq(Name("Fin"), Sp, Name("n")), All(Name("r"), Name("Nat"), All(Name("p"), Name("Nat"), Seq(Parenthesized(Seq(Name("IsOneRunStart"), Sp, Name("w"), Sp, Name("a"), Sp, Name("r"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, Name("p"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Name("p"), Sp, Plus, Sp, D(1), Sp, Lt, Sp, Name("r"))), Sp, To, Sp, Parenthesized(Seq(Neg, Sp, Name("Admissible"), Sp, Parenthesized(Seq(Name("CircularWords.flip"), Sp, Name("w"), Sp, Parenthesized(Seq(Name("cycAdd"), Sp, Name("a"), Sp, Name("p")))))))))))))))))), "Deleting an interior one splits its run around a zero gap too short for the preceding run.", DescribeRole.Theorem),
        Node("singleRun", "singleRun", Disp(All(Name("n"), Name("Nat"), All(Name("r"), Name("Nat"), Seq(Name("singleRun"), Sp, Name("n"), Sp, Name("r"), Sp, Eq, Sp, Parenthesized(Seq(Name("fun"), Sp, Name("j"), Sp, Mapsto, Sp, Name("decide"), Sp, Parenthesized(Seq(Name("j.val"), Sp, Lt, Sp, Name("r"))))))))), "The first r labelled positions are ones and the remaining positions are zeros.", DescribeRole.Definition),
        Node("singleRun_degree", "singleRun degree", Disp(All(Name("r"), Name("Nat"), All(Name("s"), Name("Nat"), Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, Name("r"))), Sp, To, Sp, Parenthesized(Seq(Name("degree"), Sp, Parenthesized(Seq(Name("singleRun"), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, Name("r"), Sp, Plus, Sp, D(1), Sp, Plus, Sp, Name("s"))), Sp, Name("r"))), Sp, Eq, Sp, Name("min"), Sp, Name("r"), Sp, D(2), Sp, Plus, Sp, Name("if"), Sp, D(2), Sp, Le, Sp, Name("s"), Sp, Name("then"), Sp, Name("s"), Sp, Name("else"), Sp, D(0))))))), "Endpoint deletions and the admissible insertions in the shared circular gap give the exact single-run degree.", DescribeRole.Theorem),
        Node("degree_raw_singleton", "degree raw singleton", Disp(All(Name("n"), Name("Nat"), All(Name("w"), Seq(Name("Fin"), Sp, Name("n"), Sp, To, Sp, Name("Bool")), All(Name("i"), Seq(Name("Fin"), Sp, Name("n")), All(Name("r"), Name("Nat"), All(Name("z"), Name("Nat"), Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, Name("r"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Name("r"), Sp, Lt, Sp, Name("z"))), Sp, To, Sp, Parenthesized(Seq(Parenthesized(Seq(Name("linearize"), Sp, Name("w"), Sp, Name("i"), Sp, Eq, Sp, Name("rawWord"), Sp, Seq(OpenBracket, Sp, Parenthesized(Seq(Name("r"), Sp, Comma, Sp, Name("z"))), Sp, CloseBracket))), Sp, To, Sp, Parenthesized(Seq(Name("degree"), Sp, Name("w"), Sp, Eq, Sp, Name("min"), Sp, Name("r"), Sp, D(2), Sp, Plus, Sp, Name("if"), Sp, D(2), Sp, Le, Sp, Name("z"), Sp, Minus, Sp, Name("r"), Sp, Minus, Sp, D(1), Sp, Name("then"), Sp, Name("z"), Sp, Minus, Sp, Name("r"), Sp, Minus, Sp, D(1), Sp, Name("else"), Sp, D(0)))))))))))))), "Rotating to the mark identifies a singleton raw-pair encoding with the single-run degree calculation.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, bool literature = false) => Describe.Lean(
        DescribeId.Create("amg-singlerundegrees-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
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
