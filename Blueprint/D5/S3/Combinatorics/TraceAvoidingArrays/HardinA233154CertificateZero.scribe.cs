using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233154CertificateZeroDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154CertificateZero.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233154");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool count = false, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("hardina233154certificatezero-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successor counts in one block of seven-column row codes.", H("Quotient row block 0"),
        Blocks(Node("row_counts",Statement(),"Every legal source code in the block has the stated number of successors in each quotient class.",theorem:true)), []));
    private static Formula Statement() {
        var code=Seq(Langle, Sp,PlusF(Mul(N(3),Val(V("a"))),N(0)),Comma,Sp,Seq(Op("by"),Sp,Op("omega")),Rangle);
        var row=C("decode",N(7),P(Seq(code,Colon,Sp,FinF(N(2187)))));
        return All("a",FinF(N(729)),Imp(C("rowLegal",row),All("s",FinF(N(16)),
            Eq(C("classCount",row,V("s")),A(C("quotient"),C("classify",row),V("s"))))));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Name(name)));
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part,i) =>
        i == 0 ? new[]{Atom(part)} : new[]{Dot,Atom(part)}).ToArray());
    private static Formula Atom(string part) {
        var words=part.Split('_');
        return words.Length == 1 ? V(part) : new Formula.Subscript(V(words[0]),
            Seq(words.Skip(1).Select(V).ToArray()));
    }

    private static Formula C(string name, params Formula[] args) => args.Length == 0 ? Name(name) : new Formula.Apply(Name(name), [.. args]);
    private static Formula A(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula P(Formula f) => Parenthesized(f);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula PlusF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula N(int n) => n < 0 ? Seq(Minus, N(-n)) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula FinF(Formula n) => C("Fin", n);
    private static Formula Val(Formula x) => C("Fin.val", x);
}
