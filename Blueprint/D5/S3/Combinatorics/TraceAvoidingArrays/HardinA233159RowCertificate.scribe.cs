using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233159RowCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159RowCertificate.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233159");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool count = false, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("a233159-hardina233159rowcertificate-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality patterns and their quotient determine labelled six-row strip counts.",
        H("OEIS A233159"), Blocks(
            Node("quotient_certificate",QuotientFormula(),"Successor counts, initial multiplicities and sparse matrix action agree with the finite column tables.",theorem:true)), []));
    private static Formula QuotientFormula() {
        var row=All("r",RowF(N(6)),All("s",FinF(N(122)),Eq(Sum("c",RowF(N(6)),Ite(And(C("columnCompatible",V("r"),V("c")),Eq(C("classify",V("c")),V("s"))),Cast(N(1),IntF()),N(0))),A(C("quotient"),C("classify",V("r")),V("s")))));
        var weights=All("s",FinF(N(122)),Eq(Sum("c",RowF(N(6)),Ite(Eq(C("classify",V("c")),V("s")),Cast(N(1),IntF()),N(0))),A(C("weights"),V("s"))));
        var action=All("v",Arr(FinF(N(122)),IntF()),All("i",FinF(N(122)),Eq(A(C("Matrix.mulVec",C("quotient"),V("v")),V("i")),C("List.sum",C("List.map",V("v"),C("successors",V("i")))))));
        return And(row,And(weights,action));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Name(name)));
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part,i) =>
        i == 0 ? new[]{Atom(part)} : new[]{Dot,Atom(part)}).ToArray());
    private static Formula Atom(string part) {
        var words=part.Split('_');
        if (part == "U3") return new Formula.Subscript(V("U"),N(3));
        if (part == "U4") return new Formula.Subscript(V("U"),N(4));
        if (part == "U5") return new Formula.Subscript(V("U"),N(5));
        if (part == "U6") return new Formula.Subscript(V("U"),N(6));
        return words.Length == 1 ? V(part) : new Formula.Subscript(V(words[0]),
            Seq(words.Skip(1).Select(V).ToArray()));
    }

    private static Formula C(string name, params Formula[] args) => args.Length == 0 ? Name(name) : new Formula.Apply(Name(name), [.. args]);
    private static Formula A(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula P(Formula f) => Parenthesized(f);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula N(int n) => n < 0 ? Seq(Minus, N(-n)) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula FinF(Formula n) => C("Fin", n);
    private static Formula IntF() => Op("Int");
    private static Formula Cast(Formula x, Formula t) => P(Seq(x, Colon, Sp, t));
    private static Formula RowF(Formula k) => C("Row", k);
    private static Formula Sum(string v, Formula ty, Formula f) => Seq(new Formula.Subscript(F.Sum, P(Seq(V(v), Colon, Sp, ty))), Sp, f);
    private static Formula Ite(Formula p, Formula a, Formula b) => Seq(Op("if"), Sp, p, Sp, Op("then"), Sp, a, Sp, Op("else"), Sp, b);
}
