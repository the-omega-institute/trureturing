using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233159RowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Rows.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233159");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool count = false, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("a233159-hardina233159rows-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality patterns and their quotient determine labelled six-row strip counts.",
        H("OEIS A233159"), Blocks(
            Node("U6",All("n",NatF(),Eq(C("U6",V("n")),FilterCard(N(6),V("n")))),"Every labelled function satisfying horizontal and antidiagonal sum exclusion is counted.",true),
            Node("classes", All("a",FinF(N(3)),All("b",FinF(N(3)),All("c",FinF(N(3)),All("d",FinF(N(3)),All("e",FinF(N(3)),All("f",FinF(N(3)),Eq(C("classes",V("a"), V("b"), V("c"), V("d"), V("e"), V("f")),C("HardinA233179PairTransfer.orbit",P(Seq(V("a"), Comma, Sp, P(Seq(V("b"), Comma, Sp, P(Seq(V("c"), Comma, Sp, P(Seq(V("d"), Comma, Sp, P(Seq(V("e"), Comma, Sp, V("f"))))))))))))))))))), "The existing first-appearance orbit index assigns the equality pattern."),
            Node("classify",All("r",RowF(N(6)),Eq(C("classify",V("r")),A(C("classes"),A(V("r"),N(0)), A(V("r"),N(1)), A(V("r"),N(2)), A(V("r"),N(3)), A(V("r"),N(4)), A(V("r"),N(5))))),"The coordinates select one of the 122 equality classes."),
            Node("representatives", All("i",FinF(N(122)),Eq(C("representatives",V("i")),C("HardinA233179PairTransfer.column",C("HardinA233179PairTransfer.representatives",V("i"))))), "The existing representative tuple is read in row order."),
            Node("quotient",All("i",FinF(N(122)),All("s",FinF(N(122)),Eq(C("quotient",V("i"),V("s")),C("List.sum",C("List.map",Lam("j",FinF(N(122)),Ite(Eq(V("j"),V("s")),Cast(N(1),IntF()),N(0))),C("successors",V("i"))))))),"The quotient entry is the multiplicity of a class in the successor list."),
            Node("weights", Cast(C("weights"), Arr(FinF(N(122)), IntF())), "The fixed 122-entry integer vector records three labelled constant columns in the constant class and six labelled columns in every other equality class."),
            Node("successors", Cast(C("successors"), Arr(FinF(N(122)), C("List", FinF(N(122))))), "The fixed table assigns each of the 122 representatives its list of compatible successor classes in base-three code order, retaining multiplicities."),
            Node("equality_classes",EqualityFormula(),"Color permutations preserve the equality class and carry each column to its representative.",theorem:true)), []));
    private static Formula EqualityFormula() {
        var perm=C("Equiv.Perm",FinF(N(3)));
        var invariant=All("e",perm,All("r",RowF(N(6)),Eq(C("classify",C("relabel",V("e"),V("r"))),C("classify",V("r")))));
        var representative=All("r",RowF(N(6)),new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("e"),perm,Eq(C("relabel",V("e"),V("r")),C("representatives",C("classify",V("r"))))));
        return And(invariant,representative);
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
    private static Formula Lam(string name, Formula type, Formula body) => P(Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, P(body)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula N(int n) => n < 0 ? Seq(Minus, N(-n)) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula FinF(Formula n) => C("Fin", n);
    private static Formula NatF() => Op("Nat");
    private static Formula IntF() => Op("Int");
    private static Formula Cast(Formula x, Formula t) => P(Seq(x, Colon, Sp, t));
    private static Formula RowF(Formula k) => C("Row", k);
    private static Formula Grid(Formula k, Formula n) => Arr(P(Seq(FinF(k), Sp, Times, Sp, FinF(n))), FinF(N(3)));
    private static Formula Ite(Formula p, Formula a, Formula b) => Seq(Op("if"), Sp, p, Sp, Op("then"), Sp, a, Sp, Op("else"), Sp, b);
    private static Formula FilterCard(Formula k, Formula n) => C("Finset.card", C("Finset.filter", Lam("f", Grid(k,n), C("Legal",V("f"))), Op("Finset.univ")));
}
