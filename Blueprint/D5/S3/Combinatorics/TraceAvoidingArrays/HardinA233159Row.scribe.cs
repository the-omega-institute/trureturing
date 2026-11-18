using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233159RowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233159Row.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233159");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool count = false, bool theorem = false) =>
        declaration == "result"
            ? Describe.Lean(DescribeId.Create("a233159-hardina233159row-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233159"), ResolutionKind.Proved))
            : Describe.Lean(DescribeId.Create("a233159-hardina233159row-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality patterns and their quotient determine labelled six-row strip counts.",
        H("OEIS A233159"), Blocks(
            Node("finite_certificate",CertificateFormula(),"The three identities specify the quotient, the initial class counts and the finite relation among matrix powers.",theorem:true),
            Node("result",ResultFormula(),"Multiplication by every further matrix power extends the finite relation to all strip lengths in the displayed range.",theorem:true)), []));
    private static Formula MV(Formula n) => C("Matrix.mulVec",Pow(C("quotient"),n),Cast(N(1),Arr(FinF(N(122)),IntF())));
    private static Formula CertificateFormula() {
        var row=All("r",RowF(N(6)),All("s",FinF(N(122)),Eq(Sum("c",RowF(N(6)),Ite(And(C("columnCompatible",V("r"),V("c")),Eq(C("classify",V("c")),V("s"))),Cast(N(1),IntF()),N(0))),A(C("quotient"),C("classify",V("r")),V("s")))));
        var weights=All("s",FinF(N(122)),Eq(Sum("c",RowF(N(6)),Ite(Eq(C("classify",V("c")),V("s")),Cast(N(1),IntF()),N(0))),A(C("weights"),V("s"))));
        var relation=Eq(MV(PlusF(N(6),N(9))),Sum("j",FinF(N(9)),C("HSMul.hSMul",A(Vec(N(-4128), N(17216), N(-27636), N(21056), N(-6705), N(-573), N(1038), N(-283), N(30)),V("j")),MV(PlusF(N(6),Val(V("j")))))));
        return And(row,And(weights,relation));
    }
    private static Formula ResultFormula() {
        Formula U(int j) => Cast(C("U6",PlusF(V("n"),N(j))),IntF());
        return All("n",NatF(),Eq(U(16),Sub(PlusF(Sub(PlusF(Sub(Sub(PlusF(Sub(Mul(N(30),U(15)),Mul(N(283),U(14))),Mul(N(1038),U(13))),Mul(N(573),U(12))),Mul(N(6705),U(11))),Mul(N(21056),U(10))),Mul(N(27636),U(9))),Mul(N(17216),U(8))),Mul(N(4128),U(7)))));
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
    private static Formula PlusF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(P(a), b);
    private static Formula N(int n) => n < 0 ? Seq(Minus, N(-n)) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula FinF(Formula n) => C("Fin", n);
    private static Formula NatF() => Op("Nat");
    private static Formula IntF() => Op("Int");
    private static Formula Cast(Formula x, Formula t) => P(Seq(x, Colon, Sp, t));
    private static Formula Val(Formula x) => C("Fin.val", x);
    private static Formula RowF(Formula k) => C("Row", k);
    private static Formula Sum(string v, Formula ty, Formula f) => Seq(new Formula.Subscript(F.Sum, P(Seq(V(v), Colon, Sp, ty))), Sp, f);
    private static Formula Ite(Formula p, Formula a, Formula b) => Seq(Op("if"), Sp, p, Sp, Op("then"), Sp, a, Sp, Op("else"), Sp, b);
    private static Formula Vec(params Formula[] xs) => Seq(Bang, OpenBracket, Join(xs), CloseBracket);
    private static Formula Join(Formula[] xs) => Seq(xs.SelectMany((x,i) => i == 0 ? new[]{x} : new[]{Comma,Sp,x}).ToArray());
}
