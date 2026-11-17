using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233154ColumnDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233154");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool count = false, bool theorem = false) =>
        declaration == "result"
            ? Describe.Lean(DescribeId.Create("hardina233154column-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233154"), ResolutionKind.Proved))
            : Describe.Lean(DescribeId.Create("hardina233154column-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal 7-column count obeys a recurrence determined by its finite row quotient.",
        H("OEIS A233154"), Blocks(
            Node("finite_certificate",CertificateFormula(),"The three finite identities give the successor counts, initial class multiplicities and a polynomial relation among quotient powers.",theorem:true),
            Node("result",ResultFormula(),"The finite relation extends through all further matrix powers. The initial instance supplies the exact starting index.",theorem:true)), []));
    private static Formula MV(Formula n) => C("Matrix.mulVec",Pow(C("quotient"),n),Cast(N(1),Arr(FinF(N(16)),IntF())));
    private static Formula CertificateFormula() {
        var row=All("r",RowF(N(7)),Imp(C("rowLegal",V("r")),All("s",FinF(N(16)),Eq(Sum("c",RowF(N(7)),Ite(And(C("rowLegal",V("c")),And(C("compatible",V("r"),V("c")),Eq(C("classify",V("c")),V("s")))),Cast(N(1),IntF()),N(0))),A(C("quotient"),C("classify",V("r")),V("s"))))));
        var weights=All("s",FinF(N(16)),Eq(Sum("c",RowF(N(7)),Ite(And(C("rowLegal",V("c")),Eq(C("classify",V("c")),V("s"))),Cast(N(1),IntF()),N(0))),A(C("weights"),V("s"))));
        var relation=Eq(MV(PlusF(N(1),N(4))),Sum("j",FinF(N(4)),C("HSMul.hSMul",A(Vec(N(-810), N(972), N(-351), N(42)),V("j")),MV(PlusF(N(1),Val(V("j")))))));
        return And(row,And(weights,relation));
    }
    private static Formula ResultFormula() {
        Formula T(int j) => Cast(C("T7",PlusF(V("n"),N(j))),IntF());
        return All("n",NatF(),Eq(T(5),Sub(PlusF(Sub(Mul(N(42),T(4)),Mul(N(351),T(3))),Mul(N(972),T(2))),Mul(N(810),T(1)))));
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
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
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
