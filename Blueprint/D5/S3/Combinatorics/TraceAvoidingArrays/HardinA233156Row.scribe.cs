using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233156RowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233156Row.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233156");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool count = false, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("a233156-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The number of labelled 3-row arrays obeys the order-2 recurrence from OEIS A233156.",
        H("OEIS A233156"), Blocks(
            Node("U3",All("n",NatF(),Eq(C("U3",V("n")),FilterCard(N(3),V("n")))),"Every labelled function satisfying horizontal and antidiagonal sum exclusion is counted.",true),
            Node("classes",Eq(C("classes"),Cast(Vec(Vec(Vec(N(0),N(1),N(1)),Vec(N(2),N(3),N(4)),Vec(N(2),N(4),N(3))),Vec(Vec(N(3),N(2),N(4)),Vec(N(1),N(0),N(1)),Vec(N(4),N(2),N(3))),Vec(Vec(N(3),N(4),N(2)),Vec(N(4),N(3),N(2)),Vec(N(1),N(1),N(0)))),ClassTableType(3,5))),"The table assigns a class to every column according to its equality pattern."),
            Node("classify",All("r",RowF(N(3)),Eq(C("classify",V("r")),A(C("classes"),A(V("r"),N(0)), A(V("r"),N(1)), A(V("r"),N(2))))),"The coordinates select one of the 5 equality classes."),
            Node("representatives",Eq(C("representatives"),Vec(Vec(N(0), N(0), N(0)), Vec(N(0), N(0), N(1)), Vec(N(0), N(1), N(0)), Vec(N(0), N(1), N(1)), Vec(N(0), N(1), N(2)))),"Each equality pattern has a representative using colors in order of first occurrence."),
            Node("quotient",Eq(C("quotient"),Vec(Vec(N(2), N(2), N(2), N(2), N(0)), Vec(N(1), N(1), N(0), N(1), N(1)), Vec(N(1), N(1), N(0), N(0), N(0)), Vec(N(1), N(1), N(1), N(1), N(0)), Vec(N(0), N(0), N(0), N(1), N(1)))),"An entry counts compatible successor columns in the indicated equality class."),
            Node("weights",Eq(C("weights"),Vec(N(3), N(6), N(6), N(6), N(6))),"The weights count all columns in each class, including constant columns."),
            Node("finite_certificate",CertificateFormula(),"The three identities specify the quotient, the initial class counts and the finite relation among matrix powers.",theorem:true),
            Node("result",ResultFormula(),"Multiplication by every further matrix power extends the finite relation to all strip lengths in the displayed range.",theorem:true)), []));
    private static Formula MV(Formula n) => C("Matrix.mulVec",Pow(C("quotient"),n),Cast(N(1),Arr(FinF(N(5)),IntF())));
    private static Formula CertificateFormula() {
        var row=All("r",RowF(N(3)),All("s",FinF(N(5)),Eq(Sum("c",RowF(N(3)),Ite(And(C("columnCompatible",V("r"),V("c")),Eq(C("classify",V("c")),V("s"))),Cast(N(1),IntF()),N(0))),A(C("quotient"),C("classify",V("r")),V("s")))));
        var weights=All("s",FinF(N(5)),Eq(Sum("c",RowF(N(3)),Ite(Eq(C("classify",V("c")),V("s")),Cast(N(1),IntF()),N(0))),A(C("weights"),V("s"))));
        var relation=Eq(MV(PlusF(N(2),N(2))),Sum("j",FinF(N(2)),C("HSMul.hSMul",A(Vec(N(-2), N(5)),V("j")),MV(PlusF(N(2),Val(V("j")))))));
        return And(row,And(weights,relation));
    }
    private static Formula ResultFormula() {
        Formula U(int j) => Cast(C("U3",PlusF(V("n"),N(j))),IntF());
        return All("n",NatF(),Eq(U(5),Sub(Mul(N(5),U(4)),Mul(N(2),U(3)))));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Name(name)));
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part,i) =>
        i == 0 ? new[]{Atom(part)} : new[]{Dot,Atom(part)}).ToArray());
    private static Formula Atom(string part) {
        var words=part.Split('_');
        if (words.Length == 1 && part.Any(char.IsDigit)) {
            var letters = new string(part.TakeWhile(char.IsLetter).ToArray());
            var digits = new string(part.SkipWhile(char.IsLetter).ToArray());
            return new Formula.Subscript(V(letters), N(int.Parse(digits)));
        }
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
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula PlusF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(P(a), b);
    private static Formula N(int n) => n < 0 ? Seq(Minus, N(-n)) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula FinF(Formula n) => C("Fin", n);
    private static Formula ClassTableType(int width, int q) { Formula t = FinF(N(q)); for (int i = 0; i < width; ++i) t = Arr(FinF(N(3)), t); return t; }
    private static Formula NatF() => Op("Nat");
    private static Formula IntF() => Op("Int");
    private static Formula Cast(Formula x, Formula t) => P(Seq(x, Colon, Sp, t));
    private static Formula Val(Formula x) => C("Fin.val", x);
    private static Formula RowF(Formula k) => C("Row", k);
    private static Formula Grid(Formula k, Formula n) => Arr(P(Seq(FinF(k), Sp, Times, Sp, FinF(n))), FinF(N(3)));
    private static Formula Sum(string v, Formula ty, Formula f) => Seq(new Formula.Subscript(F.Sum, P(Seq(V(v), Colon, Sp, ty))), Sp, f);
    private static Formula Ite(Formula p, Formula a, Formula b) => Seq(Op("if"), Sp, p, Sp, Op("then"), Sp, a, Sp, Op("else"), Sp, b);
    private static Formula FilterCard(Formula k, Formula n) => C("Finset.card", C("Finset.filter", Lam("f", Grid(k,n), C("Legal",V("f"))), Op("Finset.univ")));
    private static Formula Vec(params Formula[] xs) => Seq(Bang, OpenBracket, Join(xs), CloseBracket);
    private static Formula Join(Formula[] xs) => Seq(xs.SelectMany((x,i) => i == 0 ? new[]{x} : new[]{Comma,Sp,x}).ToArray());
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula At(Formula f, Formula i, Formula j) => A(f, P(Seq(i, Comma, Sp, j)));
    private static Formula Next(Formula i) => Seq(Langle, Sp, PlusF(Val(i),N(1)), Comma, Sp, V("h"), Rangle);
}
