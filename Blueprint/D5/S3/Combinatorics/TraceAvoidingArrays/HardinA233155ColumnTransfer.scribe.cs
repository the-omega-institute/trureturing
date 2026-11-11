using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233155ColumnTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233155");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("a233155-column-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unrestricted columns retain the literal horizontal and antidiagonal bonds.",
        H("Three-state column transfer"), Blocks(
            Node("columnCompatible",CompatibleFormula(),"Every horizontal and antidiagonal bond between the two columns excludes sum two."),
            Node("relabel",RelabelFormula(),"A color permutation acts pointwise on a column."),
            Node("successorClasses",SuccessorsFormula(),"The list records each compatible successor class in base-three code order."),
            Node("quotient_rows",QuotientFormula(),"Permutation-invariant equality classes and their representative successor lists determine all quotient entries.",true),
            Node("count_transfer",TransferFormula(),"Currying along columns identifies literal arrays with constrained words. The quotient and its initial multiplicities count every length at least two.",true)), []));
    private static Formula RelabelFormula() {
        var body=Eq(C("relabel",V("e")),C("Equiv.arrowCongr",C("Equiv.refl",FinF(V("k"))),V("e")));
        return All("k",NatF(),All("e",PermF(),body));
    }
    private static Formula SuccessorsFormula() {
        var codeType=FinF(Pow(N(3),V("k")));
        var column=C("decode",V("k"),V("c"));
        var list=C("List.finRange",Pow(N(3),V("k")));
        var predicate=Lam("c",codeType,C("decide",C("columnCompatible",V("r"),column)));
        var filtered=C("List.filter",predicate,list);
        var mapped=C("List.map",Lam("c",codeType,A(V("cls"),column)),filtered);
        return KQ(All("cls",Arr(RowF(V("k")),FinF(V("q"))),All("r",RowF(V("k")),Eq(C("successorClasses",V("cls"),V("r")),mapped))));
    }
    private static Formula PermF() => C("Equiv.Perm",FinF(N(3)));
    private static Formula KQ(Formula f) => All("k",NatF(),All("q",NatF(),f));
    private static Formula CompatibleFormula() {
        var r=V("r"); var s=V("s"); var i=V("i"); var k=V("k");
        var horizontal=All("i",FinF(k),Ne(PlusF(Val(A(r,i)),Val(A(s,i))),N(2)));
        var diagonal=All("i",FinF(k),All("h",LtF(PlusF(Val(i),N(1)),k),Ne(PlusF(Val(A(s,i)),Val(A(r,Next(i)))),N(2))));
        return All("k",NatF(),All("r",RowF(k),All("s",RowF(k),Eq(C("columnCompatible",r,s),And(horizontal,diagonal)))));
    }
    private static Formula Counts() => Sum("c",RowF(V("k")),Ite(And(C("columnCompatible",V("r"),V("c")),Eq(A(V("cls"),V("c")),V("s"))),Cast(N(1),IntF()),N(0)));
    private static Formula HQ() => All("r",RowF(V("k")),All("s",FinF(V("q")),Eq(Counts(),A(V("Q"),A(V("cls"),V("r")),V("s")))));
    private static Formula HW() => All("s",FinF(V("q")),Eq(Sum("r",RowF(V("k")),Ite(Eq(A(V("cls"),V("r")),V("s")),Cast(N(1),IntF()),N(0))),A(V("w"),V("s"))));
    private static Formula QuotientFormula() {
        var invariant=All("e",PermF(),All("r",RowF(V("k")),Eq(A(V("cls"),C("relabel",V("e"),V("r"))),A(V("cls"),V("r")))));
        var representative=All("r",RowF(V("k")),new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("e"),PermF(),Eq(C("relabel",V("e"),V("r")),A(V("rep"),A(V("cls"),V("r"))))));
        var table=All("i",FinF(V("q")),All("s",FinF(V("q")),Eq(C("List.sum",C("List.map",Lam("j",FinF(V("q")),Ite(Eq(V("j"),V("s")),Cast(N(1),IntF()),N(0))),C("successorClasses",V("cls"),A(V("rep"),V("i"))))),A(V("Q"),V("i"),V("s")))));
        return KQ(All("cls",Arr(RowF(V("k")),FinF(V("q"))),All("rep",Arr(FinF(V("q")),RowF(V("k"))),All("Q",C("Matrix",FinF(V("q")),FinF(V("q")),IntF()),Imp(invariant,Imp(representative,Imp(table,HQ())))))));
    }
    private static Formula TransferFormula() {
        var conclusion=All("n",NatF(),Eq(Cast(C("T",PlusF(V("n"),N(2)),V("k")),IntF()),C("dotProduct",V("w"),C("Matrix.mulVec",Pow(V("Q"),PlusF(V("n"),N(1))),Cast(N(1),Arr(FinF(V("q")),IntF()))))));
        return KQ(All("cls",Arr(RowF(V("k")),FinF(V("q"))),All("Q",C("Matrix",FinF(V("q")),FinF(V("q")),IntF()),All("w",Arr(FinF(V("q")),IntF()),Imp(HQ(),Imp(HW(),conclusion))))));
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
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula PlusF(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
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
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Next(Formula i) => Seq(Langle, Sp, PlusF(Val(i),N(1)), Comma, Sp, V("h"), Rangle);
}
