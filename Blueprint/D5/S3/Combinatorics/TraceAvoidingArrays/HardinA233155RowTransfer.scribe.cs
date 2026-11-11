using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233155RowTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233155");
    private static DocumentBlock Node(string declaration, Formula formula, string prose, bool count = false, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("a233155-" + declaration.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + declaration), H(declaration), StatementSource.FromAuthor(Disp(formula)), count ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Row sequences retain every labelled array and both kinds of excluded bond.",
        H("Three-state row transfer"), Blocks(
            Node("Row", All("k",NatF(),Eq(RowF(V("k")),Arr(FinF(V("k")),FinF(N(3))))), "A row is a function from the columns to the three states."),
            Node("rowLegal", RowLegalFormula(), "Each horizontal bond has sum different from two."),
            Node("compatible", CompatibleFormula(), "The upper row's next entry and the lower row's current entry have sum different from two."),
            Node("Legal", LegalFormula(), "Every row is legal and every consecutive pair is compatible."),
            Node("T", All("k",NatF(),All("n",NatF(),Eq(C("T",V("k"),V("n")),FilterCard(V("k"),V("n"))))), "The filtered finite set counts every function on the rectangle.", true),
            Node("decode", All("k",NatF(),All("c",FinF(Pow(N(3),V("k"))),Eq(C("decode",V("k"),V("c")),A(C("finFunctionFinEquiv.symm"),V("c"))))), "Base-three codes enumerate all rows."),
            Node("legalCodes", CodesFormula(), "Filtering the complete code list retains exactly the legal rows."),
            Node("row_sum", RowSumFormula(), "The sum over legal row functions equals the sum over their codes.", theorem:true),
            Node("row_sequence_bridge", SequenceFormula(), "Currying gives a bijection between literal arrays and row sequences with their local constraints.", theorem:true),
            Node("count_transfer", TransferFormula(), "Equal successor counts in each class give a matrix quotient. Initial class multiplicities and a matrix power count strips of every height at least two.", theorem:true)), []));
    private static Formula K(Formula f) => All("k",NatF(),f);
    private static Formula RowLegalFormula() => K(All("r",RowF(V("k")),Eq(C("rowLegal",V("r")),All("j",FinF(V("k")),All("h",LtF(PlusF(Val(V("j")),N(1)),V("k")),Ne(PlusF(Val(A(V("r"),V("j"))),Val(A(V("r"),Next(V("j"))))),N(2)))))));
    private static Formula CompatibleFormula() => K(All("r",RowF(V("k")),All("s",RowF(V("k")),Eq(C("compatible",V("r"),V("s")),All("j",FinF(V("k")),All("h",LtF(PlusF(Val(V("j")),N(1)),V("k")),Ne(PlusF(Val(A(V("r"),Next(V("j")))),Val(A(V("s"),V("j")))),N(2))))))));
    private static Formula RowConditions(Formula k, Formula n, Formula fn, bool grid) {
        Formula R(Formula i) => grid ? RowAt(fn,i,k) : A(fn,i);
        return And(All("i",FinF(n),C("rowLegal",R(V("i")))),All("i",FinF(n),All("h",LtF(PlusF(Val(V("i")),N(1)),n),C("compatible",R(V("i")),R(Next(V("i")))))));
    }
    private static Formula LegalFormula() => K(All("n",NatF(),All("f",Grid(V("k"),V("n")),Eq(C("Legal",V("f")),RowConditions(V("k"),V("n"),V("f"),true)))));
    private static Formula CodesFormula() => K(Eq(C("legalCodes",V("k")),C("List.filter",Lam("c",FinF(Pow(N(3),V("k"))),C("decide",C("rowLegal",C("decode",V("k"),V("c"))))),C("List.finRange",Pow(N(3),V("k"))))));
    private static Formula RowSumFormula() {
        var k=V("k"); var f=V("F");
        var lhs=Sum("r",RowF(k),Ite(C("rowLegal",V("r")),A(f,V("r")),N(0)));
        var rhs=C("List.sum",C("List.map",
            Lam("c",FinF(Pow(N(3),k)),A(f,C("decode",k,V("c")))),C("legalCodes",k)));
        return K(All("F",Arr(RowF(k),IntF()),Eq(lhs,rhs)));
    }

    private static Formula SequenceFormula() {
        var k=V("k"); var n=PlusF(V("n"),N(1));
        var subtype=Seq(OpenBrace,V("r"),Colon,Sp,Arr(FinF(n),RowF(k)),Sp,Mid,Sp,RowConditions(k,n,V("r"),false),CloseBrace);
        return K(All("n",NatF(),Eq(C("T",k,n),C("Nat.card",subtype))));
    }
    private static Formula HQ() => All("r",RowF(V("k")),Imp(C("rowLegal",V("r")),All("s",FinF(V("q")),Eq(Sum("c",RowF(V("k")),Ite(And(C("rowLegal",V("c")),And(C("compatible",V("r"),V("c")),Eq(A(V("cls"),V("c")),V("s")))),Cast(N(1),IntF()),N(0))),A(V("Q"),A(V("cls"),V("r")),V("s"))))));
    private static Formula HW() => All("s",FinF(V("q")),Eq(Sum("r",RowF(V("k")),Ite(And(C("rowLegal",V("r")),Eq(A(V("cls"),V("r")),V("s"))),Cast(N(1),IntF()),N(0))),A(V("w"),V("s"))));
    private static Formula TransferFormula() {
        var q=V("q"); var k=V("k"); var n=V("n");
        var scalar=C("dotProduct",V("w"),C("Matrix.mulVec",Pow(V("Q"),PlusF(n,N(1))),
            Cast(N(1),Arr(FinF(q),IntF()))));
        var conclusion=All("n",NatF(),Eq(Cast(C("T",k,PlusF(n,N(2))),IntF()),scalar));
        var conditional=Imp(HQ(),Imp(HW(),conclusion));
        return K(All("q",NatF(),All("cls",Arr(RowF(k),FinF(q)),
            All("Q",C("Matrix",FinF(q),FinF(q),IntF()),
            All("w",Arr(FinF(q),IntF()),conditional)))));
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
    private static Formula Lam(string name, Formula type, Formula body) => P(Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, P(body)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
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
    private static Formula Grid(Formula k, Formula n) => Arr(Seq(FinF(n), Sp, Times, Sp, FinF(k)), FinF(N(3)));
    private static Formula At(Formula f, Formula i, Formula j) => A(f, P(Seq(i, Comma, Sp, j)));
    private static Formula RowAt(Formula f, Formula i, Formula k) => Lam("j", FinF(k), At(f, i, V("j")));
    private static Formula Next(Formula j) => Seq(Langle, Sp, PlusF(Val(j), N(1)), Comma, Sp, V("h"), Rangle);
    private static Formula Sum(string v, Formula ty, Formula f) => Seq(new Formula.Subscript(F.Sum, P(Seq(V(v), Colon, Sp, ty))), Sp, f);
    private static Formula Ite(Formula p, Formula a, Formula b) => Seq(Op("if"), Sp, p, Sp, Op("then"), Sp, a, Sp, Op("else"), Sp, b);
    private static Formula FilterCard(Formula k, Formula n) => C("Finset.card", C("Finset.filter", Lam("f", Grid(k,n), C("Legal",V("f"))), Op("Finset.univ")));
}
