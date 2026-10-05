using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;
internal sealed class PrefixPalindromicLengthNotAutomaticDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The PPL-difference of the period-doubling word has an infinite binary kernel.",H("Period-Doubling PPL-Difference Is Not Automatic"),Blocks(
        Describe.Lean(DescribeId.Create("pd-pplnotautomatic-claim"),DeclarationHandle.Create(Prefix+"claim"),
            H("Conjecture 17"),StatementSource.FromAuthor(Disp(Eqn(V("claim"),LiteralFormula()))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/fridlabordepeltomaki2021automaticppl")),
            Blocks(Paragraph(Text("Frid, Laborde and Peltomäki, On prefix palindromic length of automatic words, arXiv:2009.02934v2, page 13, Conjecture 17: "),
                Text("The sequence "), Math(new Formula.Subscript(V("d"),V("pd"))),
                Text(" of the period-doubling word "), Math(new Formula.Subscript(Seq(Mathbf,Grp(V("u"))),V("pd"))),
                Text(" is not "),Math(D(2)),Text("-automatic, and so the prefix palindromic length "),
                Math(new Formula.Apply(new Formula.Subscript(Ty("PPL"),V("pd")),[V("n")])),
                Text(" of "),Math(new Formula.Subscript(Seq(Mathbf,Grp(V("u"))),V("pd"))),
                Text(" is not "),Math(D(2)),Text("-regular.")),
                Paragraph(Text("The alphabet uses false for a and true for b, and the substitution is a to ab and b to aa. upd denotes the literal substitution word u_pd. PL minimizes the number of nonempty palindrome factors of the prefix of length n, with value zero on the empty prefix. The integer difference is PPL(n+1) minus PPL(n), for n at least zero. twoKernel includes every address (e,r) with e natural and r less than 2^e. Infinitude of this kernel is the stated non-automaticity criterion. cast records natural-to-integer coercion."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-pplnotautomatic-result"),DeclarationHandle.Create(Prefix+"result"),
            H("Infinite difference kernel"),StatementSource.FromAuthor(Disp(LiteralFormula())),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Exact sparse-family evaluations force unbounded rational rank of the PPL kernel. A finite difference kernel would force a finite-dimensional PPL kernel span by residue-block telescoping. This contradicts the rank bound and proves the displayed claim without hypotheses. The same rank argument proves the stronger failure of 2-regularity through infinite dimension of the rational kernel span."))),DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Prop() => Ty("Prop");
    private static Formula SetOf(Formula a) => Call("Set", a);
    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula NotF(Formula a) => new Formula.Not(a);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula At(Formula f, Formula x) => Call("val", f, x);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));




    private static Formula PInt(Formula n) => Cast(Call("PL",Call("ofFn",Seq(LambdaLower,Sp,V("i"),Colon,Call("Fin",n),Sp,Mapsto,Sp,Call("upd",Call("val",V("i")))))),Z());
    private static Formula LiteralFormula() => NotF(Call("Finite",Call("twoKernel",Seq(LambdaLower,Sp,V("n"),Colon,N(),Sp,Mapsto,Sp,Sub(PInt(Add(V("n"),D(1))),PInt(V("n")))))));
}
