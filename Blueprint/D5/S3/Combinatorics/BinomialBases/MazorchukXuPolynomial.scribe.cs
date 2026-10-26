using System.Linq;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuPolynomialNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuPolynomialNotation
{
    internal static Formula N => Fn("Nat");
    internal static Formula Q => Fn("Rat");
    internal static Formula Prop => Fn("Prop");
    internal static Formula Ty => Fn("Type");
    internal static Formula Pairs => Fn("Prod", N, N);
    internal static Formula Points => Fn("Finset", Pairs);
    internal static Formula V(string name) => F.Id(name);
    internal static Formula Fn(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    internal static Formula Apply(Formula fn, params Formula[] args) =>
        Seq(fn, Open, new Formula.LatexSequence([.. args.SelectMany((a, i) =>
            i == 0 ? new[] { a } : new[] { Comma, Sp, a })]), Close);
    internal static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Many(string names, Formula domain, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse()) body = All(name, domain, body);
        return body;
    }
    internal static Formula Par(Formula a) => Seq(Open, a, Close);
    internal static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    internal static Formula And(params Formula[] xs) =>
        xs.Aggregate((a, b) => Logic(a, FormulaLogicOperator.And, b));
    internal static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    internal static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    internal static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    internal static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    internal static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    internal static Formula Set(string name, Formula domain, Formula predicate) =>
        Seq(OpenBrace, V(name), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace);
    internal static Formula Rel(Formula a) => new Formula.TypeArrow(a, new Formula.TypeArrow(a, Prop));
    internal static Formula Map(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Ordered(string name, Formula body) =>
        All(name, Ty, Seq(OpenBracket, Fn("LinearOrder", V(name)), CloseBracket, Sp, body));
    internal static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/mazorchukxu2026cokernel");
    internal static DocumentBlock Node(string module, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature = false) =>
        Describe.Lean(DescribeId.Create("mazorchuk-xu-" + module.ToLowerInvariant() + "-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/MazorchukXu" + module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}


internal sealed class MazorchukXuPolynomialDocument : IScribeDocumentDefinition
{
    private static Formula I => V("i");
    private static Formula D => Mul(Fn("two"),I);
    private static Formula P => Fn("countingPolynomial",I);
    private static Formula Coeff(Formula k) => Fn("patternCoefficient",I,k);
    private static Formula Rational(Formula x) => Fn("ratCast",x);
    private static Formula Divide(Formula a,Formula b) => Fn("div",a,b);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal weak-coordinate binomial identity constructs one rational polynomial valid on all original ranks. Its exact conjectured degree and leading coefficient require the top-pattern factorial identity proved in MazorchukXuTopPatterns.",
        H("The rational counting polynomial on every original rank"),Blocks(
        Node("Polynomial","countingPolynomial","The actual rational counting polynomial",
            All("i",N,Eq(P,Fn("sum",Fn("range",Plus(D,Fn("one"))),Fn("lambda",V("k"),Mul(Fn("C",Divide(Rational(Coeff(V("k"))),Rational(Fn("factorial",V("k"))))),Fn("comp",Fn("descPochhammer",Q,V("k")),Fn("add",V("X"),Fn("C",Sub(Fn("one"),Rational(I)))))))))),
            "Use the pinned Mathlib falling-factorial polynomial divided by k!, shift its variable by 1-i in the rationals, and weight by the actual admissible pattern count. The sum is finite through 2i. No count identity or top coefficient is an assumption in this definition.",DescribeRole.Definition),
        Node("Polynomial","countingPolynomial_eval","One polynomial agrees at every valid n",
            Many("n i",N,Imp(Le(I,Plus(V("n"),Fn("one"))),Eq(Fn("eval",P,Rational(V("n"))),Rational(Fn("count",V("n"),Sub(Plus(V("n"),Fn("one")),I)))))),
            "Apply count_eq_binomial_sum and Mathlib Nat.cast_choose_eq_descPochhammer_div termwise. The inequality i<=n+1 justifies the natural-subtraction cast; the rational shift then evaluates exactly at M=n+1-i. The same polynomial works for every valid n, including n=0, M=0 and i=0.",DescribeRole.Theorem),
        Node("Polynomial","countingPolynomial_natDegree_le","The polynomial degree is at most 2i",
            All("i",N,Le(Fn("natDegree",P),D)),
            "The shifted k-th falling-factorial polynomial has degree k. Multiplication by its possibly zero scalar cannot increase degree. The finite sum therefore has degree at most 2i. This is an upper bound, not the conjectured exact degree.",DescribeRole.Theorem),
        Node("Polynomial","countingPolynomial_top_coeff","The coefficient at degree 2i",
            All("i",N,Eq(Fn("coeff",P,D),Divide(Rational(Coeff(D)),Rational(Fn("factorial",D))))),
            "All terms below 2i have zero coefficient at 2i. The shifted top falling-factorial polynomial is monic of degree 2i, by the pinned Mathlib APIs. Hence the displayed coefficient is its actual pattern count divided by (2i)!. The identity i!*a(i,2i)=(2i)! is proved in MazorchukXuTopPatterns and supplies the exact degree and leading coefficient in the full theorem there.",DescribeRole.Theorem)),[]));
}
