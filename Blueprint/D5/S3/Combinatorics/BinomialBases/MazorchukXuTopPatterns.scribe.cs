using System.Linq;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuTopPatternsNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuTopPatternsNotation
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
        string prose, DescribeRole role, bool literature = false, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mazorchuk-xu-" + module.ToLowerInvariant() + "-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/MazorchukXu" + module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}


internal sealed class MazorchukXuTopPatternsDocument : IScribeDocumentDefinition
{
    private static Formula I => V("i");
    private static Formula Nn => V("n");
    private static Formula D => Mul(Fn("two"),I);
    private static Formula Fac(Formula a) => Fn("factorial",a);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The top weak-coordinate patterns are exactly a choice of position values and a permutation of the complementary cutoff values. Their factorial count proves the complete original all-deficit, all-valid-rank numerical polynomial conjecture for the literal triangular family.",
        H("The top coefficient and the complete Mazorchuk–Xu conjecture"),Blocks(
        Node("TopPatterns","patternCoefficient_top_factorial","Exact factorial count of the top patterns",
            All("i",N,Eq(Mul(Fac(I),Fn("patternCoefficient",I,D)),Fac(D))),
            "A full positive support of size 2i forces all 2i position and cutoff entries to be positive and pairwise distinct: removing zero and taking the union can otherwise not attain cardinality 2i. Thus the position entries increase strictly. The generic coordinate criterion gives exactly one exceptional-bit set. Choose its i position values as an i-subset of 1 through 2i, enumerate them in increasing order, and biject the i labelled cutoffs with the complementary values. The implemented finite bijection proves a(i,2i)=choose(2i,i)*i!. Mathlib card_finset_len, card_equiv and add_choose_mul_factorial_mul_factorial then give the displayed identity. Empty positions, empty complementary sets and i=0 are covered by the same construction.",DescribeRole.Theorem),
        Node("TopPatterns","mazorchukXu_conjecture","The original all-deficit polynomial statement",
            FullStatement(),
            "Take the actual countingPolynomial from the full weak-coordinate binomial sum. Its evaluation theorem applies to every natural n with i<=n+1, with no eventual threshold. The top factorial identity makes its coefficient at degree 2i equal to the nonzero rational inverse of i!, so its degree bound is attained and its leading coefficient is 1/i!. The conclusion is the original Conjecture defined in MazorchukXuClosure, whose count is the cardinality of the literal triangular subsets satisfying both conclusions of Condition (star), including repeated points. The proof retains empty subsets and rows, zero and tied coordinates, n=0, i=0, and i=n+1; it never evaluates a source family at n=-1. Mazorchuk and Xu supply the question and the already known first four deficit formulas. The coordinate-pattern argument supplies the general proof; no originality, priority or completed later-literature census is asserted.",DescribeRole.Theorem, resolution: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("mazorchuk-xu-2026-first-column-deficit-polynomial"),
                ResolutionKind.Proved))),[]));
    private static Formula FullStatement()
    {
        var p=V("p");
        var valid=Le(I,Plus(Nn,Fn("one")));
        var eval=Eq(Fn("eval",p,Fn("ratCast",Nn)),Fn("ratCast",Fn("count",Nn,Sub(Plus(Nn,Fn("one")),I))));
        return All("i",N,Ex("p",Fn("Polynomial",Q),And(Eq(Fn("natDegree",p),D),
            Eq(Fn("leadingCoeff",p),Fn("inv",Fn("ratCast",Fac(I)))),All("n",N,Imp(valid,eval)))));
    }
}
