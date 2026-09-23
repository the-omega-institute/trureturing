using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class CruxProblem2623RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/CruxProblem2623Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/zejnulahiarslanagic2001problem2623");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic ratio-sum monotonicity assertion in Crux Problem 2623 is false.",
        H("Crux Problem 2623: cyclic ratio-sum monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("crux-2623-cyclic-ratio-sum"),
                DeclarationHandle.Create(Prefix + "S"),
                H("The cyclic ratio sum"),
                StatementSource.FromAuthor(SFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n with a nonzero residue ring, S(x,k) sums over every j in "
                        + "ZMod n. Finset.range(k+1) contains exactly 0 through k. "
                        + "The numerator uses x(j+i), while the denominator uses "
                        + "x(j+(i+1)); both natural indices are cast to ZMod n before "
                        + "addition, so residue addition supplies the cyclic wraparound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crux-2623-monotonicity-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed monotonicity assertion"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every n at least two and every positive real-valued function "
                        + "on ZMod n, the assertion requires S(x,k+1) <= S(x,k) whenever "
                        + "k+2 <= n. The bound on n supplies the nonzero instance used "
                        + "by ZMod n. Lean index j=0 corresponds to printed index j=1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crux-2623-monotonicity-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The monotonicity assertion is false"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take n=4, k=1, and the cyclic tuple (1,2,1,2). Its four terms "
                        + "give S(x,1)=1+1+1+1=4, while S(x,2)=4/5+5/4+4/5+5/4="
                        + "41/10. Thus S(x,2) is strictly greater than S(x,1), at an "
                        + "interior index rather than an endpoint."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("crux-problem-2623-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula SFormula()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        var k = F.Id("k");
        var i = F.Id("i");
        var j = F.Id("j");
        var zmodN = Call("ZMod", n);
        var range = QualifiedCall("Finset", "range", Add(k, D(1)));
        var numerator = IndexedSum(i, range,
            Call("x", Add(j, Coerce(i, zmodN))));
        var denominator = IndexedSum(i, range,
            Call("x", Add(j,
                Coerce(Coerce(Add(i, D(1)), Naturals()), zmodN))));
        var outerSum = IndexedSum(j, zmodN,
            new Formula.Fraction(numerator, denominator));
        var equation = Equal(Call("S", x, k), outerSum);
        var withK = ForAll("k", Naturals(), equation);
        var withX = ForAll("x", FunctionType(zmodN, Reals()), withK);
        var withInstance = ImpliesFormula(Call("NeZero", n), withX);
        return Disp(ForAll("n", Naturals(), withInstance));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        var k = F.Id("k");
        var j = F.Id("j");
        var zmodN = Call("ZMod", n);
        var positivity = ForAll("j", zmodN,
            new Formula.Relation(
                D(0), FormulaRelationOperator.LessThan, Call("x", j)));
        var bound = new Formula.Relation(
            Add(k, D(2)), FormulaRelationOperator.LessThanOrEqual, n);
        var monotonicity = new Formula.Relation(
            Call("S", x, Add(k, D(1))),
            FormulaRelationOperator.LessThanOrEqual,
            Call("S", x, k));
        var kClause = ForAll("k", Naturals(),
            ImpliesFormula(bound, monotonicity));
        var xClause = ForAll("x", FunctionType(zmodN, Reals()),
            ImpliesFormula(positivity, kClause));
        var nBound = new Formula.Relation(
            D(2), FormulaRelationOperator.LessThanOrEqual, n);
        var quantified = ForAll("n", Naturals(),
            ImpliesFormula(nBound, xClause));
        return Disp(new Formula.Logic(
            Parenthesized(F.Id("claim")),
            FormulaLogicOperator.Iff,
            Parenthesized(quantified)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula IndexedSum(
        Formula index,
        Formula domain,
        Formula summand) =>
        Seq(new Formula.Subscript(
                Sum,
                Seq(index, Sp, InMacro, Sp, domain)),
            Sp,
            summand);

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula FunctionType(Formula source, Formula target) =>
        Parenthesized(Seq(source, Sp, To, Sp, target));

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            domain,
            body);

    private static Formula ImpliesFormula(Formula premise, Formula conclusion) =>
        new Formula.Logic(
            Parenthesized(premise),
            FormulaLogicOperator.Implies,
            Parenthesized(conclusion));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Reals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Real"));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
