using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class DavisWidthDescentDifferenceCoprimeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Words/DavisWidthDescentDifferenceCoprime.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/davis2017widthk");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coprime-width descent differences have a shifted Eulerian distribution.",
        H("Davis's Coprime Width-Descent Difference Formula"),
        Blocks(
            Paragraph(Text(
                "All sizes and widths are natural numbers. Perm(Fin(n)) is the symmetric "
                    + "group on positions 0 through n-1. The symbol q^z denotes the Laurent "
                    + "monomial T(z), and every finite sum is taken in the Laurent polynomial "
                    + "ring over the integers.")),
            Node(
                "width-descents",
                "Width-k descents",
                WidthDescentsFormula(),
                "A position i contributes exactly when val(i)+k<n and the value at i is "
                    + "greater than the value k positions later. This is the zero-based form "
                    + "of the paper's index range [n-k].",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "eulerian-polynomial",
                "The Eulerian polynomial as a descent enumerator",
                EulerianFormula(),
                "The exponent is the ordinary width-one descent count. The paper identifies "
                    + "this descent generating function with A_m by MacMahon's theorem. Its "
                    + "separate infinite-series characterization is not used here.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "descent-difference-polynomial",
                "The width-descent difference polynomial",
                GFormula(),
                "For each permutation, the Laurent exponent is the integer difference between "
                    + "the width-k descent count and the width-(n-k) descent count.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "conjecture-nine-claim",
                "Davis's Conjecture 9",
                ClaimFormula(),
                "The printed statement is: \"Conjecture 9. If gcd(k, n) = 1, then "
                    + "G_{n,k}(q) = nq^{1-k}A_{n-1}(q).\" The surrounding paragraph gives "
                    + "the range 1 <= k < n. The displayed formula uses the paper's own "
                    + "identification of A_{n-1} with its descent generating function.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "conjecture-nine-result",
                "The coprime-width formula",
                ResultFormula(),
                "Multiplication by k modulo n first reindexes the width comparisons into one "
                    + "cycle. Rotating a permutation until its maximum is last then decomposes "
                    + "the cyclic descent enumerator into n copies of the ordinary descent "
                    + "enumerator on n-1 letters, with one additional descent.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create("davis-width-descent-" + id),
            DeclarationHandle.Create(Prefix + DeclarationName(id)),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            claim);

    private static string DeclarationName(string id) => id switch
    {
        "width-descents" => "widthDescents",
        "eulerian-polynomial" => "eulerian",
        "descent-difference-polynomial" => "G",
        "conjecture-nine-claim" => "claim",
        "conjecture-nine-result" => "result",
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Integers() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Int"));

    private static Formula LaurentPolynomials() =>
        Call("LaurentPolynomial", Integers());

    private static Formula Named(string name) =>
        Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula IntegerCast(Formula value) =>
        Parenthesized(Seq(value, Colon, Sp, Integers()));

    private static Formula LaurentPolynomialCast(Formula value) =>
        Parenthesized(Seq(value, Colon, Sp, LaurentPolynomials()));

    private static Formula Fin(Formula size) => Call("Fin", size);

    private static Formula Permutations(Formula size) => Call("Perm", Fin(size));

    private static Formula WidthDescents(Formula width, Formula permutation) =>
        Call("widthDescents", width, permutation);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula QPower(Formula exponent) =>
        new Formula.Power(F.Id("q"), exponent);

    private static Formula SumOver(Formula index, Formula carrier, Formula summand) =>
        Seq(new Formula.Subscript(Sum, Seq(index, Sp, InMacro, Sp, carrier)), Sp, summand);

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula Universal(Formula.BoundVariable[] variables, Formula body) =>
        Disp(new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body));

    private static Formula WidthDescentsFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula sigma = F.Id("sigma");
        Formula i = F.Id("i");
        Formula shifted = Add(Call("val", i), k);
        Formula condition = new Formula.Logic(
            Parenthesized(LessThan(shifted, n)),
            FormulaLogicOperator.And,
            Parenthesized(LessThan(Call("apply", sigma, shifted), Call("apply", sigma, i))));
        Formula positions = new Formula.Absolute(Seq(
            Left, OpenBrace,
            i, Sp, InMacro, Sp, Fin(n), Sp, Mid, Sp, condition,
            Right, CloseBrace));
        return Universal(
            [Bound("n", Naturals()), Bound("k", Naturals()), Bound("sigma", Permutations(n))],
            Equal(WidthDescents(k, sigma), positions));
    }

    private static Formula EulerianFormula()
    {
        Formula m = F.Id("m");
        Formula tau = F.Id("tau");
        Formula exponent = IntegerCast(WidthDescents(D(1), tau));
        return Universal(
            [Bound("m", Naturals())],
            Equal(Call("eulerian", m), SumOver(tau, Permutations(m), QPower(exponent))));
    }

    private static Formula GFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula sigma = F.Id("sigma");
        Formula exponent = Subtract(
            IntegerCast(WidthDescents(k, sigma)),
            IntegerCast(WidthDescents(Subtract(n, k), sigma)));
        return Universal(
            [Bound("n", Naturals()), Bound("k", Naturals())],
            Equal(Call("G", n, k), SumOver(sigma, Permutations(n), QPower(exponent))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula conclusion = Equal(
            Call("G", n, k),
            Multiply(
                Multiply(LaurentPolynomialCast(n), QPower(Subtract(D(1), IntegerCast(k)))),
                Call("eulerian", Subtract(n, D(1)))));
        Formula body = new Formula.Logic(
            Parenthesized(LessOrEqual(D(1), k)),
            FormulaLogicOperator.Implies,
            Parenthesized(new Formula.Logic(
                Parenthesized(LessThan(k, n)),
                FormulaLogicOperator.Implies,
                Parenthesized(new Formula.Logic(
                    Parenthesized(Call("Coprime", k, n)),
                    FormulaLogicOperator.Implies,
                    Parenthesized(conclusion))))));
        Formula quantified = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", Naturals()), Bound("k", Naturals())],
            body);
        return Disp(new Formula.Logic(
            F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(quantified)));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));
}
