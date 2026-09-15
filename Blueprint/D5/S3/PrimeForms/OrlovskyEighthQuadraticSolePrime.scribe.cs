using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class OrlovskyEighthQuadraticSolePrimeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PrimeForms/orlovsky2009a165719");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive integral values of k(k+9)/8 have 17 as their only prime.",
        H("The Sole Prime among the Integral Eighth-Quadratic Values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a165719-integral-term"),
                DeclarationHandle.Create(Prefix + "IsTerm"),
                H("Integral values with positive parameter"),
                StatementSource.FromAuthor(TermFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A natural a is a term precisely when a positive natural k satisfies "
                        + "8a=k(k+9). This equation selects the integral values without rounding."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a165719-integrality-and-sole-prime"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The parameter classification and the sole prime"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every positive k, integrality is equivalent to k+1=8m or k=8m "
                        + "for a positive natural m. The value 17 occurs at k=8 and is prime. "
                        + "Every other term is greater than one and is not prime. Reduction "
                        + "modulo eight leaves only residues seven and zero. In the first case "
                        + "a=k(m+1), with both factors greater than one. In the second case "
                        + "a=m(8m+9); m=1 gives 17, and every larger m gives a composite value."))),
                DescribeRole.Theorem))));

    private static Formula TermFormula()
    {
        Formula a = F.Id("a"), k = F.Id("k");
        return Disp(Universal("a", Iff(Call("IsTerm", a),
            Existential("k", And(Less(D(0), k), Equal(Mul(D(8), a), Quadratic(k)))))));
    }

    private static Formula ResultFormula()
    {
        Formula a = F.Id("a"), k = F.Id("k"), m = F.Id("m");
        Formula classification = Universal("k", Implies(Less(D(0), k),
            Iff(Divides(D(8), Quadratic(k)), Existential("m", And(Less(D(0), m),
                Or(Equal(Add(k, D(1)), Mul(D(8), m)), Equal(k, Mul(D(8), m))))))));
        Formula primeTerm = And(Call("IsTerm", D(1, 7)), Call("Prime", D(1, 7)));
        Formula compositeTerms = Universal("a", Implies(Call("IsTerm", a),
            Implies(NotEqual(a, D(1, 7)), And(Less(D(1), a), new Formula.Not(Call("Prime", a))))));
        return Disp(And(classification, primeTerm, compositeTerms));
    }

    private static Formula Quadratic(Formula k) => Mul(k, Parenthesized(Add(k, D(9))));

    private static Formula Universal(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Naturals(), body);

    private static Formula Existential(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Naturals(), body);

    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
