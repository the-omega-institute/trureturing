using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class KrizekAntisigmaDecreaseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/KrizekAntisigmaDecreaseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/krizek2013a231548");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At n = 332640, antisigma decreases across a gap of three.",
        H("The OEIS A231548 Antisigma Gap-Three Conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("a231548-antisigma"),
                DeclarationHandle.Create(Prefix + "antisigma"),
                H("The antisigma function"),
                StatementSource.FromAuthor(AntisigmaFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each natural n, the finite interval contains the integers from "
                        + "one through n. The filter retains exactly those d that do not "
                        + "divide n, and the outer sum adds the retained values."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a231548-gap-three-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Krizek's gap-three conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least three, the conjecture says that "
                        + "antisigma at n minus three is at most antisigma at n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a231548-gap-three-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture fails at n = 332640"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At n = 332640, the divisor sums are sigma(332640) = 1451520 "
                        + "and sigma(332637) = 443520. The complement identity gives "
                        + "antisigma(332640) = 55323399600 and antisigma(332637) = "
                        + "55323409683. The first value is smaller, so the universal "
                        + "gap-three inequality is false."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a231548-antisigma-decrease-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula AntisigmaFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var interval = QualifiedCall("Finset", "Icc", D(1), n);
        var predicate = Lambda(d, new Formula.Not(
            new Formula.Relation(d, FormulaRelationOperator.Divides, n)));
        var filtered = QualifiedCall("Finset", "filter", interval, predicate);
        var sum = Seq(
            new Formula.Subscript(Sum, Seq(d, Sp, InMacro, Sp, filtered)),
            Sp,
            d);
        var equation = new Formula.Relation(
            Seq(Call("antisigma", n), Colon, Sp, Naturals()),
            FormulaRelationOperator.Equal,
            sum);
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            equation));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var premise = new Formula.Relation(
            D(3), FormulaRelationOperator.LessThanOrEqual, n);
        var conclusion = new Formula.Relation(
            Call("antisigma", Subtract(n, D(3))),
            FormulaRelationOperator.LessThanOrEqual,
            Call("antisigma", n));
        var quantified = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion));
        return Disp(new Formula.Logic(
            Parenthesized(F.Id("claim")),
            FormulaLogicOperator.Iff,
            Parenthesized(quantified)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Lambda(Formula variable, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, variable, Sp, Mapsto, Sp, body));

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
