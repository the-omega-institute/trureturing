using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenGaloisScalarCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden conjugation fixes exactly rational scalars and retains symmetric data.",
        H("Golden Galois Scalar Completion"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-conjugation-fixes-exactly-rational-scalars"),
            DeclarationHandle.Create(
                "D5/S3/Observer/GoldenCoding/GoldenGaloisScalarCompletion."
                    + "golden_galois_scalar_completion"),
            H("Golden conjugation fixes exactly the rational scalars"),
            StatementSource.FromAuthor(CompletionFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is the canonical rational quadratic algebra with generator "
                        + "squaring to five. The two golden conjugates are constructed in its "
                        + "rational coordinates as (1/2,1/2) and (1/2,-1/2).")),
                Paragraph(Text(
                    "Quadratic conjugation negates the second coordinate, so a fixed element "
                        + "has zero second coordinate and is exactly in the rational algebra-map "
                        + "range. Direct coordinate calculations prove that neither golden "
                        + "conjugate is fixed and establish their sum, product, and squared "
                        + "difference.")),
                Paragraph(Text(
                    "The source's qualitative statement that bare golden values usually "
                        + "disappear after completion has no quantified predicate. It is "
                        + "therefore commentary rather than an additional universal clause."))),
            DescribeRole.Theorem))));

    private static Formula CompletionFormula()
    {
        Formula rational = Call("Rational");
        Formula K = F.Id("K"), phi = F.Id("phi"), phiPrime = F.Id("phiPrime");
        Formula c = F.Id("c"), q = F.Id("q");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula carrier = Call("QuadraticAlgebra", rational, D(5), D(0));
        Formula fixedField = ForAll(
            "c",
            K,
            Iff(
                Equal(Call("star", c), c),
                Exists(
                    "q",
                    rational,
                    Equal(c, Call("algebraMap", rational, K, q)))));
        Formula clauses = All(
            fixedField,
            NotEqual(Call("star", phi), phi),
            NotEqual(Call("star", phiPrime), phiPrime),
            Equal(Add(phi, phiPrime), D(1)),
            Equal(Mul(phi, phiPrime), Neg(D(1))),
            Equal(Call("square", Sub(phi, phiPrime)), D(5)));
        Formula definitions = Seq(
            F.Id("let"), Sp, K, Sp, Eq, Sp, carrier, Semi, Sp,
            F.Id("let"), Sp, phi, Sp, Eq, Sp,
            Call("mk", half, half), Semi, Sp,
            F.Id("let"), Sp, phiPrime, Sp, Eq, Sp,
            Call("mk", half, Neg(half)), Semi, Sp,
            clauses);

        return Disp(definitions);
    }

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound(name, domain)],
            body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound(name, domain)],
            body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Neg(Formula value) => Call("neg", value);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Not(Equal(left, right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate(And);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
