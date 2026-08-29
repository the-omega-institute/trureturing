using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class SmoothExternalMomentEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula real = Call("Real"), natural = Call("Natural");
        Formula L = F.Id("L"), K = F.Id("K"), epsilon = F.Id("epsilon");
        Formula kappa = F.Id("kappa"), j = F.Id("j"), u = F.Id("u");
        Formula signedMeasure = Call("SignedMeasure", real);
        Formula functionType = new Formula.TypeArrow(real, real);
        Formula interval = Call("Icc", Seq(Minus, D(2), L), Mul(D(2), L));
        Formula jordan = Call("toJordanDecomposition", epsilon);
        Formula positivePart = Call("posPart", jordan);
        Formula negativePart = Call("negPart", jordan);
        Formula hpos = Equal(Call("restrict", positivePart, interval), positivePart);
        Formula hneg = Equal(Call("restrict", negativePart, interval), negativePart);
        Formula exponent = Mul(D(2), j);
        Formula signedMoment = Call("signedIntegral", u, Pow(u, exponent), epsilon);
        Formula correctionMoment = Call(
            "integral",
            u,
            Mul(Pow(u, exponent), Apply(kappa, u)),
            Call("volume"));
        Formula momentCancellation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", natural)],
            Implies(
                LessOrEqual(j, K),
                Equal(Add(signedMoment, correctionMoment), D(0))));
        Formula witnessProperties = All(
            Call("Even", kappa),
            Call("ContDiff", real, Call("infinity"), kappa),
            Call("HasCompactSupport", kappa),
            Seq(Call("tsupport", kappa), Sp, Subseteq, Sp, Call("compl", interval)),
            momentCancellation);
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("kappa", functionType)],
            witnessProperties);
        Formula statement = Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("L", real), Bound("K", natural), Bound("epsilon", signedMeasure)],
            Implies(All(hpos, hneg), conclusion)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "An even smooth correction supported outside a finite interval cancels every "
                + "prescribed even moment through a fixed order.",
            H("Smooth External Moment Elimination"),
            Blocks(Describe.Lean(
                DescribeId.Create("smooth-external-moment-elimination"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/TestFunctions/SmoothExternalMomentElimination."
                        + "smooth_external_finite_moment_elimination"),
                H("Smooth exterior cancellation of finitely many even moments"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reflected pairs of even derivatives of one compact bump form a lower "
                        + "triangular moment family. Integration by parts makes its diagonal "
                        + "nonzero, so the inverse finite moment matrix supplies the displayed "
                        + "even correction without entering the source interval."))),
                DescribeRole.Theorem))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Pow(Formula value, Formula exponent) =>
        Call("pow", value, exponent);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }
}
