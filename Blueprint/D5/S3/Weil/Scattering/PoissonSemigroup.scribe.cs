using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class PoissonSemigroupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Poisson convolution transports the observed profile from sigma to sigma plus eta.",
        H("Coarse Poisson Semigroup"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coarse-poisson-semigroup"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Scattering/PoissonSemigroup.coarse_poisson_semigroup"),
                H("Coarse Poisson smoothing is a semigroup"),
                StatementSource.FromAuthor(Disp(Formula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real-function carrier exposes the source convolution channel, the "
                            + "Poisson kernels P, the observed profiles d, and a fixed source "
                            + "profile. Associativity, the kernel scale-addition law, and the "
                            + "profile representation are independent hypotheses.")),
                    Paragraph(Text(
                        "At sigma greater than one and eta positive, rewriting the two profile "
                            + "representations and applying the kernel law reduces the result "
                            + "to associativity of convolution."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        var star = F.Id("star");
        var P = F.Id("P");
        var d = F.Id("d");
        var source = F.Id("source");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var realFn = Seq(reals, To, reals);
        var sigma = F.Id("sigma");
        var eta = F.Id("eta");
        var f = F.Id("f");
        var g = F.Id("g");
        var h = F.Id("h");
        var app = (Formula fn, Formula x) => Seq(fn, Open, x, Close);
        var assoc = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("f"), realFn),
             new Formula.BoundVariable(FormulaIdentifier.Create("g"), realFn),
             new Formula.BoundVariable(FormulaIdentifier.Create("h"), realFn)],
            Equal(app(app(star, f), app(app(star, g), h)),
                app(app(star, app(app(star, f), g)), h)));
        var kernel = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("sigma"), reals),
             new Formula.BoundVariable(FormulaIdentifier.Create("eta"), reals)],
            new Formula.Logic(
                new Formula.Logic(
                    new Formula.Relation(D(1), FormulaRelationOperator.LessThan, sigma),
                    FormulaLogicOperator.And,
                    new Formula.Relation(D(0), FormulaRelationOperator.LessThan, eta)),
                FormulaLogicOperator.Implies,
                Equal(app(app(star, app(P, eta)), app(P, sigma)), app(P, Add(sigma, eta)))));
        var profile = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("sigma"), reals,
            Equal(app(d, sigma), app(app(star, app(P, sigma)), source)));
        var premises = new Formula.Logic(assoc, FormulaLogicOperator.And,
            new Formula.Logic(kernel, FormulaLogicOperator.And, profile));
        var conclusion = Equal(app(d, Add(sigma, eta)),
            app(app(star, app(P, eta)), app(d, sigma)));
        var bounds = new Formula.Logic(
            new Formula.Relation(D(1), FormulaRelationOperator.LessThan, sigma),
            FormulaLogicOperator.And,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, eta));
        var quantifiedConclusion = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("sigma"), reals),
             new Formula.BoundVariable(FormulaIdentifier.Create("eta"), reals)],
            new Formula.Logic(bounds, FormulaLogicOperator.Implies, conclusion));
        return Seq(
            Forall, Sp, star, Colon, Sp, Seq(realFn, To, realFn, To, realFn), Comma, Sp,
            Forall, Sp, P, Colon, Sp, Seq(reals, To, realFn), Comma, Sp,
            Forall, Sp, d, Colon, Sp, Seq(reals, To, realFn), Comma, Sp,
            Forall, Sp, source, Colon, Sp, realFn, Comma, Sp,
            premises, Sp, Rightarrow, Sp,
            quantifiedConclusion);
    }
}
