using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.Hermite;

internal sealed class GaussianPolynomialTotalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian-polynomial tests determine a complex Lebesgue square-integrable function.",
        H("Gaussian Polynomial Totality"),
        Blocks(Describe.Lean(
            DescribeId.Create("gaussian-polynomial-totality"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Analysis/Hermite/GaussianPolynomialTotality.gaussian_polynomial_totality"),
            H("Every positive Gaussian width gives a total polynomial test family"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/tauceti2026gaussianpolynomial")),
            Blocks(
                Paragraph(Text("Let b be strictly positive and let g be a complex square-integrable "
                    + "function on the real line with Lebesgue volume. If the integral of "
                    + "q(x) exp(-b x squared / 2) g(x) vanishes for every real polynomial q, "
                    + "then every such pairing is integrable and g vanishes almost everywhere.")),
                Paragraph(Text("No exponential decay is assumed for g. Gaussian domination and "
                    + "Cauchy-Schwarz give an exponential moment for the weighted function. "
                    + "Its vanishing monomial moments identify its positive and negative "
                    + "density measures through their analytic moment-generating functions. "
                    + "The argument applies to the real and imaginary parts.")),
                Paragraph(Text("For positive physical parameters hbar, mass and frequency, "
                    + "the width b equals mass times frequency divided by hbar. "
                    + "Normalized Hermite functions, product spaces and differential "
                    + "operator domains require their own correspondence statements."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula b = F.Id("b"), g = F.Id("g"), q = F.Id("q"), x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula polynomials = Seq(real, OpenBracket, F.Id("X"), CloseBracket);
        Formula volume = new Formula.NamedConstant(FormulaIdentifier.Create("volume"));
        Formula weight = Seq(Exp, Open, Minus, Frac,
            Grp(Mul(b, Seq(x, Caret, Grp(D(2))))), Grp(D(2)), Close);
        Formula expression = Mul(Mul(new Formula.Apply(q, [x]), weight), new Formula.Apply(g, [x]));
        Formula pairing = Seq(Int, Underscore, Grp(x, Colon, Sp, real), Sp,
            expression, Sp, F.Id("dx"));
        Formula vanishing = All([Bound("q", polynomials)], Equal(pairing, D(0)));
        Formula integrable = All([Bound("q", polynomials)],
            Call("Integrable", Seq(Open, x, Colon, Sp, real, Sp, Mapsto, Sp, expression, Close), volume));
        Formula zero = Seq(g, Sp, Eq, Underscore,
            Grp(Operatorname, Grp(F.Id("ae")), Comma, Sp, F.Id("dx")), Sp, D(0));
        return All([Bound("b", real), Bound("g", new Formula.TypeArrow(real, complex))],
            Seq(Open, new Formula.Relation(D(0), FormulaRelationOperator.LessThan, b), Sp,
                Land, Sp, Call("MemLp", g, D(2), volume), Sp, Land, Sp, vanishing, Close,
                Sp, Rightarrow, Sp, integrable, Sp, Land, Sp, zero));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
