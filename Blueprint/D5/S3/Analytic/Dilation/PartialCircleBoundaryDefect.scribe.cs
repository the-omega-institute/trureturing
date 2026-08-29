using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class PartialCircleBoundaryDefectDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Dilation/PartialCircleBoundaryDefect."
            + "partial_circle_boundary_defect";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A golden-regulator arc accumulates only its endpoint mismatch.",
        H("Partial-Circle Boundary Defect"),
        Blocks(Describe.Lean(
            DescribeId.Create("partial-circle-boundary-defect"),
            DeclarationHandle.Create(Declaration),
            H("The regulator-arc break is an endpoint term"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The two real embeddings, anisotropic form, golden-unit zeta, break "
                        + "field, and accumulated arc defect are all constructed explicitly "
                        + "on the nonzero integer-pair lattice.")),
                Paragraph(Text(
                    "The source restricts the identity to a convergence region where "
                        + "termwise differentiation is permitted. The displayed derivative "
                        + "and interval-integrability premises encode exactly that analytic "
                        + "scope, including the necessary nonzero spectral parameter.")),
                Paragraph(Text(
                    "The fundamental theorem of calculus gives the endpoint difference. "
                        + "For an arc of one complete regulator period, the imported exact "
                        + "lattice reindexing identifies the endpoints and the defect vanishes."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula integers = Call("Integer"), reals = Call("Real"), complexes = Call("Complex");
        Formula pair = Call("Product", integers, integers);
        Formula alpha = F.Id("alpha"), eta = F.Id("eta"), t = F.Id("t");
        Formula s = F.Id("s"), eta0 = F.Id("eta0"), eta1 = F.Id("eta1");
        Formula sigmaPlus = F.Id("sigmaPlus"), sigmaMinus = F.Id("sigmaMinus");
        Formula form = F.Id("anisotropicForm"), zeta = F.Id("goldenUnitZeta");
        Formula breakField = F.Id("goldenBreak"), defect = F.Id("accumulatedDefect");
        Formula embeddingType = Arrow(pair, reals);
        Formula formType = Arrow(reals, Arrow(pair, reals));
        Formula zetaType = Arrow(complexes, Arrow(reals, complexes));
        Formula defectType = Arrow(complexes, Arrow(reals, Arrow(reals, complexes)));
        Formula pairZero = Call("pair", D(0), D(0));
        Formula nonzeroPairs = Call(
            "Subtype",
            pair,
            Lambda(alpha, NotEqual(alpha, pairZero)));
        Formula sigmaPlusAt = Apply(sigmaPlus, alpha);
        Formula sigmaMinusAt = Apply(sigmaMinus, alpha);
        Formula etaForm = Apply(form, eta, alpha);
        Formula period = Mul(D(2), Call("log", F.Varphi));

        Formula sigmaPlusDefinition = Lambda(
            alpha,
            Add(
                Call("intCastReal", Call("fst", alpha)),
                Mul(Call("intCastReal", Call("snd", alpha)), F.Varphi)));
        Formula sigmaMinusDefinition = Lambda(
            alpha,
            Add(
                Call("intCastReal", Call("fst", alpha)),
                Mul(Call("intCastReal", Call("snd", alpha)), F.Psi)));
        Formula formDefinition = Lambda(
            eta,
            Lambda(
                alpha,
                Add(
                    Mul(Call("exp", eta), Pow(sigmaPlusAt, D(2))),
                    Mul(Call("exp", Neg(eta)), Pow(sigmaMinusAt, D(2))))));
        Formula zetaDefinition = Lambda(
            s,
            Lambda(
                eta,
                Call(
                    "tsum",
                    nonzeroPairs,
                    Lambda(alpha, Pow(Apply(form, eta, alpha), Neg(s))))));
        Formula breakNumerator = Sub(
            Mul(Call("exp", eta), Pow(sigmaPlusAt, D(2))),
            Mul(Call("exp", Neg(eta)), Pow(sigmaMinusAt, D(2))));
        Formula breakDefinition = Lambda(
            s,
            Lambda(
                eta,
                Call(
                    "tsum",
                    nonzeroPairs,
                    Lambda(
                        alpha,
                        new Formula.Fraction(
                            breakNumerator,
                            Pow(etaForm, Add(s, D(1))))))));
        Formula defectDefinition = Lambda(
            s,
            Lambda(
                eta0,
                Lambda(
                    eta1,
                    Call(
                        "intervalIntegral",
                        eta0,
                        eta1,
                        Lambda(eta, Apply(breakField, s, eta))))));

        Formula derivativePremise = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("eta", Call("uIcc", eta0, eta1))],
            Call(
                "HasDerivAt",
                Lambda(t, Apply(zeta, s, t)),
                Neg(Mul(s, Apply(breakField, s, eta))),
                eta));
        Formula integrabilityPremise = Call(
            "IntervalIntegrable",
            Lambda(eta, Apply(breakField, s, eta)),
            Call("volume"),
            eta0,
            eta1);
        Formula boundaryIdentity = Equal(
            Apply(defect, s, eta0, eta1),
            Mul(
                Neg(new Formula.Fraction(D(1), s)),
                Sub(Apply(zeta, s, eta1), Apply(zeta, s, eta0))));
        Formula fullPeriod = Implies(
            Equal(Sub(eta1, eta0), period),
            Equal(Apply(defect, s, eta0, eta1), D(0)));
        Formula quantified = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complexes), Bound("eta0", reals), Bound("eta1", reals)],
            Implies(
                NotEqual(s, D(0)),
                Implies(
                    derivativePremise,
                    Implies(integrabilityPremise, And(boundaryIdentity, fullPeriod)))));

        return Disp(Seq(
            F.Id("let"), Sp, sigmaPlus, Colon, Sp, embeddingType, Sp, Eq, Sp,
            sigmaPlusDefinition, Semi, Sp,
            F.Id("let"), Sp, sigmaMinus, Colon, Sp, embeddingType, Sp, Eq, Sp,
            sigmaMinusDefinition, Semi, Sp,
            F.Id("let"), Sp, form, Colon, Sp, formType, Sp, Eq, Sp,
            formDefinition, Semi, Sp,
            F.Id("let"), Sp, zeta, Colon, Sp, zetaType, Sp, Eq, Sp,
            zetaDefinition, Semi, Sp,
            F.Id("let"), Sp, breakField, Colon, Sp, zetaType, Sp, Eq, Sp,
            breakDefinition, Semi, Sp,
            F.Id("let"), Sp, defect, Colon, Sp, defectType, Sp, Eq, Sp,
            defectDefinition, Semi, Sp,
            quantified));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Lambda(Formula binder, Formula body) =>
        Call("lambda", binder, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Pow(Formula value, Formula exponent) =>
        Call("pow", value, exponent);

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

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
