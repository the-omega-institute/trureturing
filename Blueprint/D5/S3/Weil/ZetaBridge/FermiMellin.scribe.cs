using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class FermiMellinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/FermiMellin.";
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula X => F.Id("x");
    private static Formula S => F.Id("s");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fermi Mellin integral on the positive half-plane and the Salem RH criterion.",
        H("Fermi Mellin Integral"),
        Blocks(
            Theorem("fermi_mellin_integrable", "Positive-scale integrability",
                Domain(Integrable(X, S)),
                "The exponentially dominated finite-prefix kernel gives convergence for every "
                    + "positive scale and every complex exponent with positive real part."),
            Theorem("fermi_mellin_eq_of_ne_one", "Value away from one",
                Domain(Implies(Ne(S, D(1)), Equal(Integral(X, S), Product(X, S)))),
                "The paired finite integrals meet the public frozen natural alternating-sum "
                    + "limit. Positive scaling preserves the entire domain, including real part one."),
            Theorem("fermi_mellin_product_tendsto_one", "Removable product limit",
                PositiveScale(Equal(
                    Seq(Lim, Underscore, Grp(S, InMacro, C, Comma, Sp,
                        S, To, D(1), Comma, Sp, S, Neq, D(1)),
                        Sp, Product(X, S)), Endpoint(X))),
                "The dyadic derivative quotient cancels the zeta residue. Gamma and scale "
                    + "are continuous at one; equality of the products is used only off one."),
            Theorem("fermi_mellin_at_one", "Actual integral at one",
                PositiveScale(Equal(Integral(X, D(1)), Endpoint(X))),
                "Exponential decay and boundedness at zero make the actual Mellin transform "
                    + "continuous at one. Its value is identified by the punctured product limit."),
            Theorem("fermi_mellin_identity", "Full-domain identity",
                Domain(And(Integrable(X, S), Equal(Integral(X, S),
                    Call("ite", Equal(S, D(1)), Endpoint(X), Product(X, S))))),
                "The endpoint branch is a proved integral value. The raw totalized "
                    + "Gamma-dyadic-zeta product at one is not substituted for that value."),
            Theorem("fermi_mellin_nonzero_iff_zeta_nonzero", "Pointwise strip nonvanishing",
                All("s", C, Implies(Strip(S), Equivalent(
                    Ne(Integral(D(1), S), D(0)), Ne(Call("riemannZeta", S), D(0))))),
                "Gamma has no zero for positive real part. The dyadic factor can vanish "
                    + "only at real part one, outside this open strip."),
            Theorem("salem_mellin_nonvanishing_iff_rh", "Salem criterion iff RH",
                Criterion(),
                "Both implications use the actual complex integral. All real imaginary "
                    + "coordinates are quantified. The integral criterion implies the standard "
                    + "Riemann hypothesis by the frozen right-half-strip reduction."))));

    private static DocumentBlock.Describe Theorem(
        string name, string title, Formula formula, string narrative) => Describe.Lean(
        DescribeId.Create(name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Weil/sanftenberg2026fermi")),
        Blocks(Paragraph(Text(narrative))), DescribeRole.Theorem);

    private static Formula Criterion()
    {
        var delta = F.Id("delta");
        var gamma = F.Id("gamma");
        var exponent = Seq(delta, Minus, D(1), Plus, F.Id("i"), Thin, gamma);
        return Equivalent(All("delta", R,
            Implies(Less(new Formula.Fraction(D(1), D(2)), delta),
                Implies(Less(delta, D(1)), All("gamma", R,
                    Ne(IntegralExponent(D(1), exponent), D(0)))))),
            Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))));
    }

    private static Formula Domain(Formula body) => PositiveScale(All("s", C,
        Implies(Less(D(0), Call("Re", S)), body)));
    private static Formula PositiveScale(Formula body) => All("x", R,
        Implies(Less(D(0), X), body));
    private static Formula Strip(Formula s) => And(
        Less(new Formula.Fraction(D(1), D(2)), Call("Re", s)), Less(Call("Re", s), D(1)));
    private static Formula Endpoint(Formula x) => new Formula.Fraction(Call("log", D(2)), x);
    private static Formula Product(Formula x, Formula s) => Seq(
        x, Caret, Grp(Minus, s), Thin, Call("Gamma", s), Thin,
        Open, D(1), Minus, D(2), Caret, Grp(D(1), Minus, s), Close,
        Thin, Call("riemannZeta", s));
    private static Formula Kernel(Formula x, Formula exponent) => new Formula.Fraction(
        Seq(F.Id("t"), Caret, Grp(exponent)),
        Seq(Call("exp", Seq(x, Thin, F.Id("t"))), Plus, D(1)));
    private static Formula Integral(Formula x, Formula s) =>
        IntegralExponent(x, Seq(s, Minus, D(1)));
    private static Formula IntegralExponent(Formula x, Formula exponent) => Seq(
        Int, Underscore, Grp(D(0)), Caret, Grp(Infty), Sp,
        Kernel(x, exponent), Thin, F.Id("d"), F.Id("t"));
    private static Formula Integrable(Formula x, Formula s) => Call("IntegrableOn",
        Seq(F.Id("t"), Mapsto, Kernel(x, Seq(s, Minus, D(1)))), Call("Ioi", D(0)));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Equivalent(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
