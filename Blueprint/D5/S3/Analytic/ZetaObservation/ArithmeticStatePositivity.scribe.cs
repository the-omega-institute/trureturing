using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class ArithmeticStatePositivityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized zeta state induces a positive arithmetic seminorm and its Hilbert "
            + "completion.",
        H("Arithmetic State Positivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("arithmetic-state-positivity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/ZetaObservation/ArithmeticStatePositivity."
                        + "arithmetic_positivity"),
                H("The arithmetic state is positive and completes to a Hilbert space"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A bounded complex observable is integrated against the repository's "
                            + "normalized zeta distribution at a real parameter above one. "
                            + "The zeroth natural-number term has zero mass, so the displayed "
                            + "natural sum is the source sum over positive integers.")),
                    Paragraph(Text(
                        "The first three conjuncts state positivity, the exact normalized "
                            + "weighted integer expansion, and the induced seminorm-square "
                            + "identity. The normalized series is nonnegative, the full complex "
                            + "state value equals its real coercion, and the real seminorm square "
                            + "equals that complex state value after coercion.")),
                    Paragraph(Text(
                        "The remaining conjuncts expose the canonical separation and completion: "
                            + "an observable maps to zero exactly when its seminorm vanishes, "
                            + "the canonical range is dense, the completion is complete, and its "
                            + "norm square is its self inner product.")),
                    Paragraph(Text(
                        "The construction uses the existing zeta distribution together with the "
                            + "pinned library's pre-inner-product core and uniform completion. "
                            + "No conjectural positivity principle is assumed."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        Seq(Open, Typed(name, type), Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula s = F.Id("s");
        Formula observable = F.Id("F");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula observableType = Seq(
            F.Id("C"), Underscore, Grp(F.Id("b")),
            Open, natural, Comma, Sp, complex, Close);
        Formula preHilbert = Call("ArithmeticPreHilbert", s);
        Formula hilbert = Call("ArithmeticHilbertSpace", s);
        Formula preObservable = Call("toArithmeticPreHilbert", s, observable);
        Formula selfProduct = Seq(
            Overline, Grp(observable), Sp, Times, Sp, observable);
        Formula stateValue = Call("arithmeticState", s, selfProduct);
        Formula observableNormSquare = Power(new Formula.Norm(Apply(observable, n)), D(2));
        Formula weightedTerm = Seq(
            observableNormSquare, Sp, Times, Sp, Power(n, Seq(Minus, s)));
        Formula weightedSum = Seq(
            Sum, Underscore, Grp(n, InMacro, natural), Sp, weightedTerm);
        Formula normalizedSum = Seq(
            new Formula.Fraction(D(1), Seq(Re, Open, Call("riemannZeta", s), Close)),
            Sp, Times, Sp, weightedSum);
        Formula normalizedComplex = Call("ofReal", normalizedSum);

        Formula positivity = new Formula.Relation(
            D(0), FormulaRelationOperator.LessThanOrEqual, normalizedSum);
        Formula exactExpansion = Equal(stateValue, normalizedComplex);
        Formula seminormIdentity = Equal(
            Call("ofReal", Power(new Formula.Norm(preObservable), D(2))),
            stateValue);
        Formula zeroSeparation = Iff(
            Equal(Call("CompletionCoe", preObservable), D(0)),
            Equal(new Formula.Norm(preObservable), D(0)));
        Formula denseRange = Call(
            "DenseRange",
            Lambda(x, preHilbert, Call("CompletionCoe", x)));
        Formula completeness = Call("CompleteSpace", hilbert);
        Formula innerLaw = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", hilbert)],
            Equal(
                Power(new Formula.Norm(x), D(2)),
                Seq(Re, Open, Call("inner", complex, x, x), Close)));
        Formula conclusion = And(
            positivity,
            And(
                exactExpansion,
                And(
                    seminormIdentity,
                    And(
                        zeroSeparation,
                        And(denseRange, And(completeness, innerLaw))))));
        Formula domain = new Formula.Relation(
            D(1), FormulaRelationOperator.LessThan, s);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", real), Bound("F", observableType)],
            Implies(domain, conclusion)));
    }
}
