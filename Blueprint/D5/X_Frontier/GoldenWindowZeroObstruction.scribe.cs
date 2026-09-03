using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.X_Frontier;

internal sealed class GoldenWindowZeroObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/X_Frontier/GoldenWindowZeroObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An off-line analytic zero conditionally obstructs normal-form O-5 window localization.",
        H("Golden Window Zero Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("o5-window-localization"),
                DeclarationHandle.Create(Prefix + "O5WindowLocalization"),
                H("O-5 window localization"),
                StatementSource.FromAuthor(LocalizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This definition restates the O-5 localization proposition directly. "
                            + "It asks for a meromorphic right-half-plane continuation that "
                            + "agrees with eulerGerm to the right of the golden window and "
                            + "places every analytic zero inside the open window on "
                            + "structuralZero.")),
                    Paragraph(Text(
                        "The definition uses phi, eulerGerm, and structuralZero from Hearts, "
                            + "but it does not depend on the open proof of o5_independence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "o5-window-localization-fails-of-offline-analytic-zero"),
                DeclarationHandle.Create(
                    Prefix + "o5_window_localization_fails_of_offline_analytic_zero"),
                H("An off-line analytic zero obstructs O-5 localization"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let W be analytic on the half-plane Re(s) greater than r and agree "
                            + "with eulerGerm to the right of the golden window. If W has a "
                            + "zero inside the window whose real part differs from "
                            + "structuralZero, then the displayed O-5 localization proposition "
                            + "cannot hold, subject to the explicit normal-form premise.")),
                    Paragraph(Text(
                        "The normal-form premise is the deliberate weakening from the originally "
                            + "requested bare MeromorphicOn statement. Mathlib permits a bare "
                            + "meromorphic representative to be changed at discrete exceptional "
                            + "points, so its point value at the proposed zero is not determined. "
                            + "MeromorphicNFOn fixes those values and makes pointwise continuation "
                            + "uniqueness available.")),
                    Paragraph(Text(
                        "The proof applies the repository theorem "
                            + "meromorphic_continuation_unique on the connected half-plane. "
                            + "Equality on the nonempty open right sub-half-plane is derived from "
                            + "the two eulerGerm agreement clauses, and equality at the proposed "
                            + "zero is therefore a conclusion rather than an added hypothesis.")),
                    Paragraph(Text(
                        "This is only a conditional reduction. It does not assert the existence "
                            + "of the off-line zero, the Riemann Hypothesis, or the falsity of O-5. "
                            + "Issue #5032 currently supplies numerical evidence for such a zero, "
                            + "not a formal existence proof."))),
                DescribeRole.Theorem))));

    private static Formula LocalizationFormula()
    {
        Formula complex = ComplexNumbers();
        Formula zqc = F.Id("Zqc");
        Formula s = F.Id("s");
        Formula positiveHalfPlane = HalfPlane(D(0));
        Formula agreement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Less(InversePhiSquared(), RealPart(s)),
                Equal(Apply(zqc, s), Apply(F.Id("eulerGerm"), s))));
        Formula localization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                LowerWindow(s),
                Implies(
                    UpperWindow(s),
                    Implies(
                        Call("AnalyticAt", complex, zqc, s),
                        Implies(
                            Equal(Apply(zqc, s), D(0)),
                            Equal(RealPart(s), F.Id("structuralZero")))))));
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("Zqc", Arrow(complex, complex))],
            And(
                Call("MeromorphicOn", zqc, positiveHalfPlane),
                And(agreement, localization)));

        return Disp(Equal(F.Id("O5WindowLocalization"), witness));
    }

    private static Formula ObstructionFormula()
    {
        Formula complex = ComplexNumbers();
        Formula real = RealNumbers();
        Formula w = F.Id("W");
        Formula s0 = F.Id("s0");
        Formula r = F.Id("r");
        Formula zqc = F.Id("Zqc");
        Formula s = F.Id("s");
        Formula continuationHalfPlane = HalfPlane(r);
        Formula agreement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Less(InversePhiSquared(), RealPart(s)),
                Equal(Apply(w, s), Apply(F.Id("eulerGerm"), s))));
        Formula candidateAgreement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Less(InversePhiSquared(), RealPart(s)),
                Equal(Apply(zqc, s), Apply(F.Id("eulerGerm"), s))));
        Formula normalFormPremise = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("Zqc", Arrow(complex, complex))],
            Implies(
                Call("MeromorphicOn", zqc, continuationHalfPlane),
                Implies(
                    candidateAgreement,
                    Call("MeromorphicNFOn", zqc, continuationHalfPlane))));
        Formula conclusion = new Formula.Not(F.Id("O5WindowLocalization"));
        Formula hypotheses = Implies(
            Less(D(0), r),
            Implies(
                Less(r, InversePhiSquared()),
                Implies(
                    Call("AnalyticOnNhd", complex, w, continuationHalfPlane),
                    Implies(
                        agreement,
                        Implies(
                            normalFormPremise,
                            Implies(
                                LowerWindow(s0),
                                Implies(
                                    UpperWindow(s0),
                                    Implies(
                                        Less(r, RealPart(s0)),
                                        Implies(
                                            Equal(Apply(w, s0), D(0)),
                                            Implies(
                                                NotEqual(
                                                    RealPart(s0),
                                                    F.Id("structuralZero")),
                                                conclusion))))))))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("W", Arrow(complex, complex)),
                Bound("s0", complex),
                Bound("r", real),
            ],
            hypotheses));
    }

    private static Formula HalfPlane(Formula lower)
    {
        Formula s = F.Id("s");
        return new Formula.SetBuilder(Less(lower, RealPart(s)), s, ComplexNumbers());
    }

    private static Formula LowerWindow(Formula s) =>
        Less(
            Divide(D(1), Multiply(D(2), PhiCubed())),
            RealPart(s));

    private static Formula UpperWindow(Formula s) =>
        Less(RealPart(s), InversePhiSquared());

    private static Formula InversePhiSquared() =>
        Divide(D(1), PhiSquared());

    private static Formula PhiSquared() =>
        new Formula.Power(F.Varphi, D(2));

    private static Formula PhiCubed() =>
        new Formula.Power(F.Varphi, D(3));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Grp(value));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
}
