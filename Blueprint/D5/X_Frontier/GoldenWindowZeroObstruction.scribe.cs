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
        "Normal-form candidates are obstructed, while bare meromorphic candidates evade point tests.",
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
                    "no-normal-form-o5-candidate-of-offline-analytic-zero"),
                DeclarationHandle.Create(
                    Prefix + "no_normal_form_o5_candidate_of_offline_analytic_zero"),
                H("An off-line analytic zero obstructs normal-form candidates"),
                StatementSource.FromAuthor(NormalFormObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let W be analytic on the half-plane Re(s) greater than r and agree "
                            + "with eulerGerm to the right of the golden window. If W has a "
                            + "zero inside the window whose real part differs from "
                            + "structuralZero, then no candidate satisfying the displayed "
                            + "MeromorphicNFOn contract can pass the guarded zero test.")),
                    Paragraph(Text(
                        "The regularity requirement belongs to each candidate inside the negated "
                            + "existential. There is no external premise asserting that every bare "
                            + "meromorphic representative is in normal form.")),
                    Paragraph(Text(
                        "The proof applies the repository theorem "
                            + "meromorphic_continuation_unique on the connected half-plane. "
                            + "Equality on the nonempty open right sub-half-plane is derived from "
                            + "the two eulerGerm agreement clauses, and equality at the proposed "
                            + "zero is therefore a conclusion rather than an added hypothesis.")),
                    Paragraph(Text(
                        "This theorem does not refute O5WindowLocalization or claim that O-5 is "
                            + "false. The frozen O-5 statement allows arbitrary meromorphic "
                            + "representatives, so a genuine refutation would first require a "
                            + "stronger candidate contract. The required zero also remains "
                            + "conditional: issue #5032 supplies numerical evidence, not a formal "
                            + "existence proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bare-meromorphic-candidate-evades-zero-test"),
                DeclarationHandle.Create(
                    Prefix + "bare_meromorphic_candidate_evades_zero_test"),
                H("A bare meromorphic candidate evades a guarded point test"),
                StatementSource.FromAuthor(BareCandidateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let W be analytic on Re(s) greater than r and agree with eulerGerm to "
                            + "the right of the golden window. At any point x in that analytic "
                            + "half-plane but left of the agreement region, changing only W(x) "
                            + "produces a candidate that remains meromorphic and preserves the "
                            + "agreement clause, but is not analytic at x.")),
                    Paragraph(Text(
                        "The witness is Function.update W x (W x + 1). Mathlib's "
                            + "MeromorphicAt.update proves that the single-point change preserves "
                            + "meromorphy, while continuousAt_update_same and uniqueness of limits "
                            + "show that analyticity at x would force one to equal zero.")),
                    Paragraph(Text(
                        "This positive result formalizes the limitation in the original O-5 "
                            + "statement: its AnalyticAt guard can be made false at a selected "
                            + "point without violating bare MeromorphicOn. Therefore the "
                            + "normal-form obstruction above is not a refutation of frozen O-5."))),
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

    private static Formula NormalFormObstructionFormula()
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
        Formula normalCandidate = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("Zqc", Arrow(complex, complex))],
            And(
                Call("MeromorphicOn", zqc, HalfPlane(D(0))),
                And(
                    candidateAgreement,
                    And(
                        Call("MeromorphicNFOn", zqc, continuationHalfPlane),
                        localization))));
        Formula conclusion = new Formula.Not(normalCandidate);
        Formula hypotheses = Implies(
            Less(D(0), r),
            Implies(
                Less(r, InversePhiSquared()),
                Implies(
                    Call("AnalyticOnNhd", complex, w, continuationHalfPlane),
                    Implies(
                        agreement,
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
                                            conclusion)))))))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("W", Arrow(complex, complex)),
                Bound("s0", complex),
                Bound("r", real),
            ],
            hypotheses));
    }

    private static Formula BareCandidateFormula()
    {
        Formula complex = ComplexNumbers();
        Formula real = RealNumbers();
        Formula w = F.Id("W");
        Formula x = F.Id("x");
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
        Formula candidate = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("Zqc", Arrow(complex, complex))],
            And(
                Call("MeromorphicOn", zqc, continuationHalfPlane),
                And(
                    candidateAgreement,
                    new Formula.Not(Call("AnalyticAt", complex, zqc, x)))));
        Formula hypotheses = Implies(
            Less(r, RealPart(x)),
            Implies(
                Less(RealPart(x), InversePhiSquared()),
                Implies(
                    Call("AnalyticOnNhd", complex, w, continuationHalfPlane),
                    Implies(agreement, candidate))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("W", Arrow(complex, complex)),
                Bound("x", complex),
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
