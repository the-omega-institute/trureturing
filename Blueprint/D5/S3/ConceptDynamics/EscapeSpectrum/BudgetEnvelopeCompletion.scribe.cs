using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.EscapeSpectrum;

internal sealed class BudgetEnvelopeCompletionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/EscapeSpectrum/BudgetEnvelopeCompletion."
            + "budget_envelope_infimum_and_limit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative budget layers are cofinal among finite residual families, so their "
            + "escape envelope converges to the all-finite infimum.",
        H("Budget Envelope Completion"),
        Blocks(Describe.Lean(
            DescribeId.Create("budget-envelope-infimum-and-limit"),
            DeclarationHandle.Create(Declaration),
            H("The finite-family budget envelope has the all-finite limit"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A candidate is a Finset of the active definition subtype Gamma. Its "
                        + "cost uses the canonical finiteSelectionCost, and its residual mass "
                        + "uses the canonical finiteSelectionSupplement, concept join, and "
                        + "target-defect relation.")),
                Paragraph(Text(
                    "Every finite candidate is feasible at some nonnegative-real budget, "
                        + "while every budget layer contains only finite candidates. These two "
                        + "directions identify the infimum across budget layers with the "
                        + "infimum across all finite candidates.")),
                Paragraph(Text(
                    "Antitonicity and the common greatest lower bound give the filter-level "
                        + "limit atTop. Dividing by the positive baseline mass preserves the "
                        + "infimum and limit for the normalized escape spectrum.")),
                Paragraph(Text(
                    "The theorem asserts approximation by cofinal budget layers only. It does "
                        + "not assert that any finite candidate attains either infimum."))),
            DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula baseType = F.Id("C");
        Formula targetType = F.Id("Y");
        Formula valueFamily = F.Id("V");
        Formula gamma = F.Id("Gamma");
        Formula definitions = F.Id("d");
        Formula baseReadout = F.Id("q");
        Formula target = F.Id("T");
        Formula cost = F.Id("c");
        Formula weight = F.Id("nu");
        Formula selection = F.Id("S");
        Formula budget = F.Id("L");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nonnegativeReal = Sub(real, Seq(Geq, D(0)));
        Formula finiteGamma = Call("Finset", gamma);
        Formula baseline = Sub(F.Id("M"), D(0));
        Formula residualMass = Call("m", selection);
        Formula envelope = Call("M", budget);
        Formula spectrum = Call("rho", budget);
        Formula allFiniteInfimum = Sub(F.Id("m"), Star);
        Formula residualSet = Seq(
            OpenBrace, Call("m", selection), Sp, Mid, Sp,
            selection, Sp, InMacro, Sp, finiteGamma, CloseBrace);
        Formula envelopeSet = Seq(
            OpenBrace, Call("M", budget), Sp, Mid, Sp,
            budget, Sp, InMacro, Sp, nonnegativeReal, CloseBrace);
        Formula spectrumSet = Seq(
            OpenBrace, Call("rho", budget), Sp, Mid, Sp,
            budget, Sp, InMacro, Sp, nonnegativeReal, CloseBrace);
        Formula residualDefinition = Call(
            "mass",
            weight,
            Call(
                "defectRelation",
                Call(
                    "conceptJoin",
                    baseReadout,
                    Call("finiteSelectionSupplement", gamma, definitions, selection)),
                target));
        Formula baselineDefinition = Call(
            "mass", weight, Call("defectRelation", baseReadout, target));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Comma, Sp,
                baseType, Comma, Sp, targetType, Colon, Sp, type, Comma),
            Seq(
                valueFamily, Colon, Sp, indexType, Sp, To, Sp, type, Comma, Sp,
                gamma, Colon, Sp, Call("Set", indexType), Comma),
            Seq(
                definitions, Colon, Sp, Forall, Sp, F.Id("i"), Colon, Sp,
                indexType, Comma, Sp, stateType, Sp, To, Sp,
                Call("V", F.Id("i")), Comma),
            Seq(
                baseReadout, Colon, Sp, stateType, Sp, To, Sp, baseType, Comma, Sp,
                target, Colon, Sp, stateType, Sp, To, Sp, targetType, Comma),
            Seq(
                cost, Colon, Sp, indexType, Sp, To, Sp, real, Comma, Sp,
                weight, Colon, Sp,
                Call("EscapeWeight", Seq(stateType, Sp, Times, Sp, stateType)), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                baseline, Sp, Eq, Sp, baselineDefinition, Comma, Sp,
                residualMass, Sp, Eq, Sp, residualDefinition, Comma),
            Seq(
                Call("C", selection), Sp, Eq, Sp,
                Call("finiteSelectionCost", gamma, cost, selection), Comma),
            Seq(
                envelope, Sp, Eq, Sp, Call("sInf", Seq(
                    OpenBrace, Call("m", selection), Sp, Mid, Sp,
                    selection, Sp, InMacro, Sp, finiteGamma, Comma, Sp,
                    Call("C", selection), Sp, Leq, Sp, budget, CloseBrace)), Comma),
            Seq(
                spectrum, Sp, Eq, Sp, new Formula.Fraction(envelope, baseline), Comma, Sp,
                allFiniteInfimum, Sp, Eq, Sp, Call("sInf", residualSet), Comma),
            Seq(
                D(0), Sp, Lt, Sp, baseline, Sp, Land, Sp,
                Call("Monotone", Call("mass", weight)), Sp, Rightarrow),
            Seq(Call("Antitone", F.Id("M")), Sp, Land),
            Seq(
                Open, Forall, Sp, budget, Colon, Sp, nonnegativeReal, Comma, Sp,
                D(0), Sp, Leq, Sp, envelope, Sp, Leq, Sp, baseline, Close, Sp, Land),
            Seq(
                Call("sInf", envelopeSet), Sp, Eq, Sp, allFiniteInfimum, Sp, Land),
            Seq(
                Call("Tendsto", F.Id("M"), F.Id("atTop"),
                    Call("nhds", allFiniteInfimum)), Sp, Land),
            Seq(
                Call("sInf", spectrumSet), Sp, Eq, Sp,
                new Formula.Fraction(allFiniteInfimum, baseline), Sp, Land),
            Seq(
                Call("Tendsto", F.Id("rho"), F.Id("atTop"),
                    Call("nhds", new Formula.Fraction(allFiniteInfimum, baseline))), Dot),
        ]));
    }
}
