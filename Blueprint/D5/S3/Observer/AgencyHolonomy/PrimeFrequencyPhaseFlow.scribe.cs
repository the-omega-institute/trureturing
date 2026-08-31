using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class PrimeFrequencyPhaseFlowDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier characters create unitary log-frequency time flow while scalar products forget order.",
        H("Prime-Frequency Fourier Phase Flow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fourier-phase-character-laws"),
                DeclarationHandle.Create(Prefix + "fourier_phase_character_laws"),
                H("Time-frequency character laws"),
                StatementSource.FromAuthor(FourierPhaseCharacterLawsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real frequency, comparison frequency, time, and shift, the phase "
                            + "at zero time is one, addition in either real argument becomes "
                            + "multiplication, and the phase has norm one.")),
                    Paragraph(Text(
                        "The final equality records symmetry of the numerical bilinear pairing "
                            + "between time and frequency. It does not identify their semantic "
                            + "roles or assert a preferred time direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordered-phase-product-collapse"),
                DeclarationHandle.Create(Prefix + "ordered_phase_product_collapse"),
                H("Scalar phase products forget order"),
                StatementSource.FromAuthor(OrderedPhaseProductCollapseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite list of real frequencies and every real time, the "
                            + "listed scalar phase product is the single phase at the sum of "
                            + "those frequencies.")),
                    Paragraph(Text(
                        "Consequently, lists with the same sum are indistinguishable at this "
                            + "commutative scalar-product layer. This is a countermodel to "
                            + "recovering list order from that product alone, not a claim that "
                            + "all Fourier or memory-bearing observer models erase chronology."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-fourier-synthesis-laws"),
                DeclarationHandle.Create(Prefix + "finite_fourier_synthesis_laws"),
                H("Finite synthesis shift and norm laws"),
                StatementSource.FromAuthor(FiniteFourierSynthesisLawsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite index type, complex amplitudes, real frequencies, and "
                            + "real time and shift, translating time distributes the shift "
                            + "phase through every term of the finite synthesis.")),
                    Paragraph(Text(
                        "At the original time, the synthesis norm is at most the sum of the "
                            + "amplitude norms because each phase has norm one. The theorem "
                            + "does not assert equality, inversion, Plancherel, irreversibility, "
                            + "or any statement about zero locations."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy")),
        ]));

    private static Formula Call(FormulaIdentifier name, params Formula[] arguments) =>
        new Formula.FunctionCall(name, [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula.BoundVariable Bound(FormulaIdentifier name, Formula domain) =>
        new(name, domain);

    private static Formula FourierPhaseCharacterLawsFormula()
    {
        Formula frequency = F.Id("frequency");
        Formula other = F.Id("other");
        Formula time = F.Id("time");
        Formula shift = F.Id("shift");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        FormulaIdentifier fourierPhase = FormulaIdentifier.Create("fourierPhase");
        Formula phaseAtZero = Equal(Call(fourierPhase, frequency, D(0)), D(1));
        Formula phaseAtTimeSum = Equal(
            Call(fourierPhase, frequency,
                new Formula.Binary(time, FormulaBinaryOperator.Add, shift)),
            Multiply(
                Call(fourierPhase, frequency, time),
                Call(fourierPhase, frequency, shift)));
        Formula phaseAtFrequencySum = Equal(
            Call(fourierPhase,
                new Formula.Binary(frequency, FormulaBinaryOperator.Add, other), time),
            Multiply(
                Call(fourierPhase, frequency, time),
                Call(fourierPhase, other, time)));
        Formula unitNorm = Equal(
            new Formula.Norm(Call(fourierPhase, frequency, time)), D(1));
        Formula symmetry = Equal(
            Call(fourierPhase, frequency, time),
            Call(fourierPhase, time, frequency));
        Formula conclusion = Seq(
            Open,
            phaseAtZero, Sp, Land, RowBreak, Grp(),
            phaseAtTimeSum, Sp, Land, RowBreak, Grp(),
            phaseAtFrequencySum, Sp, Land, RowBreak, Grp(),
            unitNorm, Sp, Land, RowBreak, Grp(),
            symmetry,
            Close);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound(FormulaIdentifier.Create("frequency"), real),
                Bound(FormulaIdentifier.Create("other"), real),
                Bound(FormulaIdentifier.Create("time"), real),
                Bound(FormulaIdentifier.Create("shift"), real),
            ],
            conclusion));
    }

    private static Formula OrderedPhaseProductCollapseFormula()
    {
        Formula frequencies = F.Id("frequencies");
        Formula time = F.Id("time");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        FormulaIdentifier orderedPhaseProduct =
            FormulaIdentifier.Create("orderedPhaseProduct");
        FormulaIdentifier fourierPhase = FormulaIdentifier.Create("fourierPhase");
        FormulaIdentifier sum = FormulaIdentifier.Create("sum");
        Formula conclusion = Equal(
            Call(orderedPhaseProduct, frequencies, time),
            Call(fourierPhase, Call(sum, frequencies), time));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound(
                    FormulaIdentifier.Create("frequencies"),
                    Call(FormulaIdentifier.Create("List"), real)),
                Bound(FormulaIdentifier.Create("time"), real),
            ],
            conclusion));
    }

    private static Formula FiniteFourierSynthesisLawsFormula()
    {
        Formula indexType = F.Id("iota");
        Formula amplitude = F.Id("amplitude");
        Formula frequency = F.Id("frequency");
        Formula time = F.Id("time");
        Formula shift = F.Id("shift");
        Formula p = F.Id("p");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        FormulaIdentifier fourierPhase = FormulaIdentifier.Create("fourierPhase");
        FormulaIdentifier finiteFourierSynthesis =
            FormulaIdentifier.Create("finiteFourierSynthesis");
        Formula amplitudeAtP = Apply(amplitude, p);
        Formula frequencyAtP = Apply(frequency, p);
        Formula phaseAtTime = Call(fourierPhase, frequencyAtP, time);
        Formula phaseAtShift = Call(fourierPhase, frequencyAtP, shift);
        Formula shiftedTerm = Multiply(
            Multiply(amplitudeAtP, phaseAtTime), phaseAtShift);
        Formula sumOverIndex = new Formula.Subscript(
            Sum, Seq(p, Colon, Sp, indexType));
        Formula shiftedSum = Seq(sumOverIndex, Sp, shiftedTerm);
        Formula timeShift = new Formula.Binary(time, FormulaBinaryOperator.Add, shift);
        Formula shiftLaw = Equal(
            Call(finiteFourierSynthesis, amplitude, frequency, timeShift),
            shiftedSum);
        Formula synthesisNorm = new Formula.Norm(
            Call(finiteFourierSynthesis, amplitude, frequency, time));
        Formula amplitudeNormSum = Seq(
            sumOverIndex, Sp, new Formula.Norm(amplitudeAtP));
        Formula normBound = new Formula.Relation(
            synthesisNorm,
            FormulaRelationOperator.LessThanOrEqual,
            amplitudeNormSum);
        Formula conclusion = Seq(
            Open,
            shiftLaw, Sp, Land, RowBreak, Grp(),
            normBound,
            Close);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound(FormulaIdentifier.Create("iota"), type),
                Bound(
                    FormulaIdentifier.Create("fintypeWitness"),
                    Call(FormulaIdentifier.Create("Fintype"), indexType)),
                Bound(FormulaIdentifier.Create("amplitude"), Arrow(indexType, complex)),
                Bound(FormulaIdentifier.Create("frequency"), Arrow(indexType, real)),
                Bound(FormulaIdentifier.Create("time"), real),
                Bound(FormulaIdentifier.Create("shift"), real),
            ],
            conclusion));
    }
}
