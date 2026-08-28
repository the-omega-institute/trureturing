using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class ApproximateSimulationWithoutExactAttainmentDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Estimation/DataProcessing/ApproximateSimulationWithoutExactAttainment."
            + "approximate_simulation_without_exact_attainment";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero nonnegative simulation infimum is approximate domination, while a nonclosed "
            + "family of stochastic postprocessors need not contain an exact member.",
        H("Approximate Simulation Without Exact Attainment"),
        Blocks(Describe.Lean(
            DescribeId.Create("approximate-simulation-without-exact-attainment"),
            DeclarationHandle.Create(Declaration),
            H("Zero simulation defect need not be attained"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For any nonempty simulator class with a nonnegative error cost, infimum "
                        + "zero is equivalent to the existence of a simulator below every "
                        + "positive tolerance.")),
                Paragraph(Text(
                    "K is the deterministic experiment on the singleton observation space, "
                        + "and L is the deterministic Boolean target law concentrated at false. "
                        + "Both are constructed as finite Markov kernels.")),
                Paragraph(Text(
                    "The nth admissible simulator assigns mass 1/(n+2) to true and the "
                        + "remaining mass to false. Its total-variation simulation error is "
                        + "therefore exactly 1/(n+2).")),
                Paragraph(Text(
                    "These errors have infimum zero and become smaller than every positive "
                        + "tolerance, while positivity of 1/(n+2) rules out an exact simulator "
                        + "inside the same family."))),
            DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula TheoremFormula()
    {
        Formula unit = F.Id("Unit");
        Formula boolean = F.Id("Bool");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula star = F.Id("star");
        Formula bit = F.Id("b");
        Formula index = F.Id("n");
        Formula epsilon = F.Id("epsilon");
        Formula experiment = F.Id("K");
        Formula target = F.Id("L");
        Formula simulator = F.Id("M");
        Formula error = F.Id("err");
        Formula simulatorType = F.Id("S");
        Formula genericSimulator = F.Id("m");
        Formula genericError = F.Id("e");
        Formula genericErrorAt = Call("e", genericSimulator);
        Formula simulatorAt = Sub(simulator, index);
        Formula errorAt = Sub(error, index);
        Formula fraction = new Formula.Fraction(D(1), Seq(index, Plus, D(2)));
        Formula Kernel(Formula source, Formula output) =>
            Call("FiniteMarkovKernel", source, output);
        Formula Row(Formula kernel) => Call("row", kernel, star);
        Formula targetValue = Call("if", bit, D(0), D(1));
        Formula simulatorValue = Call("if", bit, fraction, Seq(D(1), Minus, fraction));
        Formula composed = Call("channelOutput", simulatorAt, Row(experiment));
        Formula errors = Seq(
            OpenBrace, errorAt, Sp, Mid, Sp,
            index, Sp, InMacro, Sp, natural, CloseBrace);
        Formula genericErrors = Seq(
            OpenBrace, Call("e", genericSimulator), Sp, Mid, Sp,
            genericSimulator, Sp, InMacro, Sp, simulatorType, CloseBrace);

        return Disp(new Formula.Aligned([
            Seq(
                Open, Forall, Sp, simulatorType, Colon, Sp, type, Comma, Sp,
                genericError, Colon, Sp, simulatorType, Sp, To, Sp, real, Comma),
            Seq(
                Call("Nonempty", simulatorType), Sp, Land, Sp,
                Open, Forall, Sp, genericSimulator, Colon, Sp, simulatorType, Comma, Sp,
                D(0), Sp, Le, Sp, genericErrorAt, Close, Sp, Rightarrow),
            Seq(
                Open, Call("sInf", genericErrors), Sp, Eq, Sp, D(0), Sp, Iff, Sp,
                Forall, Sp, epsilon, Colon, Sp, real, Comma, Sp,
                D(0), Sp, Lt, Sp, epsilon, Sp, Rightarrow, Sp,
                Exists, Sp, genericSimulator, Colon, Sp, simulatorType, Comma, Sp,
                genericErrorAt, Sp, Lt, Sp, epsilon, Close, Close, Sp, Land),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                experiment, Colon, Sp, Kernel(unit, unit), Comma, Sp,
                Call("value", experiment, star, star), Sp, Eq, Sp, D(1), Comma),
            Seq(
                target, Colon, Sp, Kernel(unit, boolean), Comma, Sp,
                Call("value", target, star, bit), Sp, Eq, Sp, targetValue, Comma),
            Seq(
                simulator, Colon, Sp, natural, Sp, To, Sp, Kernel(unit, boolean), Comma, Sp,
                Call("value", simulatorAt, star, bit), Sp, Eq, Sp, simulatorValue, Comma),
            Seq(
                errorAt, Sp, Eq, Sp,
                Call("TV", Row(target), composed), Comma),
            Seq(
                Call("sInf", errors), Sp, Eq, Sp, D(0), Sp, Land),
            Seq(
                Neg, Sp, Exists, Sp, index, Colon, Sp, natural, Comma, Sp,
                Row(target), Sp, Eq, Sp, composed, Dot),
        ]));
    }
}
