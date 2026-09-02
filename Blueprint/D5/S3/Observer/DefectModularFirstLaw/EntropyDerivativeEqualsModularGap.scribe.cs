using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.DefectModularFirstLaw;

internal sealed class EntropyDerivativeEqualsModularGapDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/DefectModularFirstLaw/EntropyDerivativeEqualsModularGap."
            + "entropy_derivative_equals_modular_gap";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a positive observation scale below the defect depth, rank-one thermal "
            + "entropy has derivative and full differential equal to the local modular gap.",
        H("Entropy Derivative Equals the Modular Gap"),
        Blocks(Describe.Lean(
            DescribeId.Create("entropy-derivative-equals-modular-gap"),
            DeclarationHandle.Create(Declaration),
            H("The local modular first law"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let delta and omega be real scales with 0 < omega < delta. The Lean "
                        + "definitions localModularWeight, rankOneThermalOccupation, "
                        + "rankOneThermalEntropy, and defectModularGap carry respectively "
                        + "q = (omega/delta)^2, the externally visible occupation "
                        + "N = q/(1-q), "
                        + "S(N) = (N+1) log(N+1) - N log N, and epsilon = "
                        + "2 log(delta/omega).")),
                Paragraph(Text(
                    "The first displayed group mirrors (1388.3): S has derivative "
                        + "log((N+1)/N) at N, this coefficient is -log q, and -log q is "
                        + "epsilon. HasDerivAt records both the derivative value and the "
                        + "differentiability implicit in dS/dN.")),
                Paragraph(Text(
                    "The second displayed group mirrors (1388.4): for every real increment "
                        + "dN, the Frechet derivative sends dN to epsilon*dN, and epsilon "
                        + "equals 2 log(delta/omega). These are the theorem's five public "
                        + "conclusion leaves in the same two groups as the source.")),
                Paragraph(Text(
                    "This is the local rank-one modular thermodynamic law. It neither asserts "
                        + "the existence of an off-critical zeta zero nor states the physical "
                        + "black-hole first law."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula delta = F.Id("delta");
        Formula omega = F.Id("omega");
        Formula q = F.Id("q");
        Formula occupation = F.Id("N");
        Formula entropy = F.Id("S");
        Formula epsilon = F.Id("epsilon");
        Formula increment = F.Id("dN");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula logRatio = Logarithm(Fraction(
            Seq(occupation, Plus, D(1)), occupation));
        Formula minusLogQ = Seq(Minus, Logarithm(q));
        Formula explicitGap = Seq(D(2), Sp, Logarithm(Fraction(delta, omega)));
        Formula derivative = Call("HasDerivAt", entropy, logRatio, occupation);
        Formula differential = Seq(
            Apply(Call("fderiv", real, entropy, occupation), increment),
            Sp, Eq, Sp, epsilon, Sp, increment);

        Formula firstBox = Seq(
            derivative, Sp, Land, RowBreak, Grp(),
            logRatio, Sp, Eq, Sp, minusLogQ, Sp, Land, RowBreak, Grp(),
            minusLogQ, Sp, Eq, Sp, epsilon);
        Formula secondBox = Seq(
            Open, Forall, Sp, increment, Colon, Sp, real, Comma, Sp,
            differential, Close, Sp, Land, RowBreak, Grp(),
            epsilon, Sp, Eq, Sp, explicitGap);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, delta, Comma, Sp, omega, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            D(0), Sp, Lt, Sp, omega, Sp, Land, Sp,
            omega, Sp, Lt, Sp, delta, Sp, Rightarrow,
            RowBreak, Grp(),
            OpenBracket, firstBox, CloseBracket, Sp, Land,
            RowBreak, Grp(),
            OpenBracket, secondBox, CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Logarithm(Formula argument) =>
        Seq(Log, Sp, Open, argument, Close);
}
