using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.HolonomyBridge;

internal sealed class OffLineOrbitParityDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Off-line zero orbits split into even energy minus odd energy.",
        H("Off-Line Orbit Parity Decomposition"),
        Blocks(Describe.Lean(
            DescribeId.Create("off-line-orbit-parity-decomposition"),
            DeclarationHandle.Create(
                Prefix + "off_line_orbit_parity_decomposition"),
            H("Off-line orbit parity decomposition"),
            StatementSource.FromAuthor(ParityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For the stated non-self-conjugate off-line orbit, the test seed at the "
                        + "spectral parameter and its conjugate determines even and odd "
                        + "channels. The real four-point convolution-square contribution is "
                        + "their multiplicity-weighted even energy minus odd energy.")),
                Paragraph(Text(
                    "Both channel energies are nonnegative, so adding the odd correction "
                        + "recovers the even energy. The result is conditional on the supplied "
                        + "zero data and does not assert existence of an off-line orbit or a "
                        + "prime-side realization of the correction."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Let(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            name, Colon, Sp, type, Sp, Eq, Sp, value, Semi, RowBreak, Grp());

    private static Formula ParityFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula test = F.Id("g");
        Formula index = F.Id("n");
        Formula summationIndex = F.Id("k");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula orbitValue = F.Id("orbitValue");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula complexes = Seq(Mathbb, Grp(F.Id("C")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));

        Formula zero = Call("zero", zeroData, index);
        Formula gamma = Call("gamma", zeroData, index);
        Formula reflection = Call("reflection", zeroData, index);
        Formula conjugation = Call("conjugation", zeroData, index);
        Formula conjugateReflection =
            Call("conjugation", zeroData, reflection);
        Formula multiplicity = Call("multiplicity", zeroData, index);
        Formula orbitIndices = new Formula.SetLiteral(
            [index, reflection, conjugation, conjugateReflection]);
        Formula orbitSummand = Call(
            "zeroSummand",
            zeroData,
            Call("convolutionSquare", test),
            summationIndex);
        Formula finiteSum = Seq(
            new Formula.Subscript(
                Sum,
                Seq(summationIndex, Sp, InMacro, Sp, orbitIndices)),
            Sp, Re, Sp, Open, orbitSummand, Close);
        Formula firstValue = Call("fourierLaplace", test, gamma);
        Formula secondValue = Call(
            "fourierLaplace", test, Seq(Overline, Grp(gamma)));
        Formula orbitValueDefinition = finiteSum;
        Formula evenEnergy = Call("orbitEvenEnergy", multiplicity, first, second);
        Formula oddEnergy = Call("orbitOddEnergy", multiplicity, first, second);

        Formula premises = Seq(
            Open, conjugation, Sp, Neq, Sp, index, Close,
            Sp, Land, Sp,
            Open, Re, Sp, Open, zero, Close,
            Sp, Neq, Sp, F.Id("criticalAbscissa"), Close);
        Formula conclusions = Seq(
            Open,
            Open,
            orbitValue, Sp, Eq, Sp,
            evenEnergy, Sp, Minus, Sp, oddEnergy,
            Close,
            Sp, Land, RowBreak, Grp(),
            Open, D(0), Sp, Leq, Sp, oddEnergy, Close,
            Sp, Land, RowBreak, Grp(),
            Open,
            orbitValue, Sp, Plus, Sp, oddEnergy,
            Sp, Eq, Sp, evenEnergy,
            Close,
            Sp, Land, RowBreak, Grp(),
            Open, D(0), Sp, Leq, Sp, evenEnergy, Close,
            Close);

        return Disp(Seq(
            Forall, Sp,
            zeroData, Colon, Sp, F.Id("ZeroData"), Comma, Sp,
            test, Colon, Sp, F.Id("WeilTestFunction"), Comma, Sp,
            index, Colon, Sp, naturals, Comma, RowBreak, Grp(),
            premises, Sp, Rightarrow, RowBreak, Grp(),
            Let(first, complexes, firstValue),
            Let(second, complexes, secondValue),
            Let(orbitValue, reals, orbitValueDefinition),
            conclusions, Dot));
    }
}
