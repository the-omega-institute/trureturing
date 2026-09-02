using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class PrescribedPairNegativeOrbitDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaBridge/PrescribedPairNegativeOrbit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite prescribed transform values make a nonreal off-line zero orbit negative, "
            + "while a real off-line orbit is a nonnegative norm square.",
        H("Prescribed-Pair Negative and Real Orbit Values"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prescribed-pair-gives-negative-zero-orbit"),
                DeclarationHandle.Create(
                    Prefix + "prescribed_pair_gives_negative_zero_orbit"),
                H("A prescribed spectral pair makes a nonreal off-line orbit negative"),
                StatementSource.FromAuthor(PrescribedNegativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For supplied ZeroData and a nonreal off-line zero, the conjugation index "
                        + "differs from the original index. The frozen four-point orbit identity "
                        + "and complex-frequency convolution-square factorization reduce the "
                        + "orbit real part to the product of the two prescribed transform values, "
                        + "giving minus four times the stored multiplicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-off-line-zero-orbit-sum-real-part"),
                DeclarationHandle.Create(
                    Prefix + "real_off_line_zero_orbit_sum_re"),
                H("A real off-line orbit is a nonnegative norm square"),
                StatementSource.FromAuthor(RealOrbitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real off-line zero, conjugation fixes both the zero index and its "
                        + "reflected index, while reflection remains distinct. The four displayed "
                        + "indices therefore collapse to a two-point orbit. Frozen reflection, "
                        + "evenness, and factorization identities identify its real value with "
                        + "twice the multiplicity times the transform norm square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prescribed-pair-impossible-for-real-zero"),
                DeclarationHandle.Create(
                    Prefix + "prescribed_pair_impossible_for_real_zero"),
                H("Opposite prescribed values are impossible at a real zero"),
                StatementSource.FromAuthor(RealPairImpossibleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reality makes conjugation fix the zero index. Spectral conjugation and "
                        + "evenness then identify the two transform evaluations, so they cannot "
                        + "simultaneously equal one and minus one."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Bound(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var i = 1; i < clauses.Length; i++)
        {
            result = Seq(Open, result, Close, Sp, Land, Sp, Open, clauses[i], Close);
        }
        return result;
    }

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula ImaginaryPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Im")), Sp, Open, value, Close);

    private static Formula ImpliesFormula(Formula premises, Formula conclusion) =>
        Seq(Open, premises, Close, Sp, Rightarrow, Sp, Open, conclusion, Close);

    private static Formula NegativeOne() => Seq(Minus, D(1));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula OrbitSum(
        Formula zeroData,
        Formula test,
        Formula index)
    {
        Formula reflection = Call("reflection", zeroData, index);
        Formula conjugation = Call("conjugation", zeroData, index);
        Formula conjugateReflection = Call("conjugation", zeroData, reflection);
        Formula orbitIndices = new Formula.SetLiteral(
            [index, reflection, conjugation, conjugateReflection]);
        Formula summationIndex = F.Id("k");
        Formula summand = Call(
            "zeroSummand",
            zeroData,
            Call("convolutionSquare", test),
            summationIndex);

        return Seq(
            new Formula.Subscript(
                Sum,
                Seq(summationIndex, Sp, InMacro, Sp, orbitIndices)),
            Sp,
            summand);
    }

    private static Formula PrescribedNegativeFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula index = F.Id("n");
        Formula test = F.Id("g");
        Formula zero = Call("zero", zeroData, index);
        Formula gamma = Call("gamma", zeroData, index);
        Formula transform = Call("fourierLaplace", test, gamma);
        Formula conjugateTransform =
            Call("fourierLaplace", test, Call("conj", gamma));
        Formula multiplicity = Call("multiplicity", zeroData, index);
        Formula premises = And(
            NotEqual(RealPart(zero), F.Id("criticalAbscissa")),
            NotEqual(ImaginaryPart(zero), D(0)),
            Equal(transform, D(1)),
            Equal(conjugateTransform, NegativeOne()));
        Formula conclusion = Equal(
            RealPart(OrbitSum(zeroData, test, index)),
            Seq(Minus, D(4), Sp, Cdot, Sp, multiplicity));

        return Disp(Seq(
            Forall, Sp,
            Bound(zeroData, F.Id("ZeroData")), Comma, Sp,
            Bound(index, Naturals()), Comma, Sp,
            Bound(test, F.Id("WeilTestFunction")), Comma, RowBreak, Grp(),
            ImpliesFormula(premises, conclusion), Dot));
    }

    private static Formula RealOrbitFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula index = F.Id("n");
        Formula test = F.Id("g");
        Formula zero = Call("zero", zeroData, index);
        Formula gamma = Call("gamma", zeroData, index);
        Formula multiplicity = Call("multiplicity", zeroData, index);
        Formula transform = Call("fourierLaplace", test, gamma);
        Formula premises = And(
            Equal(ImaginaryPart(zero), D(0)),
            NotEqual(RealPart(zero), F.Id("criticalAbscissa")));
        Formula conclusion = Equal(
            RealPart(OrbitSum(zeroData, test, index)),
            Seq(
                D(2), Sp, Cdot, Sp, multiplicity, Sp, Cdot, Sp,
                Call("normSq", transform)));

        return Disp(Seq(
            Forall, Sp,
            Bound(zeroData, F.Id("ZeroData")), Comma, Sp,
            Bound(index, Naturals()), Comma, Sp,
            Bound(test, F.Id("WeilTestFunction")), Comma, RowBreak, Grp(),
            ImpliesFormula(premises, conclusion), Dot));
    }

    private static Formula RealPairImpossibleFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula index = F.Id("n");
        Formula test = F.Id("g");
        Formula zero = Call("zero", zeroData, index);
        Formula gamma = Call("gamma", zeroData, index);
        Formula transform = Call("fourierLaplace", test, gamma);
        Formula conjugateTransform =
            Call("fourierLaplace", test, Call("conj", gamma));
        Formula premises = And(
            Equal(ImaginaryPart(zero), D(0)),
            Equal(transform, D(1)),
            Equal(conjugateTransform, NegativeOne()));

        return Disp(Seq(
            Forall, Sp,
            Bound(zeroData, F.Id("ZeroData")), Comma, Sp,
            Bound(index, Naturals()), Comma, Sp,
            Bound(test, F.Id("WeilTestFunction")), Comma, RowBreak, Grp(),
            ImpliesFormula(premises, F.Id("False")), Dot));
    }
}
