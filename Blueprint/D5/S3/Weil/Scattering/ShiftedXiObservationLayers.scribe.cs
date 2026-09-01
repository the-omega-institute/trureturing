using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class ShiftedXiObservationLayersDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Scattering/ShiftedXiObservationLayers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite shifted-xi observations are sharp reflections linked by the frozen scattering quotient.",
        H("Shifted Xi Observation Layers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-shifted-xi-observation"),
                DeclarationHandle.Create(Prefix + "shiftedXiObservation"),
                H("Positive shifted-xi observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive layer evaluates the frozen xi reading at one half plus "
                        + "the real observation depth minus i times the spectral coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sharp-shifted-xi-observation"),
                DeclarationHandle.Create(Prefix + "shiftedXiObservationSharp"),
                H("Sharp shifted-xi observation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Sharp reflection conjugates the value of the positive observation at "
                        + "the conjugate spectral coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shifted-xi-observation-layers"),
                DeclarationHandle.Create(Prefix + "shifted_xi_observation_layers"),
                H("The two shifted-xi observation layers"),
                StatementSource.FromAuthor(MainTheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At positive real depth, xi reflection identifies the sharp positive "
                            + "observation with the negative shifted layer. The existing shifted-xi "
                            + "scattering reading is exactly the quotient of these two layers.")),
                    Paragraph(Text(
                        "The positive layer is assumed nonzero before quotient multiplication is "
                            + "cancelled. This excludes Lean's totalized division-by-zero value.")),
                    Paragraph(Text(
                        "This is the self-contained algebraic observation-layer closure of the "
                            + "source. The Suzuki meromorphic-inner criterion and the associated "
                            + "de Branges claims require external analytic definitions and results "
                            + "and are not asserted here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-depth-observation-witness"),
                DeclarationHandle.Create(Prefix + "positive_depth_observation_witness"),
                H("A regular observation at depth one half"),
                StatementSource.FromAuthor(PositiveWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Depth one half and spectral coordinate zero give a concrete positive-depth "
                        + "instance whose positive layer is nonzero and satisfies all three laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-denominator-breaks-transition-recovery"),
                DeclarationHandle.Create(Prefix + "zero_denominator_breaks_transition_recovery"),
                H("A zero denominator breaks transition recovery"),
                StatementSource.FromAuthor(ZeroDenominatorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete numerator one and denominator zero show that quotient "
                        + "multiplication cannot recover a nonzero numerator without the regularity "
                        + "premise."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Scattering/FiniteScatteringCascade")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/Symmetry/ZetaConjugationCovariance")),
        ]));

    private static Formula MainTheoremFormula()
    {
        Formula omega = F.Omega;
        Formula z = F.Id("z");
        Formula positive = Call("shiftedXiObservation", omega, z);
        Formula sharp = Call("shiftedXiObservationSharp", omega, z);
        Formula scattering = Call("shiftedXiScattering", omega, z);
        Formula negative = Call(
            "xiReading",
            Subtract(Subtract(Fraction(D(1), D(2)), omega), Multiply(F.Id("i"), z)));

        return Disp(Seq(
            Forall, Sp, omega, Sp, InMacro, Sp, Reals(), Comma, Sp,
            Forall, Sp, z, Sp, InMacro, Sp, Complexes(), Comma, RowBreak, Grp(),
            Open, omega, Sp, Gt, Sp, D(0), Sp, Land, Sp,
            positive, Sp, Neq, Sp, D(0), Close, Sp, Rightarrow, RowBreak, Grp(),
            sharp, Sp, Eq, Sp, negative, Sp, Land, RowBreak, Grp(),
            scattering, Sp, Eq, Sp, Fraction(sharp, positive), Sp, Land, RowBreak, Grp(),
            Multiply(scattering, positive), Sp, Eq, Sp, sharp, Dot));
    }

    private static Formula PositiveWitnessFormula()
    {
        Formula half = Fraction(D(1), D(2));
        Formula zero = D(0);
        Formula positive = Call("shiftedXiObservation", half, zero);
        Formula sharp = Call("shiftedXiObservationSharp", half, zero);
        Formula scattering = Call("shiftedXiScattering", half, zero);
        Formula negative = Call(
            "xiReading",
            Subtract(Subtract(half, half), Multiply(F.Id("i"), zero)));

        return Disp(Seq(
            D(0), Sp, Lt, Sp, half, Sp, Land, RowBreak, Grp(),
            positive, Sp, Neq, Sp, D(0), Sp, Land, RowBreak, Grp(),
            sharp, Sp, Eq, Sp, negative, Sp, Land, RowBreak, Grp(),
            scattering, Sp, Eq, Sp, Fraction(sharp, positive), Sp, Land, RowBreak, Grp(),
            Multiply(scattering, positive), Sp, Eq, Sp, sharp, Dot));
    }

    private static Formula ZeroDenominatorFormula()
    {
        Formula numerator = F.Id("numerator");
        Formula denominator = F.Id("denominator");
        return Disp(Seq(
            numerator, Sp, Colon, Eq, Sp, D(1), Comma, Sp,
            denominator, Sp, Colon, Eq, Sp, D(0), Comma, RowBreak, Grp(),
            denominator, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Multiply(Fraction(numerator, denominator), denominator),
            Sp, Neq, Sp, numerator, Dot));
    }

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
}
