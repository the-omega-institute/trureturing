using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class FiniteScatteringCascadeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Scattering/FiniteScatteringCascade.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-integer shifted-xi scattering is a finite cascade of modular completed-zeta quotients.",
        H("Finite Scattering Cascade"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shifted-xi-scattering-reading"),
                DeclarationHandle.Create(Prefix + "shiftedXiScattering"),
                H("Shifted-xi scattering reading"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reading is constructed from the frozen entire xi function by taking "
                        + "the quotient at the two opposite shifts around one half."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("modular-scattering-coefficient"),
                DeclarationHandle.Create(Prefix + "modularScatteringCoefficient"),
                H("Modular scattering coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient is the consecutive quotient of the frozen classical "
                        + "completed-zeta reading at twice the supplied parameter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("half-integer-shifted-xi-finite-scattering-cascade"),
                DeclarationHandle.Create(Prefix + "finite_scattering_cascade"),
                H("Half-integer shifted-xi scattering is a finite cascade"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural cascade length N, set the shift to N/2, set s_z "
                            + "to one half minus i times z, and set a to s_z minus N/2. "
                            + "The left denominator s_z plus N/2 is therefore the right endpoint "
                            + "a plus N used by the finite cascade.")),
                    Paragraph(Text(
                        "Both sides are converted to Mathlib's canonical meromorphic normal "
                            + "form on the complex plane. This states the unconditional "
                            + "meromorphic identity, including canonical pole values, rather "
                            + "than weakening it with pointwise nonvanishing hypotheses.")),
                    Paragraph(Text(
                        "The proof establishes the telescoping quotient on a nonempty open "
                            + "right half-plane, where completed zeta is nonzero, and then applies "
                            + "the frozen uniqueness theorem for meromorphic normal forms."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("N");
        Formula z = F.Id("z");
        Formula j = F.Id("j");
        Formula sz = Seq(F.Id("s"), Underscore, Grp(F.Id("z")), Open, z, Close);
        Formula a = Call("a", z);
        Formula halfN = Fraction(n, D(2));
        Formula leftReading = Fraction(
            Call("xiReading", Subtract(sz, halfN)),
            Call("xiReading", Add(sz, halfN)));
        Formula coefficient = Call(
            "modularScatteringCoefficient",
            Fraction(Add(Add(a, j), D(1)), D(2)));
        Formula cascade = Multiply(
            Fraction(
                Multiply(a, Subtract(a, D(1))),
                Multiply(Add(a, n), Subtract(Add(a, n), D(1)))),
            Seq(
                Prod, Underscore,
                Grp(D(0), Sp, Leq, Sp, j, Sp, Lt, Sp, n),
                Sp, coefficient));
        Formula leftNormalForm = Call(
            "toMeromorphicNFOn",
            Lambda(z, leftReading),
            ComplexNumbers());
        Formula rightNormalForm = Call(
            "toMeromorphicNFOn",
            Lambda(z, cascade),
            ComplexNumbers());

        return Disp(Seq(
            Begin, Grp(F.Id("aligned")),
            Forall, Sp, n, InMacro, Sp, NaturalNumbers(), Comma, RowBreak, Grp(),
            leftNormalForm, Sp, Eq, Sp, rightNormalForm, Comma, RowBreak, Grp(),
            F.Text, Grp(F.Id("where")), Quad, Sp,
            sz, Sp, Colon, Eq, Sp,
            Subtract(Fraction(D(1), D(2)), Multiply(F.Id("i"), z)), Comma, RowBreak, Grp(),
            a, Sp, Colon, Eq, Sp, Subtract(sz, halfN), Dot,
            End, Grp(F.Id("aligned"))));
    }

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula ComplexNumbers() =>
        Seq(Mathbb, Grp(F.Id("C")));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

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
}
