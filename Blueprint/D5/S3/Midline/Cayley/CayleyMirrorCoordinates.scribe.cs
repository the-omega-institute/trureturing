using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class CayleyMirrorCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Midline/Cayley/CayleyMirrorCoordinates.cayley_mirror_coordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugate reflection reverses the Cayley radius while preserving its phase.",
        H("Cayley Mirror Coordinates"),
        Blocks(Describe.Lean(
            DescribeId.Create("cayley-mirror-coordinates"),
            DeclarationHandle.Create(Handle),
            H("The mirror reverses radial drift and preserves phase"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a complex point s, c(s) is the imported Cayley coefficient "
                        + "(s - 1)/s, mirror(s) is one minus the conjugate of s, and "
                        + "beta(s) is the imported logarithm of the coefficient norm.")),
                Paragraph(Text(
                    "The first public conjunct is the exact complex coefficient identity. "
                        + "Taking norms and logarithms gives the second conjunct, so the "
                        + "radial gain-loss direction is reversed.")),
                Paragraph(Text(
                    "The final conjunct casts both principal arguments to Real.Angle. "
                        + "Equality there is equality modulo two pi, including the negative "
                        + "real-axis branch endpoint, and states that the phase is preserved.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies the argument laws for inversion and complex "
                        + "conjugation; the coefficient identity itself follows from the two "
                        + "imported coordinate definitions."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula s = F.Id("s");
        Formula mirrorS = Call("mirror", s);
        Formula coefficient = Call("c", s);
        Formula mirroredCoefficient = Call("c", mirrorS);
        Formula conjugateCoefficient = Seq(Overline, Grp(coefficient));
        Formula coefficientIdentity = Equal(
            mirroredCoefficient,
            new Formula.Fraction(D(1), conjugateCoefficient));
        Formula radialReversal = Equal(
            Apply(Beta, mirrorS),
            new Formula.Negate(Apply(Beta, s)));
        Formula phasePreservation = Equal(
            Call("AngleClass", Call("arg", mirroredCoefficient)),
            Call("AngleClass", Call("arg", coefficient)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, s, Colon, Sp, complex, Comma,
            RowBreak, Grp(),
            coefficientIdentity, Sp, Land,
            RowBreak, Grp(),
            radialReversal, Sp, Land,
            RowBreak, Grp(),
            phasePreservation, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
