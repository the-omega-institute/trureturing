using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class EllipticHyperbolicReflectionTrichotomyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/EllipticHyperbolicReflectionTrichotomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-dimensional generators separate hyperbolic, neutral, and elliptic spectral "
            + "sectors by determinant sign.",
        H("Elliptic-Hyperbolic Reflection Trichotomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hyperbolic-generator-definition"),
                DeclarationHandle.Create(Prefix + "hyperbolicGenerator"),
                H("The reflected hyperbolic generator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The diagonal rates delta and minus delta generate reciprocal growth and "
                        + "decay. Their trace cancels, their determinant is negative, and the "
                        + "generator square is positive scalar expansion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("elliptic-generator-definition"),
                DeclarationHandle.Create(Prefix + "ellipticGenerator"),
                H("The elliptic rotation generator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The skew two-dimensional generator represents rotation at angular rate "
                        + "gamma. Its determinant is positive and its square is negative scalar "
                        + "curvature."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("neutral-generator-definition"),
                DeclarationHandle.Create(Prefix + "neutralGenerator"),
                H("The neutral unsplit generator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero generator is the boundary between the hyperbolic and elliptic "
                        + "sectors. Its trace, determinant, and square all vanish."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("determinant-reuse-bridge"),
                DeclarationHandle.Create(Prefix +
                    "hyperbolic_det_eq_reflection_pair_signed_determinant"),
                H("The matrix determinant is the frozen reflected signed determinant"),
                StatementSource.FromAuthor(BridgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The matrix chart introduces no second negative-square invariant. Its "
                        + "determinant is identified exactly with the signed determinant already "
                        + "frozen for the reflected growth pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sector-trichotomy"),
                DeclarationHandle.Create(Prefix +
                    "elliptic_hyperbolic_reflection_trichotomy"),
                H("Determinant sign separates the three finite sectors"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The hyperbolic generator has determinant minus delta squared and square "
                            + "plus delta squared times the identity. The elliptic generator has "
                            + "determinant plus gamma squared and square minus gamma squared "
                            + "times the identity.")),
                    Paragraph(Text(
                        "The neutral generator lies at determinant zero. This finite algebraic "
                            + "trichotomy supplies the local mode dictionary and does not assert "
                            + "that completed zeta has been realized by these matrices."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare")),
        ]));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Typed(Formula value) => Seq(value, Colon, Sp, Reals());

    private static Formula PowerTwo(Formula value) => Seq(value, Caret, Grp(D(2)));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula BridgeFormula()
    {
        Formula delta = F.Id("delta");
        return Disp(Seq(
            Forall, Sp, Typed(delta), Comma, Sp,
            Call("det", Call("hyperbolicGenerator", delta)), Sp, Eq, Sp,
            Call("reflectionPairSignedDeterminant", delta), Dot));
    }

    private static Formula MainFormula()
    {
        Formula delta = F.Id("delta");
        Formula gamma = F.Id("gamma");
        Formula hyperbolic = Call("hyperbolicGenerator", delta);
        Formula elliptic = Call("ellipticGenerator", gamma);
        Formula neutral = Call("neutralGenerator");
        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(delta), Comma, Sp, Typed(gamma), Comma, Sp,
                Call("trace", hyperbolic), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                Call("det", hyperbolic), Sp, Eq, Sp, Minus, PowerTwo(delta), Sp, Land),
            Seq(
                Call("square", hyperbolic), Sp, Eq, Sp,
                Call("scalarIdentity", PowerTwo(delta)), Sp, Land),
            Seq(
                Call("trace", neutral), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                Call("det", neutral), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                Call("square", neutral), Sp, Eq, Sp, D(0), Sp, Land),
            Seq(
                Call("trace", elliptic), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                Call("det", elliptic), Sp, Eq, Sp, PowerTwo(gamma), Sp, Land),
            Seq(
                Call("square", elliptic), Sp, Eq, Sp,
                Call("scalarIdentity", Seq(Minus, PowerTwo(gamma))), Dot),
        ]));
    }
}
