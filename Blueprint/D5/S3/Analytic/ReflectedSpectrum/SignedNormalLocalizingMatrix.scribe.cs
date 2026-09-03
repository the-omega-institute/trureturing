using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ReflectedSpectrum;

internal sealed class SignedNormalLocalizingMatrixDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/ReflectedSpectrum/SignedNormalLocalizingMatrix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive-mass signed-normal atom has a positive ordinary "
            + "Hankel matrix and a negative shifted localizing witness "
            + "exactly off the reflection boundary.",
        H("Signed-Normal Localizing Matrix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-normal-location"),
                DeclarationHandle.Create(Prefix + "signedNormalLocation"),
                H("Signed-normal support coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The support coordinate reuses the frozen reflected-pair signed determinant. It is the negative square of the reflected split."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-normal-moment"),
                DeclarationHandle.Create(Prefix + "signedNormalAtomMoment"),
                H("Single-atom signed-normal moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A real mass and signed support coordinate determine the scalar moment sequence used by the ordinary and shifted Hankel matrices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordinary-hankel-matrix"),
                DeclarationHandle.Create(Prefix + "signedNormalHankelMatrix"),
                H("Ordinary positive-mass Hankel matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordinary Hankel truncation is stored as a nonnegative scalar multiple of a rank-one outer product."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shifted-localizing-matrix"),
                DeclarationHandle.Create(Prefix + "signedNormalLocalizingMatrix"),
                H("Shifted support-localizing matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first shifted matrix multiplies the same rank-one Gram factor by the signed support coordinate. This separates support location from mass positivity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hankel-localizing-certificate"),
                DeclarationHandle.Create(
                    Prefix + "signed_normal_atom_hankel_localizing_certificate"),
                H("Positive Hankel with negative localizing witness"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The signed-normal support coordinate is the negated square of the reflection offset, so it is strictly negative exactly off the reflection boundary; nonnegative mass makes every ordinary Hankel truncation positive semidefinite.")),
                    Paragraph(Text(
                        "The unit-coordinate readout of the shifted localizing matrix is the mass times the support coordinate, so a positive-mass off-boundary atom simultaneously carries positive ordinary Hankel truncations and a finite negative support-localizing certificate — the two-sided witness separating boundary from off-boundary support."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare")),
        ]));

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

    private static Formula CertificateFormula() => Disp(Seq(
        Call("PosSemidef", Call("hankel", F.Id("m"), DeltaLower)),
        Sp, Land, Sp,
        Call("hermForm",
            Call("localizing", F.Id("m"), DeltaLower), Call("e")),
        Sp, Lt, Sp, D(0)));
}
