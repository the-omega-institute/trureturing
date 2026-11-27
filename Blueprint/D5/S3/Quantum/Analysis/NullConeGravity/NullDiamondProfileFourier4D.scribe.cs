using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondProfileFourier4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact cone profiles and their modular frequency representation.",
        H("Profiles and radial Fourier weights"),
        Blocks(
            Entry("separated-profile", "ConeProfileTerm", "Separated cone profile",
                "A smooth complex radial function has compact support inside the affine interval (0,1). A complex Lipschitz function on the round sphere supplies its angular dependence.", DescribeRole.Definition),
            Entry("finite-profile", "ConeProfile", "Finite cone profile",
                "A profile is a finite list of separated terms. Its value is the sum of their products.", DescribeRole.Definition),
            Entry("affine-value", "profileValue", "Affine profile value",
                "Evaluate the radial and angular factors at their respective coordinates and sum their products.", DescribeRole.Definition),
            Entry("affine-derivative", "profileDeriv", "Affine radial derivative",
                "Differentiate each radial factor and multiply by its angular factor before summing.", DescribeRole.Definition),
            Entry("affine-radius", "affineRadius", "Affine radius",
                "The radius is the real sigmoid of 2π times the modular coordinate.", DescribeRole.Definition),
            Entry("weighted-embedding", "profileEmbed", "Weighted Fourier representation",
                "Take the angular-frequency Fourier transform in the modular radial coordinate with unitary normalization, multiply by the square root of the frequency weight, and form a complex L² class on the product phase space.", DescribeRole.Definition),
            Entry("coth-series", "profile_log_series_symbol", "Coth series and signed symbol",
                "The symmetric series has constant term 2 and summands with denominator (2π(k+1))² plus the frequency squared. After subtracting the frequency, the series equals the product of the frequency weight and the massless multiplier."),
            Entry("log-tail-transform", "profile_log_fourier_symbol", "Logarithmic Fourier symbol",
                "Integrate the exponential tail of the real hyperbolic logarithm in the angular Fourier convention. The rational transform, multiplied by the frequency squared divided by π and combined with the linear-distance and sign coefficients, yields the massless symbol."),
            Entry("dense-embedding", "profileEmbed_dense", "Density in phase space",
                "Translated and dilated compact radial tests separate the weighted Fourier pairing. A countable dense subset of the angular Lipschitz tests separates almost every angular slice. The resulting orthogonal complement is zero."),
            Entry("fourier-profile", "profileFourier", "Unweighted Fourier profile",
                "Sum the unitary angular-frequency transforms of the modular radial factors multiplied by their angular factors.", DescribeRole.Definition),
            Entry("massless-pairing", "profile_nullA_pairing", "Massless spectral pairing",
                "The pairing with the existing massless multiplier is the integral of the squared modulus of the unweighted Fourier profile against the frequency weight minus the frequency."),
            Entry("modular-profile", "modularProfile", "Modular radial slice",
                "Evaluate the affine profile at the logistic radius for a fixed angular direction, as a compactly supported Schwartz function.", DescribeRole.Definition),
            Entry("modular-logarithm", "profile_modular_log_pairing", "Modular logarithmic pairing",
                "Integrate the radial logarithmic form of each modular slice over the sphere. The linear distance, the decaying logarithmic tail, and the oriented imaginary term combine to give the quadratic form of the massless multiplier."),
            Entry("correction-pairing", "profile_nullT_pairing", "Massive Fourier pairing",
                "The square root in each weighted embedding cancels the corresponding denominator of the correction kernel. The resulting integral pairs the unweighted Fourier profiles against the mixed Fourier transform of the correction."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}

