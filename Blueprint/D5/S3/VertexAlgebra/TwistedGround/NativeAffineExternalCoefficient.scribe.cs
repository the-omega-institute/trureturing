using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class NativeAffineExternalCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeAffineExternalCoefficient", H("Ordinary external coefficients of affine Gaussians"), Blocks(
            Paragraph(Text("Finite ordinary coordinate differentiation identifies every full row occupation with its native affineCoefficient. The cutoff for the finite exponential polynomial bounds the whole occupation degree. Cauchy estimates justify every fixed finite external derivative of a normally bounded family on a positive external neighborhood. The parameterized normal estimate is uniform only over the specified family; it makes no claim of a source radius uniform across frequency cutoffs. All external index types and occupations may be empty. The calculus is classical, with no novelty or physical-realization claim.")),
            N("coordinateDerivative", "Ordinary coordinate derivative", "The derivative varies exactly one coordinate through Function.update.", DescribeRole.Definition),
            N("coordinateJet", "Finite ordered coordinate derivatives", "The empty derivative word evaluates the original function.", DescribeRole.Definition),
            N("jetOccupation", "Occupation of a derivative word", "Coordinate multiplicities record the complete finite derivative degree.", DescribeRole.Definition),
            N("externalCoefficient", "Ordinary multivariate coefficient", "The ordinary finite coordinate jet at zero is divided by the full product of coordinate factorials.", DescribeRole.Definition),
            N("externalPairCoefficient", "Two external row extractions", "The left and right external occupations are extracted consecutively, with both complete factorial denominators.", DescribeRole.Definition),
            N("external_jet_expCut", "Finite exponential jet comparison", "Vanishing of sufficiently high powers at zero proves the exact finite exponential polynomial comparison, with a genuine differentiated recurrence.", DescribeRole.Theorem),
            N("native_affine_external_jet", "Native affine row from an ordinary jet", "The full derivative occupation is used in the finite native Taylor comparison.", DescribeRole.Theorem),
            N("native_affine_external_coefficient", "Full ordinary affine coefficient", "Every full external occupation, including zero, equals the native affine coefficient. No equality of replacement source arrays is assumed.", DescribeRole.Theorem),
            N("coordinateJet_const_mul", "Constant factors through finite jets", "Constants remain literal through every finite ordinary derivative.", DescribeRole.Theorem),
            N("coordinateJet_append", "Composition of finite jets", "Concatenation applies the two finite derivative words in their specified order.", DescribeRole.Theorem),
            N("native_mixed_external_coefficient", "Full mixed row extraction", "Internal native extraction followed by external ordinary extraction gives the native coefficient at the sum of the two full occupations.", DescribeRole.Theorem),
            N("coordinateJet_congrOn", "Local equality preserves finite jets", "Equality on an open neighborhood preserves all finite ordinary coordinate derivatives.", DescribeRole.Theorem),
            N("coordinateJet_tsum_normal", "Normal finite derivative interchange", "Cauchy bounds and normally summable derivative families justify the finite derivative interchange on a smaller positive neighborhood.", DescribeRole.Theorem),
            N("externalCoefficient_tsum", "Ordinary coefficient interchange", "The normal interchange retains the complete external factorial denominator.", DescribeRole.Theorem),
            N("externalPair_affine", "Collected exponential extraction", "Two external ordinary extractions give the full native affine coefficient of the actual symmetric collected kernel and mean.", DescribeRole.Theorem),
            N("externalPair_normal_family", "Parameterized normal external extraction", "A summable bound uniform over an arbitrary parameter family survives both fixed external extractions. The proof uses actual derivatives and Cauchy estimates.", DescribeRole.Theorem),
            N("externalPair_congr_ball", "External germ equality", "Equality throughout a positive external norm ball preserves the two fixed ordinary coefficient extractions.", DescribeRole.Theorem),
            N("externalPair_mixed", "Full mixed occupation extraction", "The actual left and right mixed affine factors give the two full native rows, multiplied by exactly one internal factorial.", DescribeRole.Theorem),
            N("mixed_external_contDiff", "Entire external occupation summands", "Each actual mixed occupation factor is entire in the external coordinates because its native affine coefficient has finite polynomial dependence on the means.", DescribeRole.Theorem)), []));

    private static DocumentBlock N(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("native-external-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
