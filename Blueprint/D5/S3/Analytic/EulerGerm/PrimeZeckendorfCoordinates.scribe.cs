using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class PrimeZeckendorfCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/EulerGerm/PrimeZeckendorfCoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime-local coordinate paired with a canonical Zeckendorf address is a faithful address for one golden Euler layer.",
        H("Prime-Zeckendorf Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-zeckendorf-readout-injective"),
                DeclarationHandle.Create(Prefix + "prime_zeckendorf_readout_injective"),
                H("Prime plus Zeckendorf depth is faithful"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Injective")),
                    Open, Operatorname, Grp(F.Id("primeZeckendorfReadout")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The prime coordinate is retained and the layer coordinate is replaced by the canonical Zeckendorf equivalence, so the joint address loses no information.")),
                    Paragraph(Text(
                        "This theorem establishes faithfulness of an already supplied arithmetic product coordinate. It does not derive prime labels from geometric projection data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-local-factor-is-zeckendorf-layer-sum"),
                DeclarationHandle.Create(Prefix + "germLocalFactor_eq_prime_zeckendorf_sum"),
                H("A fixed prime-local factor sums Zeckendorf-addressed layers"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("germLocalFactor")),
                    Open, F.Id("s"), Comma, Sp, F.Id("p"), Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("tsum")),
                    Open, F.Id("v"), Comma, Sp,
                    Operatorname, Grp(F.Id("primeZeckendorfWeight")),
                    Open, F.Id("s"), Comma, Sp,
                    Open, F.Id("p"), Comma, Sp,
                    Operatorname, Grp(F.Id("wEncoding")), Open, F.Id("v"), Close,
                    Close, Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For one fixed prime channel, the frozen golden local factor is exactly the sum over all natural layers after replacing each layer by its canonical Zeckendorf address.")),
                    Paragraph(Text(
                        "The first excited layer retains the common phi-squared exponent used by the existing golden-germ zeta factorization."))),
                DescribeRole.Theorem))));
}
