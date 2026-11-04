using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelEndpointSpectralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unit spectral branch controls transfer powers below the exact determinant-order depth.",
        H("A strict depth bound for the transfer remainder"),
        Blocks(Describe.Lean(
            DescribeId.Create("metallic-hankel-transfer-spectral-remainder"),
            DeclarationHandle.Create("D5/S3/Combinatorics/MetallicHankel/MetallicHankelEndpointSpectral.transfer_spectral_remainder"),
            H("One fixed unit branch for every admissible block and depth"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel")),
            Blocks(
                Paragraph(Text("Let U be a two-by-two matrix over rational formal power series. Suppose its trace has constant coefficient one and its determinant is q^D for a positive integer D. There are a fixed power series a with a(0)=1 and a fixed matrix E such that the coefficient of degree h in every entry of U^K equals that in a^K E whenever h<D*K. The same a and E work for every natural K and every admissible depth. The condition is evaluated at the actual K.")),
                Paragraph(Text("Hensel lifting gives the characteristic root a with constant coefficient one. Its inverse defines b=q^D/a, and the characteristic equation gives trace(U)=a+b. The difference a-b is a unit. Define E=(U-bI)/(a-b) and F=I-E. The existing two-by-two Cayley-Hamilton power recurrence gives U^K=a^K E+b^K F by induction, including powers zero and one. Since b^K=q^(D*K)/a^K, the second summand has zero coefficients at every degree below D*K.")),
                Paragraph(Text("For the ordinary denominator block in the metallic construction, D=2*rho gives exactly h<2*K*rho. MetallicHankelBlocks.ordinary_blocks supplies this trace constant coefficient and determinant for the actual continuants. MetallicHankelEndpointJets combines the branch with polynomial unit-power coefficients, and MetallicHankelResiduePolynomials consumes those jets in the exact complementary boundary. The theorem does not replace them by eventual equality."))),
            DescribeRole.Theorem)), []));
}
