using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class OriginalActualSpectralEndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The genuine spectral endpoint closes the original J identity", H("The genuine spectral endpoint closes the original J identity"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-actual-spectral-triple-integrable"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.triple_integrable"),
                H("Absolute Fourier Fubini"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex integrand on frequency times the spatial square is absolutely integrable for each measurable L1 function A. Its norm is exactly weight(w)*norm(A(u))*norm(A(v)), with weight(w)=1/(1+4*w^2). The proof uses the integrable product majorant. Forward and conjugate Fourier factors are L1, so their product expansion uses genuine product integration."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-spectral-complex-resolvent-identity"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.complex_resolvent_identity"),
                H("The normalized angular resolvent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fubini interchanges frequency and the two spatial variables. OriginalAngularResolvent.angular_resolvent supplies the exact normalized inverse transform exp(-abs(s)/2)/4. The Fourier transform and its modulus square remain the literal integral expressions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-spectral-actual-spectral-square"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_spectral_square"),
                H("The literal spectral convolution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the original finite atoms and every real t, S(t) equals one quarter of the double integral over [0,D]^2 of Re(conj(A(v))*A(u))*exp(-abs(t+u-v)/2). Taking real parts and swapping u,v supplies this sign of the lag. No evenness of rho is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-spectral-actual-spectral-endpoint"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_spectral_endpoint"),
                H("The actual endpoint factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed-window moments are Iplus=integral exp(u/2)*A(u) and Iminus=integral exp(-u/2)*A(u), and Z=Re(conj(Iplus)*Iminus). Since D+u-v>=0 on the square, the endpoint kernel separates and S(D)=exp(-D/2)*Z/4. The hypotheses allow D=0 and an empty atom type."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-spectral-original-test-endpoint"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.original_test_endpoint"),
                H("The original test endpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The test is literally f=c-S for the original prefix and actual Fourier density. The correlation endpoint theorem gives c(D)=0; the actual spectral endpoint therefore gives f(D)=-exp(-D/2)*Z/4. No endpoint hypothesis is supplied by the caller."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-spectral-original-test-ac"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.original_test_ac"),
                H("Absolute continuity of the actual test"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite-measure proof instantiates the spectralS_ac theorem. Combining it with c_ac proves absolute continuity of f on [0,D], including the zero-length interval."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-spectral-actual-fullr-eq-original-j"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint.actual_fullR_eq_original_J"),
                H("The complete original J identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite atom type, arbitrary complex coefficients with zero total mass, D>=0 and nodes in [0,D], fullR(D,Z,f)=-2*EulerGamma*f(0)-J(D,f,deriv(f)). Absolute continuity supplies the actual a.e. derivative, and original_test_endpoint discharges the endpoint in OriginalSignedJ.fullR_eq_original_J. The independently defined J, the inclusive prime-power cutoff and all degeneracies are retained. Global positivity of the original K and the sublinear N(D)=o(D) estimate remain open."))),
                DescribeRole.Theorem))));
}
