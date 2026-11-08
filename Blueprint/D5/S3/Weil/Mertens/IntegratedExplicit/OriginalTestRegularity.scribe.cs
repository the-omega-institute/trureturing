using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class OriginalTestRegularityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regularity of the original correlation and spectral test", H("Regularity of the original correlation and spectral test"),
        Blocks(
            Paragraph(Text("The prefix correlation is reused from D5/S3/Analytic/Interpolation/AtomicPrefixEnergy. Absolute-continuity, Lipschitz and parametric-integral suppliers are imported from the pinned Apache-2.0 Mathlib. The uniform resolvent estimates and their assembly are repository derivations.")),
            Describe.Lean(DescribeId.Create("original-testregularity-c-eq-hinges"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_eq_hinges"),
                H("The actual finite-prefix correlation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite atom type, real nodes x and complex coefficients a of total mass zero, c(t)=Re(integral_u conj(prefix(u+t))*prefix(u)) equals -sum_{i,j} Re(conj(a_i)*a_j)*max(x_i-x_j-t,0). The existing AtomicPrefixEnergy.shifted_hinge_prefix_energy supplies the actual integral identity, including empty, repeated and cancelling atoms."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-testregularity-c-ac"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_ac"),
                H("Absolute continuity of correlation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each ramp max(b-t,0) is 1-Lipschitz and hence absolutely continuous. Finite linear combination proves absolute continuity of c on every finite interval, with no positivity or distinctness assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-testregularity-c-at-d"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.c_at_D"),
                H("The closed-window correlation endpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every node lies in [0,D], all ramps vanish at t=D. Thus c(D)=0, including the zero-length and empty cases."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-testregularity-spectrals-ac"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalTestRegularity.spectralS_ac"),
                H("Absolute continuity of the spectral resolvent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cosine-difference estimate gives a globally Lipschitz spectralS under a finite measure and hence absolute continuity on every finite interval. OriginalActualFourier proves finiteness for the literal Fourier density; OriginalActualSpectralEndpoint combines this with c_ac to obtain the actual test f=c-S and its a.e. derivative."))),
                DescribeRole.Theorem))));
}
