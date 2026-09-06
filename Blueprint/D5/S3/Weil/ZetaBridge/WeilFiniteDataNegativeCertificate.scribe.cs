using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilFiniteDataNegativeCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/WeilFiniteDataNegativeCertificate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual multi-orbit negative Weil certificates with the infinite scalar tail discharged analytically and all remaining budgets finite.",
        H("Finite-Data Negative Weil Certificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weil-finite-data-rationalComputedWeilBudget"),
                DeclarationHandle.Create(Prefix + "rationalComputedWeilBudget"),
                H("Fully specified rational error coefficient"),
                StatementSource.FromAuthor(Disp(F.Id("C(J0,J2,T)=(sum_i (3*(J0_i+J2_i))^2)*rationalFourthMomentTail(T)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuse the existing Cauchy coefficient and the newly proved rational tail. T>=5 and finite cutoff containment are certified in the soundness theorem; the function itself does not search for zeta zeros."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weil-finite-data-computed-packet-full-gram-margin"),
                DeclarationHandle.Create(Prefix + "computed_packet_full_gram_margin"),
                H("Actual Gram certificate without a supplied infinite tail"),
                StatementSource.FromAuthor(Disp(F.Id("Given an actual packet, T>=5, spectral-ball containment, actual finite two-jet enclosures, and C<=c/den, every depth N>=rationalQuarterDepth(c,den,p,q) has Re(a*G_N*a)<=-(4-p/q)*E(a)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The new analytic theorem proves both summability and the scalar tail bound. The existing all-cross-term Cauchy estimate and exact integer depth theorem are then applied to the actual full Weil Gram. No arbitrary matrix replaces the zeta form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weil-finite-data-finite-data-sparse-negative-certificate"),
                DeclarationHandle.Create(Prefix + "finite_data_sparse_negative_certificate"),
                H("Construct the whole negative family from finite geometry"),
                StatementSource.FromAuthor(Disp(F.Id("For a valid frame with certified target radii and target-target/target-exception squared gaps, T>=5, T+1<=the explicit peak cutoff, p<4q and the finite budget bound, construct an actual packet. Every computed admissible depth has PosDef(-G_N), negIndex(G_N)=card(frame), common support radius (N+2)/(4(R+1)), and uniform negative margin 4-p/q."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuse sparse_packet_computed_support_margin_and_inertia, but discharge both of its infinite spectral premises using the actual rational count-to-tail theorem. The peak, killers and their finite jets are constructed by the existing sparse owner. Finite nodal data and actual frame validity remain inputs; no off-line zero is asserted to exist. The cutoff is never enlarged after constructing the packet. This closes an analytic certificate component, not arithmetic positivity, growing-scale Xi convergence or RH."))),
                DescribeRole.Theorem)), []));
}
