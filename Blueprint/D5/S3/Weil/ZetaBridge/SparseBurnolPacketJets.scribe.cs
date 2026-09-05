using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class SparseBurnolPacketJetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/SparseBurnolPacketJets.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative bounds for actual multi-orbit Weil tests, with explicit finite geometry and scalar spectral-tail premises.",
        H("SparseBurnolPacketJets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sparseburnolpacketjets-sparsePacketExceptions"),
                DeclarationHandle.Create(Prefix + "sparsePacketExceptions"),
                H("Actual exception-only indices"),
                StatementSource.FromAuthor(Disp(F.Id("E0=symmetricIndices(quantitativePeakRadius(d,R,sigma)) minus the actual target orbit union."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing quantitativePeakRadius is reused. The exceptional window is fixed after constructing the peak; it is independent of the later killer smoothing order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparseburnolpacketjets-exists-sparse-burnol-packet-with-jets"),
                DeclarationHandle.Create(Prefix + "exists_sparse_burnol_packet_with_jets"),
                H("Construct the actual packet from finite geometry"),
                StatementSource.FromAuthor(Disp(F.Id("Given a valid frame, target radius R>=0, target squared gap sigma>0 and target-exception gap tau>0, construct P with the specified exceptional set, peak and killer support h=1/(4(R+1)), and explicit peak and killer jets through order two."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing dense target theorem constructs the unit peak. Its two jet budgets imply the existing explicit cutoff. Apply SparseEvenInterpolationJets to each signed target assignment and to the actual exception-only indices. Repeated exception nodes are allowed. No supplied packet, bump derivative, peak tail or existence-of-threshold premise is used. The finite geometric inequalities still require certified data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparseburnolpacketjets-sparse-packet-computed-support-margin-and-inertia"),
                DeclarationHandle.Create(Prefix + "sparse_packet_computed_support_margin_and_inertia"),
                H("Computed support, full margin and exact inertia"),
                StatementSource.FromAuthor(Disp(F.Id("With the actual scalar fourth-moment tail bounded by Theta and the explicit Cauchy coefficient rounded above by c/den, construct P such that every N>=rationalQuarterDepth(c,den,p,q) has PosDef(-G_N), negIndex(G_N)=card(frame), support radius (N+2)/(4(R+1)), and Re(a*G_N a)<=-(4-p/q)E(a), provided den,p,q>0 and p<4q."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the packet constructor to discharge all support and jet premises of the direct Cauchy remainder theorem. The exact integer selector supplies the error budget at every later depth. Reuse the actual full Gram and its spectral inertia theorem. The positive scalar zero-tail estimate and its summability are explicit analytic premises; a literature citation is not substituted for their proofs. No off-line zero or RH is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparseburnolpacketjets-rationalSparsePacketCutoff"),
                DeclarationHandle.Create(Prefix + "rationalSparsePacketCutoff"),
                H("Rational cutoff evaluation"),
                StatementSource.FromAuthor(Disp(F.Id("U=R+6*(rationalInterpolationJetBudget(d,R,sigma,1,0)+rationalInterpolationJetBudget(d,R,sigma,1,2))+1."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This arithmetic uses only rational operations and natural powers. It evaluates the existing real cutoff rather than defining another analytic cutoff."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparseburnolpacketjets-rationalSparsePacketCutoff-cast"),
                DeclarationHandle.Create(Prefix + "rationalSparsePacketCutoff_cast"),
                H("Exact cutoff semantics"),
                StatementSource.FromAuthor(Disp(F.Id("The rational cutoff cast to the reals equals quantitativePeakRadius(d,R,sigma)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the existing rational interpolation-jet cast lemma; no numerical approximation or real logarithm enters."))),
                DescribeRole.Theorem)), []));
}
