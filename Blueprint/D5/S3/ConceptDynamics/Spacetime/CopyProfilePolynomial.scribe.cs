using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class CopyProfilePolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native multilinear time profiles yield the complete copy polynomial and the finite slice argument for tail regions.",
        H("Copy Profiles and Polynomial Readouts"),
        Blocks(
            Describe.Lean(DescribeId.Create("copies"), DeclarationHandle.Create(Prefix + "copies"),
                H("Tagged parallel copies"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("copies 0 is the empty balanced history and copies (n+1) appends one tagged parallel copy of the input."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("value"), DeclarationHandle.Create(Prefix + "value"),
                H("Independent copy evaluation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("value is the total native value of a copy term under an independent leaf assignment, with the empty history as the failure default."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polynomial-law"), DeclarationHandle.Create(Prefix + "CopyPolynomialLaw"),
                H("The 5B/5C polynomial bridge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive temporal-free copy term and balanced input, diagonal evaluation on independently replicated leaves is an integer polynomial in the replication count. Its degree is bounded by the number of input occurrences, its constant coefficient is q(N(0)), and its linear coefficient is the sum of one-hole slice values minus the full constant correction r·q(N(0)). The theorem copy_polynomial_law proves this statement from the actual native time profile."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("profile-coefficients"), DeclarationHandle.Create(Prefix + "profileCoefficients"),
                H("Squarefree profile coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A coefficient is the multilinear profile model evaluated with the input profile on the indicated set of leaf occurrences and the empty profile elsewhere."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("profile-multiaffine"), DeclarationHandle.Create(Prefix + "profile_multiaffine"),
                H("Native independent-copy expansion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every temporal-free copy term, balanced input and independently chosen natural replication counts, the actual native profile is the sum over sets of distinct leaf occurrences, weighted by the product of their counts. The proof consumes model_eval and the primitive profile updates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proved-polynomial"), DeclarationHandle.Create(Prefix + "copy_polynomial_law"),
                H("Lemma 5B and the full 5C coefficient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual charge of a temporal-free term on m copies at every leaf is an integer polynomial of degree at most the arity. The constant coefficient is q(N(0)); the linear coefficient is the sum of the one-leaf slice charges minus r times q(N(0)). No vanishing constant is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("region-linear"), DeclarationHandle.Create(Prefix + "CopiesRegionLinear"),
                H("Region readout under copies"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This predicate specifies integer linearity of every region readout under tagged parallel copies; copies_region_linear proves it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("word-readout"), DeclarationHandle.Create(Prefix + "wordReadout"),
                H("Scalar readout of a native word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("wordReadout extracts q from a successful native one-hole word and returns the neutral integer on failure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slice-law"), DeclarationHandle.Create(Prefix + "CopySliceReadoutLaw"),
                H("Finite one-hole slice family"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CopySliceReadoutLaw is the exact finite normalization consequence needed after the polynomial bridge: every total copy expression representing the fixed region supplies a finite family of total one-hole words whose readouts sum to that region."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("saturation-law"), DeclarationHandle.Create(Prefix + "CopySaturationLaw"),
                H("Joint saturation for finite word families"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CopySaturationLaw records the common indistinguishability construction below a nonpositive time threshold for any finite family of total one-hole words."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("copy-expressible"), DeclarationHandle.Create(Prefix + "CopyQExpressible"),
                H("Positive finite diagonal copy expression"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A region is copy-expressible when some positive finite copy term is total on every balanced input and its diagonal q readout equals the region readout."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polynomial-identification"), DeclarationHandle.Create(Prefix + "polynomial_identification"),
                H("Identification from natural evaluations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An integer polynomial whose values at all natural numbers are n times a fixed integer is X multiplied by the constant polynomial a."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proved-region-linearity"), DeclarationHandle.Create(Prefix + "copies_region_linear"),
                H("Exact regional replication law"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every fixed region readout on n tagged parallel copies equals n times its value on the original balanced input."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proved-saturation"), DeclarationHandle.Create(Prefix + "copy_saturation_law"),
                H("Lemma 6 for a common finite family"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any finite family of total one-hole words admits a common nonpositive threshold and, at every position and every pair of times below it, a pair of inputs with equal readouts for every word. The proof reuses the existing finite predicate construction and its saturation theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("proved-slice"), DeclarationHandle.Create(Prefix + "copy_slice_readout_law"),
                H("Polynomial identification recovers the slices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Normalize the total copy term before choosing the input. Identify its polynomial from all natural replication counts using regional linearity, obtain zero constant coefficient, and use the full linear coefficient to recover the exact sum of the fixed one-hole slices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-to-tail"), DeclarationHandle.Create(Prefix + "sum_word_readouts_implies_tail"),
                H("Finite word sums force a uniform tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proved joint saturation shows that a finite sum of total one-hole word readouts cannot distinguish sufficiently early times at one position; equality of the sum and the selected-region calculation therefore forces Tail."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("copy-to-tail"), DeclarationHandle.Create(Prefix + "copy_q_expressible_implies_tail"),
                H("Copy necessity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Copy expressibility implies Tail by the proved polynomial, slice-readout and finite joint-saturation results, without additional law assumptions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tail-to-copy"), DeclarationHandle.Create(Prefix + "tail_implies_copy_q_expressible"),
                H("Tail supplies a one-copy expression"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing one-hole tail construction embeds as a positive one-occurrence copy term."))), DescribeRole.Theorem)
        ),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile"))
        ]));
}
