using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class CopyProfilePolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The copy profile bridge is stated explicitly and its tail consequence is compiled conditionally.",
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
                Blocks(Paragraph(Text("For every positive temporal-free copy term and balanced input, diagonal evaluation on independently replicated leaves is an integer polynomial in the replication count. Its degree is bounded by the number of input occurrences, its constant coefficient is q(N(0)), and its linear coefficient is the sum of one-hole slice values minus the full constant correction r·q(N(0)). This is the explicit open bridge; the module does not assert it as proved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("region-linear"), DeclarationHandle.Create(Prefix + "CopiesRegionLinear"),
                H("Region readout under copies"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second explicit open law records the expected integer linearity of every region readout under tagged parallel copies."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("word-readout"), DeclarationHandle.Create(Prefix + "wordReadout"),
                H("Scalar readout of a native word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("wordReadout extracts q from a successful native one-hole word and returns the neutral integer on failure."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("slice-law"), DeclarationHandle.Create(Prefix + "CopySliceReadoutLaw"),
                H("Finite one-hole slice family"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CopySliceReadoutLaw is the exact finite normalization consequence needed after the polynomial bridge: every total copy expression supplies a finite family of total one-hole words whose readouts sum to the target region."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("saturation-law"), DeclarationHandle.Create(Prefix + "CopySaturationLaw"),
                H("Joint saturation for finite word families"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CopySaturationLaw records the common low-time indistinguishability construction for any finite family of total one-hole words."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("copy-expressible"), DeclarationHandle.Create(Prefix + "CopyQExpressible"),
                H("Positive finite diagonal copy expression"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A region is copy-expressible when some positive finite copy term is total on every balanced input and its diagonal q readout equals the region readout."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polynomial-identification"), DeclarationHandle.Create(Prefix + "polynomial_identification"),
                H("Identification from natural evaluations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An integer polynomial whose values at all natural numbers are n times a fixed integer is X multiplied by the constant polynomial a."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-to-tail"), DeclarationHandle.Create(Prefix + "sum_word_readouts_implies_tail"),
                H("Finite word sums force a uniform tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under joint saturation, a finite sum of total one-hole word readouts cannot distinguish sufficiently early times at one position; equality of the sum and the selected-region calculation therefore forces Tail."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("copy-to-tail"), DeclarationHandle.Create(Prefix + "copy_q_expressible_implies_tail"),
                H("Conditional copy necessity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Copy expressibility implies Tail once the finite slice-readout and joint-saturation laws are supplied."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tail-to-copy"), DeclarationHandle.Create(Prefix + "tail_implies_copy_q_expressible"),
                H("Tail supplies a one-copy expression"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing one-hole tail construction embeds as a positive one-occurrence copy term."))), DescribeRole.Theorem)
        ),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization"))
        ]));
}
