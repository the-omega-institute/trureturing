using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation.OriginalReturnSectors;

internal sealed class ContactsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalReturnSectors/Contacts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole-return compactness and stable source contacts in the original cone.",
        H("Original return contact geometry"), Blocks(
        Describe.Lean(DescribeId.Create("leakage"), DeclarationHandle.Create(Owner + "leakage"),
            H("Entire return leakage"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("alpha_F(t) is the supremum of dist(x,F) over every x in D(t). Compactness makes it an attained maximum. The same auxiliary norm is used throughout. No selected subset of a return face is substituted."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("base-maximum"), DeclarationHandle.Create(Owner + "baseMaximum"),
            H("Actual original maximum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("M(b) is the supremum of b on the entire original K. For every nonzero original positive annihilator of an actual pure label, M(b)>0 and one fixed A>0 gives norm(b)<=A M(b). CommonSourceLiftObstruction.original_dual_bound supplies the original dual estimate for every signed functional, and its positive_base_norm identifies the whole-K state norm with M(b) for positive b. The original positive_annihilator_maximum gives strict positivity. M(b) has no imposed upper budget."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("sector-violation"), DeclarationHandle.Create(Owner + "sectorViolation"),
            H("Additional common-sector condition"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every one of the fixed dim(a)+1 source sectors has a nonzero original normal b, nonnegative on all of C and vanishing at the same actual t, with nonzero actual source slope, direction within theta of that sector, and norm(g_b)>H M(b) alpha_F(t). This is Q133.14 at one index. Its eventual sequence version is an extra antecedent and is not derived from exclusion balls, positive lifts or local pure-limit density. Normalized contrast is allowed to tend to zero."))), DescribeRole.Definition),
        Paragraph(Text("The source uses the entire original finite real cone, normalized base, pure locus and effect interval. Its compactness argument includes mixed limit labels and repeated exclusion fibers. Sphere contacts include positive dimension one and the chart center. Positive barycentric reconstruction is stable both for a fixed source affine space and for one common affine space of bounded dimension. The whole_return_leakage, source_contact_simplex and uniform_return_sectors conclusions consume these ingredients through the original module. These are conditional mathematical results without a physical-realization claim.")))));
}
