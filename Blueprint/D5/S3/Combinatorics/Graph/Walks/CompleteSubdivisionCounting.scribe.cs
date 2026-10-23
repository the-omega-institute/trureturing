using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CompleteSubdivisionCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionCounting.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/farhan2026multiset");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four exact distance bins",
        H("Four exact distance bins"),
        Blocks(
            Paragraph(Text("For an arbitrary landmark subset, let a_u be its original-vertex bit, b_uv its selected-midpoint bit, d_u its selected incident-midpoint count, A its original total and M its midpoint total. The four bin counts satisfy H0=a_u+b_uv, H1+b_uv=a_v+d_u, H2+a_u+a_v+b_uv=A+d_v and H3+d_u+d_v=M+b_uv. All equations use integers and preserve the exact counts at empty classes and at n=3.")),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-original-bit"),
                DeclarationHandle.Create(Prefix + "originalBit"),
                H("originalBit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The original-vertex selection bit is the integer indicator of membership in the landmark set."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-midpoint-bit"),
                DeclarationHandle.Create(Prefix + "midpointBit"),
                H("midpointBit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The midpoint selection bit is the integer indicator of membership in the landmark set."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-original-total"),
                DeclarationHandle.Create(Prefix + "originalTotal"),
                H("originalTotal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The integer total counts selected originals."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-midpoint-total"),
                DeclarationHandle.Create(Prefix + "midpointTotal"),
                H("midpointTotal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The integer total counts selected midpoints."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-selected-degree"),
                DeclarationHandle.Create(Prefix + "selectedDegree"),
                H("selectedDegree"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The selected degree counts selected midpoint vertices incident with an original."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-bin"),
                DeclarationHandle.Create(Prefix + "bin"),
                H("bin"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A bin counts selected vertices at one actual edge distance, using integer-valued indicators."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-bin-eq-count"),
                DeclarationHandle.Create(Prefix + "bin_eq_count"),
                H("bin eq count"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The integer bin is the natural multiset multiplicity embedded in the integers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-midpoint-bit-swap"),
                DeclarationHandle.Create(Prefix + "midpointBit_swap"),
                H("midpointBit swap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The same selected midpoint bit is obtained in either endpoint order."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-histogram"),
                DeclarationHandle.Create(Prefix + "histogram"),
                H("histogram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The four exact integer equations follow by summing the proved pointwise distance classes over every selected landmark."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-counting-profile-eq-of-histogram"),
                DeclarationHandle.Create(Prefix + "profile_eq_of_histogram"),
                H("profile eq of histogram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Four equal integer bins give equal actual distance multisets for the two incidence edges."))), DescribeRole.Theorem))));
}
