using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class AffineExamplesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/AffineExamples.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "AffineExamples in the actual loopless sum graphs.",
        H("Retained constructions and exact corrected examples"),
        Blocks(
            Describe.Lean(DescribeId.Create("action-mul"),
                DeclarationHandle.Create(Prefix + "action_mul"), H("Composition of affine permutations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The multiplication (s,b)(t,c)=(st,b+sc) agrees with composition on every field element."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("action-injective"),
                DeclarationHandle.Create(Prefix + "action_injective"), H("The full faithful affine action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The field action is injective; the full multiplier and offset are retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conjugate-iff"),
                DeclarationHandle.Create(Prefix + "conjugate_iff"), H("The actual nontranslation conjugacy classes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every nonidentity multiplier s, its full affine conjugacy class is exactly the multiplier fiber. This binds the source unions of classes in both retained constructions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("connection-normal"),
                DeclarationHandle.Create(Prefix + "connection_normal"), H("The corrected normal connection set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The connection is the identity together with every affine negation, over the entire field."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("total-code"),
                DeclarationHandle.Create(Prefix + "total_code"), H("The corrected subgroup total codes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite field of odd characteristic whose units square to 1 or -1, the full complement fixing zero is a total perfect code of the actual loopless graph. The F3 and F5 specializations are the two original examples, not a claim for arbitrary q."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("connected-iff"),
                DeclarationHandle.Create(Prefix + "connected_iff"), H("The precise connectedness distinction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For this actual affine connection, connectedness holds exactly when all units are signs. Thus the F3 example is connected and the F5 example is disconnected. Generation alone is not used as a converse connectedness criterion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("transversalconnection-normal"),
                DeclarationHandle.Create(Prefix + "transversalConnection_normal"), H("Normal multiplier-transversal connections"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("All affine elements whose multiplier lies in the chosen transversal form a normal subset."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("total-construction"),
                DeclarationHandle.Create(Prefix + "total_construction"), H("The complete retained affine total construction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite field, every multiplicative subgroup H and every actual left coset transversal T, if its internal representative a0 is a nonsquare of H, the full union of the chosen multiplier classes admits the embedded H as a total code. This includes all original q-1=s*t, t>1, H=<c^s> parameters of Zhang Theorem 5.13. No code property is assumed in the hypotheses."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("perfectconnection-normal"),
                DeclarationHandle.Create(Prefix + "perfectConnection_normal"), H("Normal perfect-code connections"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Remove the internal multiplier class and add all nonidentity translations, exactly as in the source construction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("perfect-construction"),
                DeclarationHandle.Create(Prefix + "perfect_construction"), H("The complete retained affine perfect construction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every actual multiplier transversal gives the specified perfect-code connection, independently of a nonsquare or total-code assumption."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/CayleySumCodes/CodeCentralizers")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal"))]));
}
