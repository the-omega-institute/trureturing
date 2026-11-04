using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Jacobi;

internal sealed class ConnectedFlagGradeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Jacobi/ConnectedFlagGrade.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact connected source grade embeds in the actual diagram quotient", H("The exact connected source grade embeds in the actual diagram quotient"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-flag-grade"),
                DeclarationHandle.Create(Prefix + "flagGrade"), H("Actual connectivity, original genus, and every label population"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The grade of a finite cyclic flag diagram records whether its actual incidence graph is connected, its original edge-pair Euler genus, and the number of flags with each ordinary color or numbered anchor label. Selecting a true connectivity coordinate and the required genus and populations gives the connected fixed-grade source on this carrier. The exceptional bare topological circle remains a separate source case."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-source-grade-relator"),
                DeclarationHandle.Create(Prefix + "GradeRelator"), H("The same literal AS, IHX, CL, and flag-isomorphism generators"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite linear combination on a grade fiber is a GradeRelator exactly when its inclusion in the free space of all actual diagrams is a literal ActualRelator. The construction uses the same geometric generators and introduces no normalization-kernel relation. AS and both IHX branches preserve actual connectivity by transferring incidence walks through the local rotor tables. Explicit permutations conjugate the rotor cycles and preserve the number of actual owner orbits. Edge pairing is unchanged, so original genus is preserved. CL keeps the graph and exchanges exactly two ordinary labels, preserving every population."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-source-graded-jacobi-space"),
                DeclarationHandle.Create(Prefix + "GradedJacobiSpace"), H("The quotient within one exact source grade"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("GradedJacobiSpace is the rational free space on the exact grade fiber, divided by the span of its literal source generators. The original connectivity, genus and label populations are conditions on its actual diagram basis; they are not supplied as an abstract homogeneity assumption."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-source-quotient-inclusion"),
                DeclarationHandle.Create(Prefix + "gradeInclusion"), H("The natural quotient inclusion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inclusion sends a source basis diagram to the same actual diagram in the all-diagram AS, IHX and ordinary-CL quotient. A coordinate projection back to the fiber sends every all-diagram generator either to zero or to the same literal source generator, because every term of each actual relation has one exact grade."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-source-quotient-zero-reflection"),
                DeclarationHandle.Create(Prefix + "gradeInclusion_injective"), H("The source inclusion reflects zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every exact connectivity, Euler-genus and label-population grade, the natural quotient inclusion is injective. The proof constructs a left inverse on the quotients from the literal basis projection and the checked grade invariance of every actual relation. Thus a source class maps to zero exactly when it was already zero in that exact source quotient. This supplies the missing finite-flag connected fixed-genus quotient comparison; it does not by itself establish the global skeleton presentation, the insertion normal form, the exceptional bare-circle case or the full four-loop theorem."))), DescribeRole.Theorem))));
}
