using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class PresentationTimeCochainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same time/id edge in every finite presentation basis measures actual primitive-orbit count.",
        H("The same time/id edge in every finite presentation basis measures actual primitive-orbit count"),
        Blocks(
            Paragraph(Text("In the outOld basis, vertex_matrix identifies graph time with the literal nonnegative counted matrix A. dyadicGyration_nonnegative applied to A and the identity, followed by RankedTimeRecoding.relative_time and orbitChart, gives the actual primitive-orbit cardinality. closed_square is then applied to r=time and s=id; both composites equal time even if it is singular. The common K is retained and canceled. rows_id identifies the new backward matrix as the identity. This proves the same time calibration in c without assigning zero to an open chart edge.")),
            Describe.Lean(
                DescribeId.Create("presentationtimecochain-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/PresentationTimeCochain.time_calibration"),
                H("Time calibration through the same closed square"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite presentation F, any finite basis c of F.V coefficient functions indexed by Fin m, and every natural d with NeZero d and hd : three divides d, let b=presentationBasis F and K=value(b,c,id,(vertex F).time). The result states both value(b,b,time,id)+K=K+value(c,c,time,id) and dyadicGyration d rows(c,c,time) 1=card(Orbit F d) in ZMod 3. No invertibility of graph time is assumed; zero vertices and empty orbit fibers remain included."))),
                DescribeRole.Theorem),
            Paragraph(Text("The complete native application is recorded in the ActualWordEnumeratedLoop owner narrative. Here this calibration is used at OriginalRootKernelCheck.hcal for every nonzero p divisible by three, before any specialization to three or six. No orbit-count calibration replaces arbitrary h.")))));
}
