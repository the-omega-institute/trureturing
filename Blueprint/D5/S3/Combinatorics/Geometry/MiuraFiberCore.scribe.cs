using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraFiberCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraFiberCore.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive vectors in the existing actual core fibers.", H("Every indexed positive vector has a distinct actual realization"),
        Blocks(
            Describe.Lean(DescribeId.Create("miurafibercore-0"),
                DeclarationHandle.Create(Prefix + "core_positive_vectors_inject"), H("An injection into the actual fixed-core residual fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix any member K of the existing finite Core(a,b), with its individual normalized height function and both reduced axes. At every m,n at least 2(a+b)-1, the entire product of PositiveLengths(m-rowOccupied K,rowRuns K) and PositiveLengths(n-colOccupied K,colRuns K) injects into the actual normalized residual arrays on the m by n rectangle that reduce to this exact K. The codomain also retains, separately for each original physical side, equivalence of the assertion that all minima lie on that side. On a reduced actual core, inactive columns are precisely isolated frozen-run starts. A fixed equivalence indexes these individual lines by Fin of the already defined run count. Removing one compulsory cell from every positive run gives a supported extra-copy vector with exactly the required output dimension. Both complete vectors are then realized on one actual residual array. Equality of two outputs reads both extra-copy vectors back; their indexed positive lengths follow coordinate by coordinate. The theorem also gives the resulting lower bound on the original residualCount(a,b,m,n) of the complete actual residual class. This is a bound for each fixed core, with no assertion that lower bounds for distinct cores may be added. Surjectivity onto all arrays reducing to K and disjointness of fibers of different cores are not conclusions of this theorem."))), DescribeRole.Theorem))));
}
