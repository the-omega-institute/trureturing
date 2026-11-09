using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class ProperQuaternionOldNecessityCounterexampleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper-normal necessity counterexample", H("Actual finite-group refutation"),
        Blocks(Describe.Lean(DescribeId.Create("properquaternionoldnecessitycounterexample-refutation"),
            DeclarationHandle.Create("D5/S3/Combinatorics/CayleySumCodes/ProperQuaternionOldNecessityCounterexample.result"),
            H("The source counterexample"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/manikandishzhang2026sumcodes")),
            Blocks(Paragraph(Text("The exact Example2.3(3) uses G=QuaternionGroup2 times the multiplicative form of ZMod3, H=Q8 times the identity and Y={(1,0),(-1,0),(1,1),(1,2)} in additive notation. The finite proof establishes that H is proper, normal and a total perfect subgroup code in this same actual graph. The unique internal representative of any normal transversal is central, and every central member of H is a square of H. Thus the old necessity fails even on proper normal subgroups; this is independent of the two whole-group examples."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples"))]));
}
