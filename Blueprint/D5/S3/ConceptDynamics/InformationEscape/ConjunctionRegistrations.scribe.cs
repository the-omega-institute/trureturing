using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ConjunctionRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed finite conjunction registration programs preserve complete source statements.",
        H("ConjunctionRegistrations"),
        Blocks(
            Node("partitionClauses", "The four clauses retain coverage and each of the three disjointness assertions.", DescribeRole.Definition),
            Node("partitionArena", "The arena is the original 31-point finite projective plane.", DescribeRole.Definition),
            Node("partitionRealization", "Three state-dependent membership predicates retain the original projective axis sets.", DescribeRole.Definition),
            Node("partition_bridge", "The bridge only reflects Boolean admission and normalizes filtering the universal set by membership; it uses no partition facts.", DescribeRole.Theorem),
            Node("partition_lawSensitive", "The frozen partition theorem satisfies the law; removing the first admitted set falsifies it.", DescribeRole.Theorem),
            Node("partition_slotSensitive", "Removing any one admitted set falsifies the law while the other two readouts stay fixed.", DescribeRole.Theorem),
            Node("countsClauses", "Three count-equality clauses preserve the right-associated source conjunction.", DescribeRole.Definition),
            Node("countsArena", "The arena is the original three-voter carrier Fin 3.", DescribeRole.Definition),
            Node("countsRealization", "The readouts retain prefers v i (i + 1); the three finite indices reduce to the exact source pairs (0,1), (1,2), and (2,0).", DescribeRole.Definition),
            Node("counts_bridge", "The bridge retains the three unreduced preference counts and every equality to two.", DescribeRole.Theorem),
            Node("counts_lawSensitive", "The frozen vote-count theorem satisfies the law; one all-false readout falsifies it.", DescribeRole.Theorem),
            Node("counts_slotSensitive", "Each of the three preference readouts independently affects its count clause.", DescribeRole.Theorem),
            Node("membershipClauses", "A positive membership clause and a negative membership clause preserve the two source conjuncts.", DescribeRole.Definition),
            Node("membershipArena", "The arena is ZMod 4 with two generated anchor slots.", DescribeRole.Definition),
            Node("membershipRealization", "The single readout is membership in the original subgroup; anchors are exactly two and one.", DescribeRole.Definition),
            Node("membership_bridge", "The bridge preserves both source anchors and membership polarity without rewriting membership using proved subgroup facts.", DescribeRole.Theorem),
            Node("membership_lawSensitive", "The frozen subgroup theorem satisfies the law; an all-false readout falsifies positive membership.", DescribeRole.Theorem),
            Node("membership_slotSensitive", "The readout can change the law, and exchanging either anchor with the other independently falsifies its clause.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
