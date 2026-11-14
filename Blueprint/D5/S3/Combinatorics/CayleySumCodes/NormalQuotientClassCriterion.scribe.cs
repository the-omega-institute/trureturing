using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class NormalQuotientClassCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/NormalQuotientClassCriterion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/FiniteGroups/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual quotient conjugacy-class criterion for perfect subgroup codes.",
        H("Normal transversals and equal-cardinality conjugacy lifts"),
        Blocks(
            Describe.Lean(DescribeId.Create("normal-transversal-class-lifts"),
                DeclarationHandle.Create(Prefix + "nlt_iff"), H("Every quotient class lifts without collapsing conjugates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every normal subgroup H of every finite group G, a normal left transversal exists if and only if each actual element of G/H has a lift t whose full conjugacy class has the same cardinality as its quotient class. The projection from conjugates of t onto conjugates of its image is always surjective. Equality of their finite cardinalities makes it bijective. Choosing one lift for each quotient conjugacy class and taking its entire conjugacy class gives an actual conjugation-invariant transversal, with existence and uniqueness in every coset. The forward direction uses the actual specified normal transversal. Neither a count bound alone nor an order-specific group classification is substituted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normal-subgroup-perfect-class-criterion"),
                DeclarationHandle.Create(Prefix + "result"), H("The unaffected perfect-code criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A normal subgroup H of a finite group is a perfect code of some normal-connection-set loopless Cayley sum graph exactly when every x outside H has h in H such that the conjugacy class of xH in G/H and the conjugacy class of xh in G have equal cardinality. The graph may depend on H. The identity quotient class is handled separately by its identity lift; no coset or trivial subgroup is discarded. This is the perfect-code second part of antecedent Theorem 2.9, attributed as unaffected by the correction's missing total case. The proof uses the actual normalized perfect-code/NLT equivalence. It does not certify the antecedent's unrelated CFSG lemmas or assert total-code inheritance in quotients."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal"))]));
}
