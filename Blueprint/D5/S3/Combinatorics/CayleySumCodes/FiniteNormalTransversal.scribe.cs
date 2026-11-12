using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class FiniteNormalTransversalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/FiniteNormalTransversal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/Nikandish/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The elementary normal-transversal characterization of finite abelian groups.",
        H("Normal transversals in arbitrary finite groups"),
        Blocks(
            Describe.Lean(DescribeId.Create("all-nlt-implies-commutative"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every subgroup NLT forces commutativity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every finite group G, if every subgroup has a conjugation-invariant "
                    + "left transversal in G, then G is abelian. Strong induction on the "
                    + "actual group cardinal passes the property to proper subgroups and "
                    + "normal-subgroup quotients. A proper nontrivial normal subgroup and "
                    + "its quotient are abelian, so the solvable theorem applies. In the "
                    + "remaining simple case, every proper subgroup is abelian. Distinct "
                    + "maximal subgroups intersect trivially and are self-normalizing. "
                    + "The proof counts their actual conjugacy orbits and disjoint sets "
                    + "of nonidentity elements, then proves the exact covering equality. "
                    + "The equality contradicts properness. No order-sixty restriction, "
                    + "classification of finite simple groups, or finite sample is used. "
                    + "The general simple-center lemma and nonidentity injection are reused "
                    + "from SimpleOrderSixty with its Moonshine-in-Kansas/atlas attribution; "
                    + "their declarations themselves have no order-sixty hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-subgroup-code-equivalence"),
                DeclarationHandle.Create(Prefix + "equivalence"),
                H("Abelian groups and subgroup sum-graph codes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A finite group is abelian exactly when every subgroup is a perfect "
                    + "or total perfect code of some loopless Cayley sum graph with a normal "
                    + "connection set. The graph and code type may depend on the subgroup. "
                    + "Every code supplies NLT, including the two-element total-code branch "
                    + "where the identity is removed from the connection set. Conversely, "
                    + "abelian groups admit perfect-code witnesses for every subgroup. "
                    + "Together these are the three equivalent properties in Theorem 4.5 "
                    + "of both public correction versions by Ma, Nikandish and Zhang. "
                    + "NLT restriction is not an assertion of total-code quotient "
                    + "inheritance, and this elementary route does not independently "
                    + "certify the unaffected CFSG casework in the antecedent article."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/FiniteGroups/SimpleOrderSixty"))]));
}
