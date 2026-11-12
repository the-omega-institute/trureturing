using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class PerfectCodeTransversalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/Nikandish/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized perfect subgroup codes in normal-connection sum graphs.",
        H("Perfect codes and identity-containing normal transversals"),
        Blocks(
            Describe.Lean(DescribeId.Create("perfect-code-definition"),
                DeclarationHandle.Create(Prefix + "IsPerfectCode"), H("Closed neighborhoods"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A perfect code has exactly one code vertex in each closed neighborhood, "
                    + "including the vertex itself. A total perfect code instead uses open "
                    + "neighborhoods, so the predicates and their transversal criteria differ."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transversal-to-perfect-code"),
                DeclarationHandle.Create(Prefix + "of_transversal"), H("Constructing the witness graph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A specified conjugation-invariant left transversal T containing 1 gives "
                    + "a perfect subgroup code with connection set T without 1. Inside H the "
                    + "only closed-neighborhood code vertex is the vertex itself; outside H "
                    + "uniqueness follows from the actual coset representative. This retains "
                    + "the normalized perfect-code antecedent of Jun-Yang Zhang, Lemma 3.1; "
                    + "the supplied arXiv v1 and final publisher article remain distinct source "
                    + "identities. No graph equality under identity deletion is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("perfect-code-normalization"),
                DeclarationHandle.Create(Prefix + "normalized_transversal"), H("Normalizing an arbitrary witness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For an arbitrary perfect-code connection set Y, its intersection with "
                    + "H is contained in {1}, and need not be empty. Remove 1 and insert 1 "
                    + "as the H-coset representative to get an actual normal left transversal. "
                    + "This supplies the perfect-code part of correction Proposition 4.1 "
                    + "and repairs the arbitrary-witness disjointness inference; it does "
                    + "not identify the old and normalized graphs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("existential-perfect-code-criterion"),
                DeclarationHandle.Create(Prefix + "exists_iff"), H("The normalized existential equivalence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A subgroup has some perfect-code sum graph with normal connection "
                    + "set if and only if it has an identity-containing normal left "
                    + "transversal. The existential witnesses may change; this is not a "
                    + "fixed-connection-set equivalence or a quotient code-inheritance claim."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normal-subgroup-nlt-perfect-code"),
                DeclarationHandle.Create(Prefix + "normal_exists_iff"), H("Normal subgroups admit normalization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For normal H, NLT is equivalent to existence of a perfect-code sum "
                    + "graph. The representative of H in a normal transversal is central "
                    + "in G. Translating the whole transversal by its inverse preserves "
                    + "conjugation invariance and gives a representative equal to 1. "
                    + "The proof does not extend this normalization to nonnormal H or "
                    + "claim equality of the original and constructed graphs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("abelian-perfect-code-existence"),
                DeclarationHandle.Create(Prefix + "abelian_exists"), H("Every abelian subgroup has a witness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every subgroup of an abelian group has a perfect-code sum-graph "
                    + "witness. Choose an actual left transversal containing 1; in an abelian "
                    + "group every subset is conjugation invariant. The construction does "
                    + "not require finiteness and supplies the finite case retained from "
                    + "Zhang Theorem 5.1. It claims neither regularity nor total perfect "
                    + "coding for arbitrary subgroup order."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/NormalTransversal"))]));
}
