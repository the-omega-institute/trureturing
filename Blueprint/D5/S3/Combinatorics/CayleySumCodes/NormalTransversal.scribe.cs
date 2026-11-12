using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class NormalTransversalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/NormalTransversal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal left transversals obtained from both total perfect subgroup code cases.",
        H("Total codes supply normal transversals"),
        Blocks(
            Describe.Lean(DescribeId.Create("normal-left-transversal"),
                DeclarationHandle.Create(Prefix + "NLT"), H("The NLT property"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "NLT(H,G) means that some conjugation-invariant subset T is a left "
                    + "transversal of H. The formal definition uses Mathlib Subgroup.IsComplement: "
                    + "multiplication T times H is a bijection onto G. Equivalently T meets each "
                    + "left coset exactly once. No nonsquare or identity-normalization condition "
                    + "is built into NLT."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("total-code-to-nlt"),
                DeclarationHandle.Create(Prefix + "result"), H("Both code branches"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every total perfect subgroup code in a finite group's normal-connection "
                    + "sum graph is NLT. In the singleton-nonsquare case take T=Y. In the "
                    + "two-element case take T=Y without the identity: the square of 1 puts "
                    + "1 in Y, removing it leaves exactly one member in the H-coset and changes "
                    + "no outside-coset intersection. Both choices are normal subsets. "
                    + "This is the total-code part of Proposition 4.1 in the source; it does "
                    + "not establish code inheritance, quotient total-code inheritance, "
                    + "the separate perfect-code route, or the full arbitrary-finite-group "
                    + "abelian equivalence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-connection-transversal-cases"),
                DeclarationHandle.Create(Prefix + "transversal_cases"), H("The specified connection transversal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "If the identity is absent from Y, Y itself is the actual left transversal. "
                    + "If the identity belongs to Y, remove it to obtain the transversal. "
                    + "This distinction retains the exceptional second branch of Theorem 2.1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("connection-index-cardinality"),
                DeclarationHandle.Create(Prefix + "cardinal"), H("The additional identity in the count"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The actual size of Y equals the subgroup index when 1 is absent and "
                    + "the index plus one when 1 is present. The second branch's additional "
                    + "identity is retained in the connection-set count although the sum "
                    + "graph excludes self-neighbors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("intermediate-subgroup-inheritance"),
                DeclarationHandle.Create(Prefix + "restrict"), H("Restriction to every intermediate subgroup"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For H contained in M contained in G, restrict a specified normal "
                    + "left transversal T to M. Every M-coset representative selected in G "
                    + "lies in M because its difference from the M-element lies in H. "
                    + "Conjugation by M preserves the intersection. Thus NLT(H,G) implies "
                    + "NLT(H,M) for arbitrary intermediate M, without subnormality. This "
                    + "is Lemma 4.2 of the correction. It is not a statement that quotient "
                    + "or subgroup total-code inheritance follows from NLT."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quotient-inheritance"),
                DeclarationHandle.Create(Prefix + "map"), H("Images under group quotients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a surjective group homomorphism f whose kernel lies in H, the image "
                    + "of an actual normal transversal is a normal transversal of f(H). "
                    + "The preimage of f(H) is exactly H, so any two putative image "
                    + "representatives in the same coset lift to the same original "
                    + "representative. Surjectivity transports conjugation invariance. "
                    + "Taking f:G to G/N gives NLT(H/N,G/N) whenever N is normal in G "
                    + "and contained in H. This is the quotient statement of Lemma 4.3. "
                    + "It asserts NLT inheritance and supplies no quotient total-code "
                    + "inheritance theorem."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion"))]));
}
