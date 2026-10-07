using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class SectionClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For finite groups, a bound on every alternating section passes through subgroups and quotients and is stable under extensions when the threshold is at least four.",
        H("Closure of the bounded-section class"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-involves-of-surjective-image"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.involves_of_surjective_image"),
                H("Sections lift through a surjection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary groups G, Q and A and a surjective homomorphism q from G to Q, Involves(A,Q) implies Involves(A,G). Pull back the section subgroup and compose its surjection to A. The section subgroup need not be normal."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-alpha-le-iff-sections"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_iff_sections"),
                H("The maximum controls every section"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite group G and natural k, alpha(G) is at most k if and only if every natural n for which the alternating group on Fin n is a section of G satisfies n at most k. This uses the genuine maximum alpha_spec, including small alternating degrees."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-alpha-le-four-of-subsingleton"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_four_of_subsingleton"),
                H("Trivial groups satisfy the small bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite subsingleton group has alpha at most four. Its order is one, and the alternating-degree cardinality bound excludes larger sections."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-alpha-le-of-injective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_injective"),
                H("Bounds pass through faithful maps"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite groups G and Q and an injective homomorphism from G to Q, alpha(G) is at most alpha(Q). An arbitrary subgroup section of G transports to a subgroup section of Q."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-alpha-le-of-subgroup-le"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_subgroup_le"),
                H("Bounds pass through subgroup inclusions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For subgroups H and K of a finite group G, H contained in K implies alpha(H) at most alpha(K). Apply the injective-map bound to the inclusion homomorphism."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-alpha-le-of-surjective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_surjective"),
                H("Bounds pass to quotient images"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite groups G and Q and a surjective homomorphism from G to Q, alpha(Q) is at most alpha(G). Pull back each alternating section of Q."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-alpha-le-of-kernel-codomain"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_kernel_codomain"),
                H("Kernel and codomain bounds give an extension bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite groups G and Q, any homomorphism q from G to Q, and any natural k at least four, alpha(ker q) at most k and alpha(Q) at most k imply alpha(G) at most k. Surjectivity is unnecessary. Alternating groups in degrees at least five are simple, so their sections occur in Q or ker q; smaller degrees are already bounded by k."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-alpha-le-of-normal-extension"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_normal_extension"),
                H("Normal extensions remain bounded"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite group G, normal subgroup N and natural k at least four, alpha(N) at most k and alpha(G/N) at most k imply alpha(G) at most k. Use the quotient homomorphism and its kernel."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-alpha-quotient-kernel-le"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_quotient_kernel_le"),
                H("The first isomorphism bounds a quotient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite groups G and Q and any homomorphism q from G to Q, alpha(G/ker q) is at most alpha(Q). The first-isomorphism embedding is faithful, even when q is not surjective."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sectionclosure-alpha-preimage-le"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_preimage_le"),
                H("Preimages of bounded subgroups"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite groups G and Q, any homomorphism q from G to Q, any subgroup H of Q, and natural k at least four, bounds alpha(ker q) at most k and alpha(H) at most k imply alpha(q inverse image of H) at most k. Restrict q to this preimage; its kernel embeds into ker q."))),
                DescribeRole.Lemma))));
}
