using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HartRowleyGreedyRefutationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/hartrowley2025involutionprefixes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Greedy involution prefix and suffix counts can differ in a qualifying Coxeter system.",
        H("Orientation dependence of greedy involution counts"),
        Blocks(
            Paragraph(Text(
                "The linked Lean declarations specify the claim and its refutation. "
                + "Their statement formulas are unavailable from the native projector; "
                + "the explanations below are authored exposition.")),
            Describe.Lean(
                DescribeId.Create("hart-rowley-greedy-equality-claim"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/HartRowleyGreedyRefutation.claim"),
                H("The unrestricted tentative assertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Hart and Rowley, arXiv:2502.00777v1, section 3, printed page 5, "
                    + "tentatively suggest equality of their greedy prefix and suffix counts. "
                    + "The claim ranges over all Coxeter systems, including infinite systems, "
                    + "whose every nonidentity element has a unique maximum-length "
                    + "order-exactly-two prefix. The quantified equality decision has a "
                    + "classical instance for every carrier and imposes no finiteness condition. "
                    + "The ancestor maximum compares every involution prefix using genuine "
                    + "Coxeter length and length additivity. The counts recursively remove "
                    + "the selected factor and return zero at identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hart-rowley-greedy-equality-refuted"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/HartRowleyGreedyRefutation.result"),
                H("A qualifying Coxeter countermodel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The result is the literal negation of the closed claim. Mathlib's "
                        + "type A3 Coxeter presentation is identified with permutations of "
                        + "four letters using 24 normal words and their transitions under "
                        + "all three adjacent generators. A lower bound along every "
                        + "generator step and the normal-word upper bound identify actual "
                        + "Coxeter length with inversion count. A finite kernel certificate "
                        + "then verifies the unique maximum for every nonidentity "
                        + "permutation and every competing involution prefix.")),
                    Paragraph(Text(
                        "The prefix and suffix procedures are well-founded recursions on "
                        + "Coxeter length. The suffix choice is transported by inversion, "
                        + "with its maximum and uniqueness proved from the group-wide "
                        + "prefix property. The bounded evaluator is equated to the actual "
                        + "recursion whenever its fuel is at least that length. For w=2431, "
                        + "with (uv)(i)=u(v(i)), the prefix residual chain is "
                        + "2431,1342,1243,1 and the suffix chain is 2431,2134,1. "
                        + "Their counts are respectively three and two.")),
                    Paragraph(Text(
                        "The initial commuting pair (12)(34) leaves two further prefix "
                        + "factors, while the longer right factor (24) leaves one. "
                        + "Inversion still relates suffixes of w to prefixes of its inverse; "
                        + "it need not preserve the prefix count of w itself. "
                        + "The source's Conjectures 1.2 and 1.3 and its Coxeter-element "
                        + "results are separate. This model satisfies the ancestor "
                        + "hypothesis and its counts obey the rank-three bound. "
                        + "No minimality, classification, adjacent resolution, or "
                        + "worldwide priority claim is made. Bounded source-status "
                        + "qualification and its remaining limits are recorded in the "
                        + "source note and problem dossier."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hart-rowley-greedy-prefix-suffix-equality"),
                    ResolutionKind.Refuted)))));
}
