using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Quandles;

internal sealed class PresentedQuandleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S0/Certificates/Quandles/PresentedQuandle.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/gupta2025biorderability");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full term presentation of quandles with universal evaluation.",
        H("Presented quandles with action and inverse action"),
        Blocks(
            Node("terms", "Unrestricted quandle terms", "Term", DescribeRole.Definition,
                "Terms contain generators, action and inverse action. Mathlib's action is actor first. The inverse operation prevents the positive-term shelf from being substituted for a quandle."),
            Node("evaluation", "Evaluation in any quandle", "eval", DescribeRole.Definition,
                "An arbitrary generator assignment evaluates every expression in a target quandle using its action and inverse action. The generator type and target can be empty; there is no distinctness assumption."),
            Node("relations", "The least generated congruence", "Rel", DescribeRole.Definition,
                "The only constructors are equivalence, congruence for both operations, idempotence, left self-distributivity, the two inverse-action laws and the supplied equations. Every such derivation is respected by evaluation into any model of the equations."),
            Node("carrier", "The full quotient carrier", "Carrier", DescribeRole.Definition,
                "Quotient the term type by this congruence. The actual Quandle instance is built on the quotient: both operations descend, and the quandle laws follow from the corresponding constructors. This is a standard universal-algebra construction; its new implementation is consumed by the eight-crossing specialization, with no claim of mathematical novelty."),
            Node("generators", "Generators in the quotient", "of", DescribeRole.Definition,
                "Each generator denotes its term class. No injectivity is assumed or generally true."),
            Node("equations", "All supplied equations hold", "relation_eq", DescribeRole.Theorem,
                "Every presentation equation gives an equality of the actual quotient classes. The 8_20 specialization consumes this theorem for the six relations used by its order obstruction."),
            Node("extension", "Universal evaluation homomorphism", "lift", DescribeRole.Definition,
                "Every assignment satisfying all supplied relations extends by quotient lift to a ShelfHom, the existing Mathlib notion of quandle homomorphism. The homomorphism is defined on every quotient element, not merely the named generators."),
            Node("values", "The extension's generator values", "lift_of", DescribeRole.Theorem,
                "The extension agrees with the assignment on all generators. This reduction is used by the coloring separation."),
            Node("uniqueness", "Uniqueness on the full presented quandle", "lift_unique", DescribeRole.Theorem,
                "Any homomorphism with the specified generator values equals the extension. The proof inducts on expressions and derives inverse-action preservation from rack cancellation. Combined with lift and lift_of, this proves the presentation universal property for arbitrary target quandles. The least-congruence construction imposes no additional relations."))));

    private static DocumentBlock Node(string id, string title, string name, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
