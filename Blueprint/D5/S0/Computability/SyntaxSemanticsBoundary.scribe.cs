using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class SyntaxSemanticsBoundaryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Lawvere =
        LibraryNoteRef.Create("D5/L/Diagonal/lawvere1969diagonal");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "No same-level code type enumerates all predicates on itself.",
            H("The Syntax-Semantics Boundary"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("same-layer-predicates-are-not-enumerable"),
                    DeclarationHandle.Create("D5/S0/Computability/SyntaxSemanticsBoundary.same_layer_predicates_not_enumerable"),
                    H("Same-level syntax cannot enumerate full predicate semantics"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, F.Id("Code"), Comma, Sp,
                        Forall, Sp, F.Id("semantics"), Colon, Sp,
                        F.Id("Code"), To, Sp,
                        Operatorname, Grp(F.Id("Set")), Open, F.Id("Code"), Close,
                        Comma, Sp, Neg,
                        Operatorname, Grp(F.Id("Surjective")),
                        Open, F.Id("semantics"), Close, Dot))),
                    AssessedProvenance.FromLiterature(Lawvere),
                    Blocks(
                        Paragraph(Text(
                            "Take any type of codes and any proposed interpretation that "
                            + "assigns to each code a predicate on that same code type. The "
                            + "interpretation cannot be surjective: diagonalization forms "
                            + "the predicate that rejects a code exactly when the predicate "
                            + "assigned to that code accepts it, so the diagonal predicate "
                            + "cannot equal any predicate in the proposed range. Full "
                            + "predicate semantics therefore exceeds every same-level "
                            + "enumeration by syntax. This is the precise cardinal boundary "
                            + "asserted by the source atom; it does not assume a particular "
                            + "programming language or claim that a higher-level semantics "
                            + "has already been constructed.")),
                        Paragraph(Text(
                            "The library was searched before proving. Pinned Mathlib already "
                            + "contains the exact result as Function.cantor_surjective in its "
                            + "basic function theory; the neighboring declarations "
                            + "Function.exists_fixed_point_of_surjective and "
                            + "Function.cantor_injective were also checked. The Lean theorem "
                            + "is consequently a declared thin honest wrapper that applies "
                            + "the upstream result without reproducing its diagonal proof. "
                            + "A repository search found computability-restricted closure "
                            + "results and finite diagonal escape results, but no existing "
                            + "formal declaration of this unrestricted predicate-enumeration "
                            + "boundary."))),
                    DescribeRole.Theorem))));
}
