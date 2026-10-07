using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class PrivateEncloserDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/PrivateEncloserDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In a distinct odd cover with minimum modulus sum at its class count, "
            + "an odd nonunit modulus enclosing an original's complete private region "
            + "must occur whenever it is smaller than an actual descendant modulus.",
        H("Private Encloser Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("private-encloser-below-descendant-is-present"),
                DeclarationHandle.Create(Prefix + "private_encloser_below_descendant_is_present"),
                H("A descendant bounds every missing private encloser"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F cover every natural number by L congruence classes with "
                        + "pairwise distinct odd moduli greater than one. Assume its modulus "
                        + "sum is no larger than that of any such cover with L classes. "
                        + "Choose original indices g and M so that the modulus of g divides "
                        + "the modulus of M. The indices may coincide.")),
                    Paragraph(Text(
                        "Let e be odd and greater than one, and suppose e is smaller than "
                        + "the modulus of M. If all private points of g are congruent to "
                        + "one fixed w modulo e, then e is an original modulus. A private "
                        + "point belongs to g and to no other original class; the hypothesis "
                        + "concerns the entire private region. The conclusion specifies the "
                        + "numerical modulus, without assigning its original residue.")),
                    Paragraph(Text(
                        "Suppose e is absent. Replace slot M by the class w modulo e, "
                        + "and, when g differs from M, move the residue of g to the old "
                        + "residue of M while retaining g's modulus. A private point of g "
                        + "belongs to the new class. Every other point has an old owner "
                        + "different from g. If that owner is M, the moved class g covers "
                        + "the point by divisibility; otherwise its owner is unchanged. "
                        + "This also covers the case g equals M, where only one slot changes.")),
                    Paragraph(Text(
                        "The absent modulus e preserves distinctness. Oddness and the "
                        + "number of classes are preserved, but the modulus sum decreases "
                        + "by the positive difference between the old modulus of M and e. "
                        + "This contradicts minimality. No assumption of minimum class "
                        + "count, disjoint comparable classes, or a prime-power descendant "
                        + "ratio is required."))),
                DescribeRole.Theorem))));
}
