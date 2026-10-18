using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class AngleStarCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite weighted angle-star capacity inequality.",
        H("Weighted angle-star capacity"),
        Blocks(
            Paragraph(Text(
                "Let I be a nonempty finite set of target occurrences and F a finite set "
                + "of neighbouring global labels. For i in I, alpha(i) is the target angle "
                + "and neighbor(i,f) is the angle mass assigned to label f in that local "
                + "star. The coefficient mu(f) records the maximum multiplicity with which "
                + "the f contribution is charged across the target stars.")),
            Describe.Lean(
                DescribeId.Create("weighted-angle-star-capacity"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/AngleStarCapacity.weighted_star_capacity"),
                H("Local angle demand bounds the target occurrence count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume every target occurrence has local demand strictly above "
                        + "pi: pi < 2 alpha(i) + sum_f neighbor(i,f). Assume the total "
                        + "target mass is (2-m) pi, and for every f the aggregate charged "
                        + "neighbour mass is at most mu(f) times (2-mf(f)) pi. If g is the "
                        + "cardinality of I, then")),
                    Paragraph(Text(
                        "The resulting strict bound is g < 2(2-m) plus the finite sum "
                        + "over f of mu(f)(2-mf(f)).")),
                    Paragraph(Text(
                        "The proof sums the strict local inequalities over the actual finite "
                        + "occurrence set, swaps the two finite sums, applies the per-label "
                        + "multiplicity bounds, and divides by the positive pi. It is the "
                        + "finite aggregation step behind the mixed-matching capacity estimate.")),
                    Paragraph(Text(
                        "The lemma does not supply the local angle lower bound, the global "
                        + "2pi equations, the multiplicity coefficients, or a geometric "
                        + "realization. Those must be established by the surrounding actual "
                        + "face-pairing and angle-formula interfaces.")),
                    Paragraph(Text(
                        "The faithful four-slot escape audit for this public theorem remains "
                        + "unfinished under https://github.com/the-omega-institute/trureturing/issues/19006. "
                        + "The issue records missing registration evidence only; it supplies "
                        + "neither a mathematical proof nor a declared_validated registration."))),
                DescribeRole.Theorem))));
}
