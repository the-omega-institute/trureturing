using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class InclusiveCountLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaRvm/InclusiveCountLimit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounds at zero-free heights extend to the inclusive zero count with the same envelope.",
        H("Inclusive zero counts at the cutoff"),
        Blocks(
            Paragraph(Text("The count N(T) includes all nontrivial zeta zeros with 0 < Im ρ ≤ T and their analytic multiplicities. A good height is a height that is not a nontrivial zero ordinate.")),
            Describe.Lean(
                DescribeId.Create("eventually-good-height-and-count-eq"),
                DeclarationHandle.Create(Owner + ".eventually_goodHeight_and_count_eq"),
                H("The count immediately to the right"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordinates in (T,T+1] form a finite set that excludes T. Its complement contains a neighborhood of T. In a sufficiently short interval immediately to the right, every height is good and the set of zeros counted in (0,t] is exactly the set counted in (0,T]. Equality of the sets preserves every multiplicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abs-ncount-sub-le-of-good-height"),
                DeclarationHandle.Create(Owner + ".abs_ncount_sub_le_of_goodHeight"),
                H("Transfer of a right-continuous bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Suppose M and E are right-continuous at each T ≥ T₀. If |N(t)−M(t)| ≤ E(t) at every good height t ≥ T₀, the same inequality holds at every T ≥ T₀.")),
                    Paragraph(Text("Take a right limit along heights at which N(t) equals N(T). Continuity of subtraction and absolute value gives the limiting discrepancy. Closedness of the real order preserves the bound. The argument retains the full multiplicity at T and requires no assumption about a symmetric convention for the argument of zeta."))),
                DescribeRole.Theorem))));
}
