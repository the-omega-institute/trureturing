using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Witt;
internal sealed class BoundedEulerCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Witt/BoundedEulerCorrection.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded corrections for arbitrary integer ghost weights", H("Bounded corrections for arbitrary integer ghost weights"), Blocks(
            Paragraph(Text("For an arbitrary integer sequence w, the Euler exponent at n is the Euclidean quotient of w(n) minus the proper-divisor ghost, and the correction is its residue modulo n. Only n>0 is constrained. The value at zero is unused by the actual exponential. The proof constructs the integer account by strong recursion, then reuses the existing Euler and Gauss machinery to establish actual integrality and positive-index uniqueness.")),
            Node("ledger", "ledger", "Strong recursion uses only proper divisors. Division here is integer Euclidean division; the denominator at zero has no mathematical role.", DescribeRole.Definition),
            Node("properGhost", "properGhost", "The finite sum uses the actual proper divisors of n and their integer Euler exponents.", DescribeRole.Definition),
            Node("correction", "correction", "The remainder selects the unique representative from zero through n-1 at every positive index.", DescribeRole.Definition),
            Node("IsCorrection", "IsCorrection", "The predicate combines positive-index bounds with integrality of every coefficient of the literal rational formal exponential.", DescribeRole.Definition),
            Node("correction_equation", "correction equation", "Euclidean quotient and remainder give the exact divisor-sum ghost equation. This is a derived identity for the constructed account.", DescribeRole.Theorem),
            Node("correction_integral", "correction integral", "The constructed account satisfies the existing divisor-ghost Gauss congruences. The canonical integrality theorem identifies the actual exponential with an integer Euler series.", DescribeRole.Theorem),
            Node("correction_unique", "correction unique", "For a competing bounded correction, the existing integral-input ledger theorem supplies integer exponents. Strong induction on proper divisors makes both the residue and quotient rigid. No equality at index zero is claimed.", DescribeRole.Theorem),
            Node("moebiusTransform", "moebiusTransform", "The finite integer sum is the uncorrected Mobius transform of the arbitrary weight.", DescribeRole.Definition),
            Node("moebius_identity", "moebius identity", "Mobius inversion applies to the exact constructed ghost equation, producing the correction term with mu(n/d).", DescribeRole.Theorem),
            Node("logarithmic_error", "logarithmic error", "The absolute Mobius value is at most one and each positive-index correction is less than its index. Complementary divisors convert the normalized divisor sum into reciprocal divisors, bounded by the harmonic sum and one plus the natural logarithm. No positivity assumption on the original weights is used.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("boundedeulercorrection-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
