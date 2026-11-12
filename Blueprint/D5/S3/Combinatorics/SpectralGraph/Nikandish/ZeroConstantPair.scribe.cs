using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class ZeroConstantPairDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/Nikandish/ZeroConstantPair." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire zero-constant endpoint family.", H("The entire zero-constant endpoint family."),
        Blocks(
            Paragraph(Text("Source: four-prime-zero-constant, supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The original parameter domains, attribution and failed-method limitations are retained. Formal proofs are task-local integrations of the full source results. General four-prime and higher-prime Q3 remain open outside the stated families. Original academic approval and publication boundaries are unchanged.")),
            Item("bezout", "denominator_bezout", "The exact universal Bezout-eight identity", "The source N and D polynomials satisfy the complete ring identity; D is odd and at least three for integer a>=2."),
            Item("denominator", "denominator_obstruction", "The sole positive rational candidate is never integer", "The entire integer a>=2 domain excludes N-Dc=0 by the odd denominator and exact Bezout identity, without a tail bound."),
            Item("factor", "factor_two", "The exact whole-operator root-two factorization", "For b=(a-1)(2a-1), the characteristic endpoint factors as 2a(a-1)c(N-Dc). Polynomial c=0 is an interpolation boundary, never a positive graph example."),
            Item("low", "low_eigenpair", "Full real free-tail interval", "For all real a>=2 and c>=a the genuine operator has an eigenpair in (1,3), retaining c=a and both tail orderings."),
            Item("actual", "actual_nonintegral", "Actual ideal-graph nonintegrality on the full family", "All natural a>=2 and c>=a on arbitrary distinct primes are covered. No tail coprimality is assumed and no general integrality criterion follows."),
            Item("minimum", "minimum_window", "The genuine full-operator minimum in (1,3)", "For every real a>=2 and c>=a, the minimum comparison includes every real eigenpair of the full source operator. The integer endpoint-two obstruction remains a separate arithmetic theorem.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift"))]));
}
