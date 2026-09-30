using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class ZeckendorfPrefixCylinderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical Zeckendorf prefix cylinders, their composition coordinates, and natural density.",
        H("Actual Zeckendorf Prefix Cylinders"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prefix-value-has-canonical-digits"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder"
                    + ".prefixValue_has_canonical_digits"),
                H("The literal prefix value has exactly its prescribed digits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every length m and internally nonadjacent binary prefix w, the "
                    + "canonical Zeckendorf digits of its Fibonacci value agree with w "
                    + "below m and vanish at every index above. The proof builds a finitely supported raw "
                    + "digit string, proves it canonical from internal nonadjacency, "
                    + "computes its Fibonacci value, and applies Mathlib's uniqueness.")),
                    Paragraph(Text(
                    "The zero-tail result supplies the low side of the canonical inverse split."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-cylinder-of-shift"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder"
                    + ".prefixCylinder_of_shift"),
                H("A shifted canonical tail preserves the actual prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every internally nonadjacent binary prefix w and every natural tail t, "
                    + "the actual Zeckendorf digits of the literal sum of the prefix value and "
                    + "the seam-adjusted iterated substitution start agree with w. The proof "
                    + "uses the existing digit-shift theorem, proves the cross-seam gap, "
                    + "joins the canonical occupied-index lists, and applies uniqueness.")),
                    Paragraph(Text(
                    "This supplies forward inclusion for every actual canonical tail, including zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-cylinder-has-tail"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder"
                    + ".prefixCylinder_has_tail"),
                H("Every actual prefix member has one ordered canonical tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each legal prefix and every number satisfying its actual padded "
                    + "Zeckendorf digit predicate, the proof partitions occupied indices at "
                    + "the seam, excludes the forced adjacent bit, lowers the high indices "
                    + "to a canonical tail, and reconstructs the original number. "
                    + "The tail is unique and the parameter map is strictly increasing. "
                    + "The same digit partition proves the exact composition identity for "
                    + "the integer matrix [[0,1],[1,1]] and seed (-1,1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-cylinder-real-cutoff-discrepancy"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/Admissibility/ZeckendorfPrefixCylinder"
                    + ".prefixCylinder_real_cutoff_discrepancy"),
                H("Literal prefix counts have density and compatible refinement ratios"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every legal prefix, the literal finite cardinality below each "
                    + "nonnegative real cutoff differs from the golden-ratio main term by "
                    + "a fixed-prefix constant. The proof bijects the counted numbers with "
                    + "their unique canonical tail parameters and sandwiches the count "
                    + "between two real thresholds using the existing substitution-start "
                    + "error window. It derives natural density and the ratio for every "
                    + "legal appended prefix, including the empty extension. The "
                    + "denominator is eventually positive because its density is positive."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/Raw"))]));
}
