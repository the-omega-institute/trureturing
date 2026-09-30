using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class ZeckendorfPrefixCylinderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual padded Nat.zeckendorf prefix values and the forward canonical seam splice.",
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
                    "This establishes the exact zero-tail digits of the prefix value. "
                    + "The inverse seam split, occupied-index coordinate identity, "
                    + "literal real-cutoff count, density, and extension ratio remain open."))),
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
                    "This is the forward inclusion in source 116.4. It does not prove the "
                    + "inverse, bijection, coordinate identity, or 116.5 count and density."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/Raw"))]));
}
