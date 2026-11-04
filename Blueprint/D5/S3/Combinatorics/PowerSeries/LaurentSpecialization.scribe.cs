using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PowerSeries;

internal sealed class LaurentSpecializationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PowerSeries/LaurentSpecialization.";
    private static readonly LibraryNoteRef Question = LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Support-controlled specialization of Laurent coefficient series.", H("LaurentSpecialization"), Blocks(
            Paragraph(Text("For a source monomial q^n T^k, shift the Laurent row by T^n. On the cone k >= -n the row becomes an ordinary polynomial, so evaluation at q^r followed by outer evaluation at q^(a+1) is legitimate. The final degree is (a+1+r)n+rk. Truncation is used only to define a continuous additive map on the ambient space; multiplicativity is proved on admissible inputs by the injective polynomial-to-Laurent map. The weighted Jacobi module is the live consumer. This construction reuses Mathlib LaurentPolynomial.trunc and PowerSeries.eval₂Hom, with their complete discrete-coefficient topology. It does not assert an unrestricted Laurent substitution.")),
            Node("0", "lift", "Shift row n by T^n and take its nonnegative polynomial part.", DescribeRole.Definition),
            Node("1", "Admissible", "The shifted series lies in the image of genuine polynomial coefficients; this records the support cone.", DescribeRole.Definition),
            Node("2", "lift_of_map", "A polynomial preimage is reconstructed exactly by truncation.", DescribeRole.Theorem),
            Node("3", "map_lift", "For admissible input, lifting loses no Laurent coefficient.", DescribeRole.Theorem),
            Node("4", "admissible_one", "The identity series belongs to the support cone.", DescribeRole.Theorem),
            Node("5", "admissible_mul", "The support condition is closed under multiplication.", DescribeRole.Theorem),
            Node("6", "lift_mul", "The polynomial lift is multiplicative on admissible inputs.", DescribeRole.Theorem),
            Node("7", "lift_one", "The lift preserves the identity, used by finite products.", DescribeRole.Theorem),
            Node("8", "liftAdd", "The lift is additive on the full ambient coefficient space.", DescribeRole.Definition),
            Node("9", "continuous_lift", "Each lifted row depends continuously on just its original row.", DescribeRole.Theorem),
            Node("10", "diagonal", "Evaluate the polynomial variable at q^r and the outer variable at q^(a+1).", DescribeRole.Definition),
            Node("11", "specialize", "The composite row shift and positive evaluation map.", DescribeRole.Definition),
            Node("12", "specializeAdd", "The continuous additive specialization used to transfer complete integer sums.", DescribeRole.Definition),
            Node("13", "specialize_mul", "Admissible products specialize multiplicatively.", DescribeRole.Theorem),
            Node("14", "specialize_one", "The specialization preserves one, including empty finite products.", DescribeRole.Theorem),
            Node("15", "continuous_specialize", "The positive weighted evaluation preserves genuine limits.", DescribeRole.Theorem),
            Node("16", "lift_monomial", "A supported monomial becomes the exact ordinary polynomial monomial of degree n+k.", DescribeRole.Theorem),
            Node("17", "admissible_monomial", "The explicit inequality n+k >= 0 supplies the required polynomial preimage.", DescribeRole.Theorem),
            Node("18", "specialize_monomial", "The exact weighted degree and the original rational coefficient are preserved.", DescribeRole.Theorem),
            Node("19", "admissible_sub", "The support condition is closed under subtraction.", DescribeRole.Theorem),
            Node("20", "admissible_prod", "Every finite product of supported factors remains supported.", DescribeRole.Theorem),
            Node("21", "specialize_prod", "The supported specialization commutes with arbitrary finite products.", DescribeRole.Theorem),
            Node("22", "specialize_factor", "A supported Laurent Euler factor becomes its exact weighted Euler factor.", DescribeRole.Theorem),
            Node("23", "admissible_factor", "The positivity condition on a Laurent factor is checked before specializing.", DescribeRole.Theorem)
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("laurentspecialization-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Question),
            Blocks(Paragraph(Text(text))), role);
}
