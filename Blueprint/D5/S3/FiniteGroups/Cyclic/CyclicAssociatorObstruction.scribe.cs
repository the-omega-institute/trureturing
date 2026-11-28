using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Cyclic;

internal sealed class CyclicAssociatorObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/Cyclic/CyclicAssociatorObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic product of an ambient associator excludes elements of nonzero carry type from subgroups that trivialize it.",
        H("Cyclic Associator Obstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("cyclic-product-telescoping"),
                DeclarationHandle.Create(Prefix + "cyclicProduct_mul_coboundary"),
                H("The cyclic product is invariant under coboundaries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite-order element g, multiply the values of a three-cochain α at "
                    + "(g,g^i,g) for i from zero through orderOf(g) minus one. With trivial action on an abelian "
                    + "multiplicative coefficient group, each of the two coboundary ratios telescopes by rotating i by one. "
                    + "The product is therefore invariant under multiplication by the coboundary of an arbitrary two-cochain."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-product-type-phase"),
                DeclarationHandle.Create(Prefix + "cyclicProduct_eq_type_phase"),
                H("The cyclic product gives the type phase"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let g and ζ both have exact order n greater than one. Assume the pullback of α "
                    + "along a ↦ g^a.val equals the carry phase of type t times a two-cochain coboundary. The carry phase "
                    + "is ζ raised to the least nonnegative representative of w(t,a,b,c). Telescoping removes the coboundary, "
                    + "and summing the carry exponents modulo n gives t. "
                    + "Thus the cyclic product is ζ raised to t.val. For ζ = exp(2πi/n), the carry phase is equation (2.13) "
                    + "of Evans–Gannon, arXiv:1804.11145v1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonzero-type-exclusion"),
                DeclarationHandle.Create(Prefix + "not_mem_of_nonzero_type"),
                H("Nonzero type excludes subgroup membership"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the ambient α restricts to a two-cochain coboundary on a subgroup H, every g in H "
                    + "has cyclic product one. Under the pullback comparison, exact order n of ζ makes this impossible for "
                    + "nonzero t in ZMod n. Both two-cochains are arbitrary."))),
                DescribeRole.Theorem),
            Paragraph(Text("Evans–Gannon, arXiv:1804.11145v1, equation (2.14), gives the generator-flux conformal weight ρ "
                + "congruent to t/n² modulo 1/n after removing the central-charge term from the T phase. "
                + "For the c = 48 P48q order-three case, a weight in 16/9 + (1/3)ℤ gives type 1 in this convention. "
                + "Applying the obstruction to a group or VOA requires an external comparison of the actual ambient associator "
                + "on the cyclic generator with the carry phase up to coboundary. Corollary 2 supplies the coboundary "
                + "restriction condition for the extension subgroups in the Evans–Gannon setting.")))));
}
