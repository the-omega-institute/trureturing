using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdTwistedChargeCocycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.";
    private static readonly LibraryNoteRef TwistedCharges =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete order-three lattice multiplier and the exact divisibility test for its moving-charge commutator.",
        H("Order-Three Twisted Lattice Charges"),
        Blocks(
            Paragraph(Text("Write ⟨a,b⟩ for the integral pairing on the native even charge lattice and use "
                + "ζ = exp(2πi/3). The Lean formulas for B and c allow any additive equivalence g. "
                + "The identification with Bakalov–Kac uses an order-three lattice isometry. "
                + "The moving-charge laws assume g preserves the pairing and g³ = 1, with N = 1 + g + g².")),
            Describe.Lean(
                DescribeId.Create("third-twisted-charge-factor"),
                DeclarationHandle.Create(Prefix + "B"),
                H("Product factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(TwistedCharges),
                Blocks(Paragraph(Text("For an order-three lattice isometry g, B(a,b) is the product factor "
                    + "of Bakalov–Kac, arXiv:math/0402315v3, equation (4.37). The factors are 3 to the power −⟨a,b⟩, "
                    + "(1 − ζ) to the power ⟨g a,b⟩, and (1 − ζ²) to the power ⟨g² a,b⟩. "
                    + "Each factor is a complex unit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-charge-multiplier"),
                DeclarationHandle.Create(Prefix + "c"),
                H("Charge multiplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(TwistedCharges),
                Blocks(Paragraph(Text("The Lean formula c(a,b) = ε(a,b)/B(a,b) uses the native lattice "
                    + "sign ε as a unit. For an order-three lattice isometry g, this is the coefficient "
                    + "of U_(a+b) in U_a U_b in equation (4.42) of arXiv:math/0402315v3."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-charge-commutator"),
                DeclarationHandle.Create(Prefix + "commutator_difference"),
                H("The moving-charge commutator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("For the order-three twist, equation (4.43) of arXiv:math/0402315v3 uses "
                    + "the order U_d U_b U_d⁻¹ U_b⁻¹. For d = a − g a, Lean proves that c(d,b)/c(b,d) is "
                    + "ζ to the power −⟨N a,b⟩. The swapped product factors use "
                    + "1 − ζ² = (1 − ζ)(−ζ⁻¹). The lattice sign then has an even exponent, and the "
                    + "remaining exponent differs from −⟨N a,b⟩ by a multiple of three. With the compatible "
                    + "normalized lift of (4.18)–(4.19), this phase cancels the conjugation phase from the "
                    + "fixed part N a / 3 in the quotient relation (4.46)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-charge-divisibility"),
                DeclarationHandle.Create(Prefix + "commutator_difference_eq_one_iff"),
                H("When the commutator is trivial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("The commutator equals one exactly when three divides ⟨N a,b⟩. "
                    + "Equivalently it is nontrivial precisely when that integer has nonzero residue "
                    + "modulo three. The test uses that ζ has order exactly three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-twisted-charge-descent"),
                DeclarationHandle.Create(Prefix + "commutator_difference_congr"),
                H("Dependence on the difference charge and orbit norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("The commutator is unchanged when a is replaced by a′ with "
                    + "a − a′ fixed by g and b is replaced by b′ with N b = N b′. The first condition "
                    + "preserves the difference charge. For the second, the isometry and g³ = 1 give "
                    + "⟨N a,b⟩ = ⟨a,N b⟩."))),
                DescribeRole.Theorem))));
}
