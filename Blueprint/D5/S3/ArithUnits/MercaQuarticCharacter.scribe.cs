using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MercaQuarticCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MercaQuarticCharacter.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/mazhang2026quartic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every prime r congruent to five modulo eight, the actual complex Dirichlet "
            + "character of order four with value i at two exists uniquely. It is primitive "
            + "and odd. Its literal unit kernel has index four and cardinality (r-1)/4.",
        H("The Normalized Quartic Character"),
        Blocks(
            Paragraph(Text("All moduli are natural numbers; primality is Mathlib's Nat.Prime. "
                + "Characters are actual DirichletCharacter values on ZMod r with complex "
                + "coefficients, extended by zero at nonunits. Order is multiplicative order. "
                + "Odd means chi(-1)=-1, and primitive means that the conductor equals r. "
                + "The finite character statements include r=5. The historical actual-field "
                + "class-number formula has the separate restriction r>5.")),
            Node("existence", "Existence, normalization and uniqueness",
                "normalized_quartic_exists_unique", DescribeRole.Theorem,
                "For every prime r with r mod 8 equal to 5, there exists a complex Dirichlet "
                    + "character chi modulo r with order exactly four, chi(2)=i, primitive "
                    + "conductor and odd parity. Every complex Dirichlet character psi modulo "
                    + "r with order four and psi(2)=i equals this chi. Choose an auxiliary "
                    + "generator g of the full finite unit group. Two is nonsquare, so its "
                    + "exponent in g is odd. Construct the character with chi(g)=i and choose "
                    + "it or its cube to orient the value at two. The generator's half-order "
                    + "power is minus one, which proves oddness since (r-1)/2 is 2 modulo 4. "
                    + "An odd exponent is invertible modulo four, proving uniqueness. "
                    + "The nonprincipal character at a prime modulus is primitive. "
                    + "Two need not be a generator."),
            Node("character", "The canonical normalized character", "character",
                DescribeRole.Definition,
                "For a prime r and a proof that r mod 8 is 5, character r is a choice of "
                    + "the preceding unique normalized character. Uniqueness removes dependence "
                    + "on the auxiliary generator. The coefficient field is the complex numbers."),
            Node("kernel", "The actual unit kernel", "kernel", DescribeRole.Definition,
                "Kernel r is the kernel of character r restricted to the actual unit group "
                    + "of ZMod r, with values in the complex unit group. It consists of "
                    + "precisely the units on which the character is one."),
            Node("structure", "Kernel cardinality, index and omitted minus one",
                "kernel_structure", DescribeRole.Theorem,
                "For every prime r congruent to 5 modulo 8, the canonical character has "
                    + "order four, value i at two, primitive conductor, odd parity and the "
                    + "uniqueness property above. Its actual kernel K has cardinality "
                    + "(r-1)/4 and index four, and minus one does not belong to K. "
                    + "The image is exactly the four complex fourth roots of unity: every "
                    + "value is a fourth root, and powers of the unit two realize all four "
                    + "roots. The kernel-index formula gives the cardinality. Oddness "
                    + "excludes minus one."))));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("merca-quartic-character-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
