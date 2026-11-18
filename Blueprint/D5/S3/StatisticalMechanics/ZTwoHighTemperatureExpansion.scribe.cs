using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class ZTwoHighTemperatureExpansionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/ZTwoHighTemperatureExpansion.";

    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/SpinModels/wegner2014generalizedising");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity sums of plaquette products over 𝔽₂ keep the plaquette sets with given boundary.",
        H("The high-temperature expansion over 𝔽₂"), Blocks(
            Paragraph(Text(
                "Let E and P be finite sets and let M be a P × E matrix with entries in 𝔽₂ = ZMod 2. "
                + "Read E as a set of links, P as a set of plaquettes, and M p e = 1 as the statement "
                + "that the link e lies on the plaquette p. A configuration is a vector σ : E → 𝔽₂; "
                + "its value on the plaquette p is (M σ)_p, the sum mod 2 of σ over the links of p. "
                + "A vector S : P → 𝔽₂ is a set of plaquettes, its weight |S| is the number of p with "
                + "S p ≠ 0, and its boundary is the vector Mᵀ S : E → 𝔽₂.")),
            Describe.Lean(DescribeId.Create("ztwo-sign"),
                DeclarationHandle.Create(Module + "sgn"),
                H("The sign of an element of 𝔽₂"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a ring R and z in 𝔽₂, sgn_R(z) is 1 when z = 0 and −1 otherwise. In a "
                        + "commutative ring it satisfies sgn(a + b) = sgn(a) sgn(b), so sgn of a sum "
                        + "over a finite set is the product of the signs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ztwo-high-temperature-expansion"),
                DeclarationHandle.Create(Module + "sum_sgn_mul_prod_one_add_eq"),
                H("Plaquette sets with prescribed boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let R be a commutative ring, t ∈ R, and c : E → 𝔽₂. Then the sum over all "
                        + "configurations σ : E → 𝔽₂ of sgn(c · σ) · ∏_(p ∈ P) (1 + t · sgn((M σ)_p)) "
                        + "equals 2^|E| times the sum of t^|S| over the vectors S : P → 𝔽₂ whose "
                        + "boundary is Mᵀ S = c. Here c · σ is the dot product over 𝔽₂.")),
                    Paragraph(Text(
                        "Proof: expand each factor as 1 + t · sgn(x_p) = Σ_(b ∈ 𝔽₂) w(b) sgn(b x_p) "
                        + "with w(0) = 1 and w(1) = t, where x = M σ. Distributing the product over "
                        + "P turns it into the sum over S : P → 𝔽₂ of t^|S| sgn(S · M σ), and "
                        + "S · M σ = (Mᵀ S) · σ. Multiplying by sgn(c · σ) and exchanging the two "
                        + "sums leaves, for each S, the factor Σ_σ sgn((c + Mᵀ S) · σ). For a "
                        + "vector v : E → 𝔽₂ this sum factors over the coordinates as "
                        + "∏_(e ∈ E) (1 + sgn(v e)), which is 2^|E| when v = 0 and 0 otherwise. "
                        + "Since −c = c over 𝔽₂, the condition c + Mᵀ S = 0 is Mᵀ S = c.")),
                    Paragraph(Text(
                        "With c = 0 the right-hand side runs over the plaquette sets with empty "
                        + "boundary, the cycles of M; this is the high-temperature expansion of "
                        + "the partition function of a generalized Ising model with mod-2 incidence "
                        + "matrix, equations (24)–(27) of Wegner's notes, with plaquettes in the "
                        + "role of his bonds, links in the role of his sites, and t a common value "
                        + "of tanh K(b). A vector c outside the image of Mᵀ makes the sum vanish. A "
                        + "nonzero c inserts the product of the spins along c, for example the "
                        + "indicator of a closed loop for a Wilson loop; the expansion then keeps "
                        + "exactly the plaquette sets bounded by c, by the same argument.")),
                    Paragraph(Text(
                        "The identity is an algebraic statement about a finite incidence matrix "
                        + "over 𝔽₂ and does not use any lattice, dimension, thermodynamic limit "
                        + "or phase transition. Reading E and P as the links and plaquettes of a "
                        + "lattice gauge theory, and the identity as its strong-coupling expansion, "
                        + "is an interpretation of the variables only. The dual model of the "
                        + "duality transformation is not stated. No novelty is claimed: the "
                        + "expansion is classical, and the character sum over 𝔽₂-vectors used in "
                        + "its proof is the same orthogonality that underlies the MacWilliams "
                        + "identity for binary codes."))),
                DescribeRole.Theorem))));
}
