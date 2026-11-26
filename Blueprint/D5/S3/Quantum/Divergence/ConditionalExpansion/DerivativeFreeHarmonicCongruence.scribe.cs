using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class DerivativeFreeHarmonicCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.";

    private static readonly LibraryNoteRef ConditionalExpansion =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    private static readonly LibraryNoteRef Doeblin =
        LibraryNoteRef.Create("D5/L/Divergence/georgehirchenuradhawilde2026doeblin");

    private static DocumentBlock.Describe Definition(string name, string id, string title, string description) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonality of modified Jordan ranges gives a quadratic and a harmonic bound for a positive matrix congruence.",
        H("Derivative-free harmonic congruence"),
        Blocks(
            Definition("harmonicB", "harmonic-congruence-sector-mass", "Sector mass",
                "For square complex matrices X and Q, let X₊ and X₋ denote the positive and negative parts. "
                + "The sector matrix B is Q X₊ Q + (I − Q) X₋ (I − Q)."),
            Definition("harmonicDelta", "harmonic-congruence-input-gap", "Input gap",
                "Write n(X) for the real trace of the positive part of −X. "
                + "The input gap δ is n(X) plus the real trace of QX."),
            Definition("harmonicValue", "harmonic-congruence-output-gap", "Congruence gap",
                "For square matrices S, X and Q on the same finite index type, "
                + "the congruence gap is n(SXS) plus the real trace of QSXS."),
            Describe.Lean(
                DescribeId.Create("harmonic-congruence-all-real-quadratic"),
                DeclarationHandle.Create(Prefix + "derivative_free_harmonic_congruence"),
                H("The quadratic bound for every real parameter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(ConditionalExpansion, Doeblin),
                Blocks(
                    Paragraph(Text("On any finite decidable index type, take square complex matrices W, X and Q. "
                        + "Suppose W is positive definite, X is Hermitian, Q is Hermitian and idempotent, and W commutes with Q. "
                        + "Put S = W¹ᐟ² and c equal to the real trace of W⁻¹B. For every real t, "
                        + "the congruence gap is at least 2tδ − t²c. The bound includes singular X and zero input gap.")),
                    Paragraph(Text("The algebraic proof uses "
                        + "M₊ = S(I − Q) + tS⁻¹Q, M₋ = SQ + tS⁻¹(I − Q), and D = S − tS⁻¹. "
                        + "The modified filters have product tI. The ranges of M₊√X₊ and M₋√X₋ are orthogonal, "
                        + "since the two Jordan square roots multiply to zero. Test the negative trace with the "
                        + "orthogonal projection onto the second range. Removing the vanishing modified-filter terms "
                        + "and contracting by the projection and its complement bounds the two trace losses by the real trace "
                        + "of D²B. Subtracting this from the real trace of WB gives the quadratic, "
                        + "using W − D² = 2tI − t²W⁻¹ and the identity between the real trace of B and δ.")),
                    Paragraph(Text("Hirche, George, Nuradha and Wilde define the conditional expansion coefficient in "
                        + "arXiv:2608.27171v1, Definition 3, Eq. (2.42). Their Proposition 9 reduces the trace-distance "
                        + "expansion infimum to orthogonal pairs. Their Eq. (5.2) gives the positive-part "
                        + "variational principle, applied here to the negative of the congruence. "
                        + "George, Hirche, Nuradha and Wilde give the complete expansion bound for equal reference "
                        + "marginals in arXiv:2503.22823v3, Proposition 33, Eq. (6.56). "
                        + "The matrix argument retains the reference-effect term through the congruence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("harmonic-congruence-optimized-quotient"),
                DeclarationHandle.Create(Prefix + "derivative_free_harmonic_congruence_optimized"),
                H("The optimized harmonic bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same matrix hypotheses, assume δ > 0. "
                    + "The sector matrix B is positive semidefinite and has real trace δ, so it is nonzero. "
                    + "Since W⁻¹ is positive definite, its trace pairing c with B is strictly positive. "
                    + "Substituting the maximizing real parameter t = δ/c in the quadratic lower bound gives "
                    + "the congruence gap at least δ²/c."))),
                DescribeRole.Theorem))));
}
