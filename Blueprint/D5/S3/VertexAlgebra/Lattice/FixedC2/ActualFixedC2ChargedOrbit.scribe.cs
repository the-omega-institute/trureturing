using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.FixedC2;

internal sealed class ActualFixedC2ChargedOrbitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descent in charge energy leaves finitely many fixed charge orbits spanning the quotient.",
        H("Finite Charge Support in the Fixed Leech C2 Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-fixed-orbit-word-span"),
                DeclarationHandle.Create(Prefix + "fixed_charge_orbit_eq_span_words"),
                H("Symmetrized words span the full fixed orbit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pair a word at charge c with its sign transform at -c. "
                    + "Such words span the fixed subspace supported on that orbit by expanding the "
                    + "oscillator polynomials in their monomial basis and applying the fixed "
                    + "projection. When c=0 the two charges coincide, and the projection retains "
                    + "the even words."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-charged-quadratic-word-length"),
                DeclarationHandle.Create(Prefix + "fixed_quadratic_charged_word_length"),
                H("The leading term of a quadratic mode on a charged word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual neutral quadratic (-1)-mode acting on a fixed "
                    + "charged word has the two-letter concatenation as its leading term. In the "
                    + "other terms the inner nonnegative mode acts by annihilation or a charge "
                    + "scalar, and the outer mode creates at most one oscillator. Thus the "
                    + "corrections are shorter words supported on the same orbit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-fixed-orbit-ground-and-singles"),
                DeclarationHandle.Create(Prefix + "fixed_charge_orbit_le_of_ground_and_singles"),
                H("The ground and the single oscillators generate under quadratic modes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A subspace containing the fixed ground and all single "
                    + "oscillators and stable under quadratic (-1)-modes contains the entire orbit. "
                    + "Induction uses the two base lengths zero and one, then creates a pair from "
                    + "a shorter word and subtracts the shorter corrections."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-leech-orbit-outside-short-step"),
                DeclarationHandle.Create(Prefix + "leech_fixed_charge_orbit_step_outside_short"),
                H("The signed basis step reduces the entire fixed orbit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any Leech charge c outside the closed Gram-coordinate "
                    + "box, the signed basis step gives an orbit of strictly smaller charge energy. "
                    + "The ground reduction into that orbit extends to all single oscillators and "
                    + "then to every word by quadratic stability. The entire upper orbit maps "
                    + "into the lower orbit image modulo intrinsic C2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-c2-leech-finite-charge-support"),
                DeclarationHandle.Create(Prefix + "leech_fixed_c2_finite_charge_support"),
                H("The short charge orbits span the intrinsic quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The short charges are exactly those satisfying "
                    + "|B(e_i,c)| ≤ G(i,i) for every basis direction i. The Gram-coordinate map is "
                    + "injective by positive definiteness, so this closed integer box gives a "
                    + "finite set. Strong induction on charge energy reduces each orbit image to "
                    + "the span of those short orbit images. Each fixed state is a finite sum of "
                    + "symmetrized charge components, so this span is the whole quotient."))),
                DescribeRole.Theorem))));
}
