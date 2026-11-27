using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class DimensionSelection4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/DimensionSelection4D.";

    private static readonly LibraryNoteRef Angular =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");
    private static readonly LibraryNoteRef Petrov =
        LibraryNoteRef.Create("D5/L/LieTheory/petrov1954weyl");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero trace-free null screen, angular trace summability, and even dimension select four dimensions.",
        H("Four-dimensional selection by curvature and angular summability"),
        Blocks(
            Entry("algebraic-curvature-rank", "finrank_algebraicCurvature", "Dimension of algebraic curvature",
                "For D ≥ 3 the real dimension is D²(D² − 1)/12. Pair skew symmetry and exchange symmetry reduce the tensor "
                + "to a symmetric array on increasing pairs. The Bianchi expression is alternating, so its increasing quadruple "
                + "coordinates suffice. The Bianchi map splits by assigning each quadruple to the pairing of its first two "
                + "and last two indices. Rank–nullity subtracts the number of quadruples from the symmetric pair-array dimension.", Petrov),
            Entry("ricci-section", "ricci_right_inverse", "A section of Ricci contraction",
                "In D ≥ 3, contracting the Kulkarni–Nomizu product of the metric with a symmetric form P gives "
                + "(D − 2)P + tr_g(P)g. For a prescribed Ricci form T, take P = (T − tr_g(T)g/(2(D − 1)))/(D − 2). "
                + "Its contraction is T."),
            Entry("weyl-rank", "finrank_weyl", "Dimension of Weyl curvature",
                "For D ≥ 3 the Ricci kernel has real dimension D(D + 1)(D + 2)(D − 3)/12. "
                + "The right inverse of Ricci contraction subtracts precisely D(D + 1)/2 symmetric coordinates.", Petrov),
            Entry("screen-rank", "finrank_screenSTF", "Dimension of the trace-free screen",
                "The screen has D − 2 coordinates for D ≥ 3. Trace on its symmetric forms is onto by taking a scalar multiple of the screen metric. The trace kernel has real dimension D(D − 3)/2, positive precisely from D = 4."),
            Entry("weyl-screen-tide", "screen_tide_weyl_invariance", "The trace-free tide is the Weyl tide",
                "In the standard Lorentz null frame, contract on the generator e₀ + e₁ and the transverse coordinate screen. "
                + "The Ricci lift shifts the tide by a scalar multiple of the screen metric. The Weyl tide has zero trace, "
                + "so subtracting the average trace leaves exactly that tide."),
            Entry("four-dimensional-ricci", "curvature4_ricci", "Ricci agrees in the four-dimensional oriented basis",
                "Evaluate the general curvature form in pair order (01, 02, 03, 23, 31, 12). "
                + "The sign of the reversed pair 31 gives the Bianchi trace condition and the Ricci contraction agrees entrywise.", Petrov),
            Entry("four-dimensional-ranks", "four_dimensional_compatibility", "Four-dimensional curvature, Weyl, and screen ranks",
                "The general curvature and Weyl dimensions agree with the four-dimensional oriented spaces, with ranks 20 and 10. "
                + "The real trace-free screen rank is 2."),
            Entry("angular-summability", "summable_angularMode_iff", "Summability of the angular model",
                "The sum of (ℓ + 1)^(D − 7) over nonnegative integers ℓ converges exactly for D ≤ 5. "
                + "The shift removes the index zero, and the real power-series criterion requires exponent strictly below −1.", Angular),
            Entry("angular-comparison", "angular_trace_summable_iff_of_eventually_comparable", "Two-sided comparison",
                "If a nonnegative angular contribution is eventually bounded above and below by positive multiples "
                + "of the model term, the same summability threshold holds. The comparison is a hypothesis on the physical contributions.", Angular),
            Entry("four-dimensional-selection", "unique_dimension_four_of_weyl_modular_chiral", "Selection by even dimension",
                "A positive screen dimension gives D ≥ 4. Summability gives D ≤ 5. Of these dimensions only four is even, "
                + "and dimension four satisfies all three conditions.", Angular),
            Entry("hodge-degree-selection", "unique_dimension_four_of_weyl_modular_hodge", "Selection by Hodge degree",
                "The complementary degree of a two-form is D − 2. Requiring this degree to equal two gives D = 4, "
                + "where the screen is positive and the angular model is summable."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        params LibraryNoteRef[] sources) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(sources),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
