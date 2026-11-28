using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class DeSitterGravitonModesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/DeSitterGravitonModes.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The de Sitter tensor mode equation, normalized four-dimensional solutions and dimension selection.",
        H("De Sitter transverse-traceless graviton modes"),
        Blocks(
            Paragraph(Text("The tensor equation concerns individual bulk Fourier polarizations. "
                + "Appendix B.2 of Satishchandran and Sorce describes the Minkowski characteristic "
                + "graviton reference.")),
            Entry("tensor-exponent", "gravitonKappa", "Tensor rescaling exponent",
                "Half the tensor kinetic exponent, κ = (D − 2)/2.", DescribeRole.Definition),
            Entry("tensor-rescaling", "ds_graviton_tt_rescaled_ode", "Exact tensor rescaling",
                "For D ≥ 2, H > 0 and t < 0, set Ω = −1/(Ht) and v = Ω^κ h. "
                + "The operator (Ω^(D − 2)h′)′ + Ω^(D − 2)k²h equals Ω^κ[v″ + "
                + "(k² − κ(κ + 1)/t²)v]. The identity uses differentiability of h at negative "
                + "times and of its derivative at t."),
            Entry("scalar-potential", "ds_graviton_tt_scalar_potential", "Minimally coupled scalar potential",
                "For D ≥ 4, H > 0 and t < 0, the scalar conformal mass shift at zero bare mass "
                + "and curvature coupling yields the same potential k² − κ(κ + 1)/t²."),
            Entry("bd-mode", "ds4GravitonBDMode", "Four-dimensional Bunch–Davies mode",
                "Multiply exp(−ikt) by 1 − i/(kt) and divide by √(2k).", DescribeRole.Definition),
            Entry("bd-equation", "ds4_graviton_bd_mode_solves_ode", "Exact mode equation",
                "For k > 0 and t < 0 the mode satisfies v″ + (k² − 2/t²)v = 0."),
            Entry("bd-wronskian", "ds4_graviton_bd_wronskian", "Canonical Wronskian",
                "For k > 0 and t < 0, v times the conjugate of v′ minus the conjugate of v times v′ equals i."),
            Entry("bd-power", "ds4_graviton_bd_power", "Squared metric mode amplitude",
                "For H > 0, k > 0 and t < 0, |v/Ω|² = H²(1 + k²t²)/(2k³)."),
            Entry("bd-limit", "ds4_graviton_bd_superhorizon_limit", "Superhorizon power",
                "For H > 0 and k > 0 the squared amplitude tends to H²/(2k³) as t approaches zero "
                + "from below. Multiplying the limit by k³ gives a scale-independent amplitude."),
            Entry("tensor-space", "GravitonTT", "Tensor polarization space",
                "Use the existing symmetric trace-free space on a screen of dimension D − 2.",
                DescribeRole.Definition),
            Entry("count", "gravitonPolarizationCount", "Tensor polarization count",
                "Use the natural-number formula (D − 2)(D − 1)/2 − 1.", DescribeRole.Definition),
            Entry("screen-count", "gravitonPolarization_eq_screenSTF", "Equivalent screen count",
                "The count equals the existing screen dimension D(D − 3)/2."),
            Entry("screen-finrank", "finrank_gravitonTT", "Rank of the trace-free screen",
                "For D ≥ 2 the screen has rank (D − 2)(D − 1)/2 − 1. "
                + "The two-dimensional spacetime boundary has an empty screen and rank zero."),
            Entry("count-examples", "graviton_polarizations_three_four_five", "Polarizations in three, four and five dimensions",
                "The three counts are zero, two and five, respectively."),
            Entry("weyl-tide", "graviton4_weyl_screen_coordinates", "Weyl tidal coordinates in dimension four",
                "Half the real and imaginary parts of the complex Weyl tide are the first diagonal "
                + "and off-diagonal entries of the real trace-free screen tide."),
            Entry("propagation", "graviton_propagating_iff", "Propagation threshold",
                "The tensor polarization count is positive exactly when D ≥ 4."),
            Entry("scalar-gravity", "scalar_nullDiamond_and_propagating_gravity_iff", "Gravity and scalar summability",
                "The conjunction of D ≥ 4 and leading null-diamond angular weight summability holds "
                + "exactly in dimensions four and five."),
            Entry("maxwell-selection", "unique_dimension_four_of_nullDiamond_and_conformalMaxwell", "Selection by Maxwell invariance",
                "Intersect the gravity and scalar summability window with Maxwell invariance at every "
                + "positive conformal scale. The intersection consists of dimension four."),
            Entry("proca-selection", "unique_dimension_four_of_graviton_nullDiamond_and_procaConformal", "Selection by Proca curvature cancellation",
                "A positive tensor polarization count, scalar leading-weight summability and zero "
                + "transverse Proca curvature coefficient occur together exactly in dimension four."),
            Entry("joint-selection", "grand_unification_unique_dimension_four", "Joint Weyl, scalar, Maxwell and Hodge selection",
                "For D ≥ 3, positive Weyl rank, summable scalar leading weights, invariant Maxwell "
                + "weight at every positive scale, and Hodge complementary degree two for 2-forms "
                + "hold together exactly when D = 4."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
