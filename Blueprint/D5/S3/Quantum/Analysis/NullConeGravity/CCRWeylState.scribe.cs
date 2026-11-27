using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRWeylStateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weyl generators, Gaussian characteristic functions, and the countable vector-state folium of a GNS representation.",
        H("Weyl systems and state transport"),
        Blocks(
            Paragraph(Text("An alternating real bilinear form fixes the Weyl phase. The linear span of the generators is norm dense in the common C-star algebra. A positive normalized functional has a canonical cyclic vector in its GNS completion. Countable mixtures of vector states in this completion express excitability.")),
            Entry("weyl-system", "WeylSystem", "Weyl system",
                "The zero datum is sent to the algebra identity. The generators satisfy the phase-twisted addition law and the adjoint law, and have norm-dense complex linear span. The real bilinear form is alternating.", DescribeRole.Definition),
            Entry("gaussian-state", "IsGaussian", "Gaussian state",
                "The functional is normalized at the identity and takes each Weyl generator to the exponential of minus one half of the covariance quadratic form.", DescribeRole.Definition),
            Entry("excitability", "Excitability", "Excitability",
                "There exists a sequence of vectors in the reference GNS space whose squared norms sum to one and whose vector expectations sum to the target functional at every algebra element.", DescribeRole.Definition),
            Entry("gns-vacuum", "gnsVacuum", "Canonical GNS vector",
                "The vector represented by the algebra identity in the GNS completion.", DescribeRole.Definition),
            Entry("weyl-unitarity", "weyl_unitary", "Unitarity of the Weyl operators",
                "Multiplying a generator by its adjoint in either order gives the identity. Alternation makes the phase for opposite labels equal to one."),
            Entry("weyl-norm", "weyl_norm_le_one", "Weyl norm bound",
                "Each generator has norm at most one by the C-star identity and the unitary product law."),
            Entry("weyl-negation", "weyl_neg", "Weyl inversion",
                "The generator indexed by the negative datum equals the adjoint of the original generator."),
            Entry("vacuum-norm", "gnsVacuum_norm", "Unit GNS vacuum",
                "For a positive functional normalized at the identity the canonical GNS vector has norm one."),
            Entry("vacuum-expectation", "gnsVacuum_expectation", "GNS vacuum expectation",
                "The expectation of the represented algebra element in the canonical GNS vector is the original positive functional evaluated at that element."),
            Entry("state-bound", "state_norm_le", "Contractive state evaluation",
                "For a normalized positive functional, the absolute value at any algebra element is bounded by the element's norm. Cauchy–Schwarz and contractivity of the GNS representation give the bound."),
            Entry("state-continuity", "state_continuous", "State continuity",
                "The normalized positive functional is continuous in the C-star norm."),
            Entry("weyl-density", "weyl_determines", "Determination by Weyl coefficients",
                "Two continuous complex linear functionals agreeing at each generator agree on the entire algebra, by linearity and density."),
            Entry("gaussian-uniqueness", "gaussian_unique", "Uniqueness of Gaussian states",
                "Two Gaussian states on the same Weyl system with the same covariance are equal because their characteristic functions agree."),
            Entry("folium-summability", "folium_summable", "Summable vector expectations",
                "When the squared norms of the sequence sum to one, the vector expectations of each algebra element form a summable complex series."),
            Entry("folium-norm", "folium_norm_le", "Norm bound for the folium series",
                "The absolute value of the series at each algebra element is bounded by the norm of that element."),
            Entry("folium-functional", "foliumFunctional", "Continuous folium functional",
                "A sequence with total squared norm one defines the continuous complex linear functional obtained by summing its vector expectations.", DescribeRole.Definition),
            Entry("folium-weyl-determination", "excitability_of_weyl_coefficients", "Excitability from Weyl coefficients",
                "If the vector expectation series equals the target state at every Weyl generator, its continuous linear extension agrees with the target everywhere. The sequence therefore witnesses excitability."),
            Entry("folium-unitary-transfer", "excitability_of_unitary_intertwining", "Unitary transfer of vector decompositions",
                "A complex linear isometric equivalence intertwining the generator actions transports a sequence of vectors in the representation space back to the reference GNS space. Norms and generator expectations are preserved, giving excitability when the coefficients match."),
            Entry("reflexive-excitability", "excitability_refl", "Reflexive excitability",
                "For a normalized state, the sequence concentrated at the canonical GNS vector has total squared norm one and recovers the state at every algebra element."),
            Entry("excitability-pullback", "excitability_pullback", "Pullback of excitability",
                "A surjective unital star-algebra homomorphism identifies the pulled-back reference GNS completion isometrically with the original completion. Pulling back its vector witnesses gives excitability of the composed positive functionals."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
