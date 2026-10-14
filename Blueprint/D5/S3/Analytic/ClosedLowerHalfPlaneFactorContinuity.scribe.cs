using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class ClosedLowerHalfPlaneFactorContinuityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Factorization =
        LibraryNoteRef.Create("D5/L/Fourier/ephremidze2010polynomial");
    private static readonly LibraryNoteRef RootTopology =
        LibraryNoteRef.Create("D5/L/Topology/curgus2006roots");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Supplied monic closed lower half-plane factors vary continuously on arbitrary topological parameter spaces.",
        H("Closed Lower Half-Plane Factor Continuity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("closed-lower-factor-unique"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/ClosedLowerHalfPlaneFactorContinuity.closed_lower_factor_unique"),
                H("Uniqueness including real root multiplicities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Factorization),
                Blocks(
                    Paragraph(Text("Let p and q be monic complex polynomials whose roots all have "
                        + "nonpositive imaginary part. Write p# for coefficient conjugation, so "
                        + "p#(z)=conj(p(conj(z))). If p p# = q q#, then p=q. No equal-degree "
                        + "premise, positivity of the degree, or simple-root hypothesis is needed.")),
                    Paragraph(Text("Conjugation transports root multiplicity, and multiplication "
                        + "adds it. For a root strictly below the real axis, its conjugate has "
                        + "positive imaginary part and has multiplicity zero in each supplied "
                        + "factor. At a real root the product multiplicity is twice the factor "
                        + "multiplicity. Above the real axis both factor multiplicities are zero. "
                        + "The product identity therefore equates all factor multiplicities. "
                        + "Monicity and factorization over the complex numbers identify the polynomials.")),
                    Paragraph(Text("This is the scalar monic consequence of Ephremidze's "
                        + "real-line polynomial spectral factorization uniqueness, Theorem 2 "
                        + "of arXiv:1011.3777v1. That theorem allows real zeros and fixes the "
                        + "factor up to a constant unitary multiplier; monicity fixes that multiplier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continuous-coeff-of-monic-closed-lower-factor"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/ClosedLowerHalfPlaneFactorContinuity.continuous_coeff_of_monic_closed_lower_factor"),
                H("Continuity on an arbitrary parameter space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(RootTopology),
                Blocks(
                    Paragraph(Text("Let A be any topological space, m any natural number, and "
                        + "H and B functions from A to complex polynomials. Assume every B(a) "
                        + "is monic of natural degree exactly m, all its roots have imaginary "
                        + "part at most zero, H(a)=B(a)B(a)#, and every coefficient of H depends "
                        + "continuously on a. Then every coefficient of B depends continuously "
                        + "on a. Neither first-countability nor any separation axiom is imposed on A.")),
                    Paragraph(Text("Repeated roots, collisions on the real axis and degree zero "
                        + "are included. The proof never chooses root labels continuously. For "
                        + "a convergent sequence in coefficient space, the coefficient-sum Cauchy "
                        + "bound places the roots in one fixed closed disk. Compactness of the "
                        + "finite product of these disks gives a convergent subsequence of root "
                        + "tuples. The limit remains closed lower, and the conjugate product "
                        + "identity passes to the limit. The uniqueness theorem identifies the "
                        + "limiting product with the supplied factor.")),
                    Paragraph(Text("To handle arbitrary A, record only coefficients zero through "
                        + "2m of H and give their image the subspace topology in a finite complex "
                        + "coefficient space. Select a supplied factor at each image point. "
                        + "The product degree is 2m, so these coordinates determine H completely; "
                        + "boundary uniqueness makes the selected factor independent of the chosen "
                        + "representative. The sequence argument proves continuity on this metrizable "
                        + "image. Composition with the continuous coefficient map from A gives the "
                        + "claimed continuity without a countability assumption on A.")),
                    Paragraph(Text("The topological antecedents are Curgus and Mascioni's "
                        + "Theorems 2.4 and 4.4 on continuous inverses and fixed-degree root "
                        + "multisets. The result combines classical compactness with closed-boundary "
                        + "factor uniqueness; no worldwide novelty claim is made. The Lean proof "
                        + "directly reuses the root enumeration and product coefficient continuity "
                        + "from LowerHalfPlaneFactorContinuity and the coefficient-sum root bound "
                        + "from CompactSeparatedRealContinuation.")),
                    Paragraph(Text("The factors are supplied. No factor existence, continuous "
                        + "root labeling, quantitative modulus, anchored telescoping-square "
                        + "construction, instrument or operator continuity, stationary limit, "
                        + "physical realization or native quantum field statement is asserted."))),
                DescribeRole.Theorem))));
}
