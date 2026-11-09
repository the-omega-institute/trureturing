using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PredictiveMerging;

internal sealed class BlackwellDubinsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PredictiveMerging/BlackwellDubins.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/blackwelldubins1962merging");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute continuity makes predictive probability laws merge on the entire infinite future along almost every history.",
        H("Blackwell–Dubins predictive merging"), Blocks(
            Paragraph(Text("Fix any universe and any family of measurable spaces Xᵢ indexed by the natural numbers. The history space Ω is their dependent product, equipped with its product sigma-algebra. At time n the past space is the product of Xᵢ over i ≤ n, and the future space is the product of X_(n+1+j) over all natural j. These are arbitrary measurable coordinate spaces; they need no topology or common carrier.")),
            Describe.Lean(DescribeId.Create("blackwell-dubins-coordinate-split"),
                DeclarationHandle.Create(Prefix + "split"),
                H("The actual prefix and the entire tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every such family and every natural n, split is the measurable equivalence from Ω to Pastₙ × Futureₙ whose first component at history ω has coordinate i equal to ωᵢ for every i ≤ n, and whose second component has coordinate j equal to ω_(n+1+j). The inverse joins these two disjoint sets of coordinates. The auxiliary tailIndex identifies j with n+1+j in the natural indices strictly above n; tailReindex applies this identification to the dependent product. The past projection is exactly the first component of split."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blackwell-dubins-normalized-predictive-kernel"),
                DeclarationHandle.Create(Prefix + "changedKernel"),
                H("A probability row at every past"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("For probability measures P and Q with Q absolutely continuous with respect to P, let q(ω) be the real value of the Radon–Nikodym derivative dQ/dP at ω, with the extended value infinity sent to zero by toReal. Set f = ofReal(q). At time n put hₙ(u,v) = f(splitₙ⁻¹(u,v)) and rₙ(u) = ∫ hₙ(u,v) κₙ(u,dv), where this integral is extended and nonnegative. These are splitDensity and rowMass.")),
                    Paragraph(Text("The set goodRows consists of pasts u with 0 < rₙ(u) < infinity. On this set rowDensity is hₙ(u,v)/rₙ(u); on every other row it is the constant one. The construction changedKernel is κₙ.withDensity(rowDensity). In particular, both zero-mass and infinite-mass rows retain the original κₙ row. The definition uses no selected default future point."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blackwell-dubins-predictive-change-of-measure"),
                DeclarationHandle.Create(Prefix + "predictive_change_of_measure"),
                H("Transport of the chosen predictive versions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("For every universe, every dependent family Xᵢ of arbitrary measurable spaces, every pair of probability measures P,Q on Ω with Q absolutely continuous with respect to P, and every chosen sequence of Markov kernels κₙ from Pastₙ to Futureₙ, assume only that P.map(splitₙ) = P.map(pastₙ) ⊗ κₙ for every n. Then q is measurable, nonnegative everywhere and P-integrable, its integral is one, P.withDensity(ofReal(q)) = Q, and q is strictly positive Q-almost everywhere.")),
                    Paragraph(Text("For every n, rₙ is measurable and the uncurried rowDensity is measurable. The rowDensity is finite at every pair (u,v), its κₙ(u)-integral is one for every u, and ηₙ = changedKernel(P,Q,n,κₙ) is a Markov kernel. The Q past marginal is P.map(pastₙ).withDensity(rₙ), the P past integral of rₙ is one, and the genuine Q predictive law holds: Q.map(splitₙ) = Q.map(pastₙ) ⊗ ηₙ.")),
                    Paragraph(Text("Writing Fₙ for the product-prefix sigma-algebra Filtration.piLE n, the real function rₙ(pastₙ ω).toReal equals E_P[q | Fₙ](ω) P-almost everywhere. The good-row condition holds Q.map(pastₙ)-almost everywhere for every n. No statement asserts finite rₙ or integrability of the original density on every row.")),
                    Paragraph(Text("The finite real representative agrees with the extended Radon–Nikodym derivative P-almost everywhere. The measure Radon–Nikodym theorem supplies the density law and absolute continuity transfers its exceptional set to Q. Kernel integration gives measurability of rₙ. Positive finite rows normalize by cancellation, while all other rows retain the original probability row.")),
                    Paragraph(Text("Fubini and the supplied P predictive law give the Q split density law. Infinite row masses form a P-past null set. On zero-mass rows the nonnegative density is zero κₙ(u)-almost everywhere, so the factorization rₙ(u) times rowDensity equals hₙ(u,v) almost everywhere under the original composition product. The withDensity composition-product identity reconstructs the Q split law, and its first marginal identifies the Q past law. Zero rows are null under that new marginal, and absolute continuity transfers the infinite-row null set. The mapped-Radon–Nikodym conditional-expectation identity identifies rₙ.toReal with the prefix conditional mean."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("blackwell-dubins-bounded-overlap-numerator"),
                DeclarationHandle.Create(Prefix + "overlapNumerator"),
                H("The bounded common-part numerator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every P,Q, n and kernel κₙ, write cₙ(u) = rₙ(u).toReal. The real scalar overlapNumerator aₙ(u) is ∫ min(q(splitₙ⁻¹(u,v)), cₙ(u)) κₙ(u,dv). For the probability kernels in the merging theorem the integrand lies between zero and the finite constant cₙ(u), so this bounded row integral is defined without an all-row integrability assumption on q itself."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blackwell-dubins-full-predictive-merging"),
                DeclarationHandle.Create(Prefix + "blackwell_dubins_predictive_merging"),
                H("Merging over all measurable infinite-future events"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("For every universe, every family Xᵢ of arbitrary measurable spaces, every pair of probability measures P,Q on the product history space with Q absolutely continuous with respect to P, and every chosen sequence κₙ of Markov kernels from the actual prefix space Pastₙ to the entire future space Futureₙ satisfying P.map(splitₙ) = P.map(pastₙ) ⊗ κₙ for every n, there exists a sequence ηₙ of Markov kernels on exactly the same spaces such that Q.map(splitₙ) = Q.map(pastₙ) ⊗ ηₙ for every n. There is one Q-null exceptional set of full histories outside which, as n tends to infinity, the supremum over all measurable C ⊆ Futureₙ of |κₙ(pastₙ ω)(C) − ηₙ(pastₙ ω)(C)| tends to zero.")),
                    Paragraph(Text("The supremum is the real supremum of the range of these measurable-event discrepancies. It is event total variation, equal to one half of the full variation norm for probability measures. The order of choices is for every chosen κ sequence, followed by the existence of η. The exceptional set is chosen for the whole convergence assertion on a full history; it is not selected separately for each future event.")),
                    Paragraph(Text("Choose the normalized sequence η from the preceding construction. The prefix fields Fₙ increase to the full product sigma-algebra: each coordinate evaluation is measurable in its own prefix field, and those evaluations generate the product field. Upward conditional-expectation convergence and the scalar row identity therefore give cₙ(pastₙ ω) → q(ω) P-almost everywhere.")),
                    Paragraph(Text("Set yₙ(ω) = min(q(ω), cₙ(pastₙ ω)). This sequence is measurable, nonnegative, bounded by the single integrable function q, and converges P-almost everywhere to q. Apply joint conditional dominated convergence to E_P[yₙ | Fⱼ] and take the cofinal diagonal j = n. Its limit is q because the supremum field is the full product field. The supplied composition-product law identifies the diagonal conditional means with aₙ(pastₙ ω): push integrals on prefix-measurable sets to the past marginal, integrate the future row by Fubini, and pull back by the actual measurable split. Conditional-expectation uniqueness gives the identification. Thus both aₙ(pastₙ ω) and cₙ(pastₙ ω) tend to q(ω).")),
                    Paragraph(Text("On each good row the individual-law Radon–Nikodym common part of κₙ(u) and ηₙ(u), relative to κₙ(u), has density min(1,hₙ(u,v)/rₙ(u)). Its real mass is aₙ(u)/cₙ(u). The common-part mass identity gives the exact uniform equality between the full measurable-event supremum and 1 − aₙ(u)/cₙ(u). This equality is an identity of measures on the entire future space and has no exceptional set indexed by future events.")),
                    Paragraph(Text("Intersect the countably many scalar conditional-mean identities and good-row assertions with their convergence events, transfer the P-almost-everywhere conclusions through Q absolutely continuous with respect to P, and include q > 0 Q-almost everywhere. At a remaining single history the numerator and denominator converge to the same strictly positive q, so their ratio tends to one. The row overlap identity makes the entire measurable-event supremum tend to zero on that one common Q-full set.")),
                    Paragraph(Text("There is no finite-state, common-coordinate-type, countably-generated, standard-Borel, strictly-positive-density, equivalence-of-measures, Markov-process, stationarity or finite-horizon premise. No normalization, merging or likelihood-convergence assumption is supplied. The kernel factorization for the chosen P sequence is the sole predictiveness premise. The proof uses individual probability laws on arbitrary measurable future spaces and makes no measurability assertion about the family of event-TV suprema.")),
                    Paragraph(Text("This is the Main Theorem of Blackwell and Dubins, Merging of Opinions with Increasing Information, page 883, with predictive conditional laws as defined on page 882. The bounded-overlap calculation is the common-part form of the density argument on pages 884–885, including equations (13)–(14). The joint conditional dominated-convergence input is their Theorem 2, page 883."))),
                DescribeRole.Theorem))));
}
