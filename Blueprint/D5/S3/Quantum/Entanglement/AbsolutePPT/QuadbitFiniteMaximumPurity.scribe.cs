using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QuadbitFiniteMaximumPurityDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Desc(string name, string title, string statement, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("appt-quadbit-finite-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitFiniteMaximumPurity." + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/ahiablekothakondawinter2026geometry")),
            Blocks(Paragraph(Text(statement))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual four-by-n APPT maximum purity for every natural n from seven through thirteen.",
        H("Finite rank-one APPT maximum"), Blocks(
            Desc("purityValue", "Rank-one purity value",
                "For every natural n, purityValue(n)=(4n+8)/(4n+2)^2 in the real numbers. Natural multiplication is performed before coercion. The formula and attaining spectrum are due to Ahiable–Kothakonda–Winter, arXiv:2608.03390v2, Corollary 6.4 and equation (44).", DescribeRole.Definition),
            Desc("physicalPurities", "Purities of actual density matrices",
                "For every natural n, physicalPurities(n) is the set of real p for which an actual complex matrix rho on Fin 4 times Fin n is positive semidefinite, has complex trace one, satisfies APPT, and has real part of trace(rho*rho) equal to p. APPT means that every global unitary conjugate has positive semidefinite second-factor partial transpose. No spectral relaxation replaces this physical domain.", DescribeRole.Definition),
            Desc("basisZero", "Product basis origin",
                "For every natural n with 7<=n, basisZero(n) is the actual product index (0,0) in Fin 4 times Fin n. Its second coordinate is constructed from the positive dimension; its proof argument is suppressed here.", DescribeRole.Definition),
            Desc("attainingDensity", "Density from a normalized rank-one ray",
                "For every natural n with 7<=n, attainingDensity(n) is normalizedRay(Pi.single(basisZero(n),1))=(I+2|00><00|)/(4n+2). The normalization is the existing physical ray construction. It is also the basis diagonal with entry 3/(4n+2) at the origin and 1/(4n+2) elsewhere.", DescribeRole.Definition),
            Desc("physical_purity_upper_bound", "Unconditional physical upper bound",
                "For every natural n with 7<=n<=13 and every complex matrix rho indexed by Fin 4 times Fin n, positive semidefiniteness of rho, trace(rho)=1 and APPT(rho) imply re(trace(rho*rho))<=(4n+8)/(4n+2)^2. One actual sorted spectrum l:Fin(4n) to Real is obtained by diagonal_spectral_reduction with finProdFinEquiv. Its nonnegative entries sum to one and its actual labelled diagonal remains APPT. That same l supplies both literal K1 and K2 through diagonal_necessary_both, the first-six/last-ten inequality through uniform_rank_four_necessary, and the trace-square identity. No independent spectral choices are combined. The length-52 endpoint actual_k1_l4_length52_purity_bound has value 5/243, needs no K2 assumption and applies to arbitrary ordered spectra. rank_four_endpoint_interval transports this endpoint down to length 24; substituting N=4n and k=N-16 covers every required dimension 28 through 52. The endpoint is proved internally, rather than left as a hypothesis.", DescribeRole.Theorem),
            Desc("physical_finite7_maximum", "Actual attained maximum and real supremum",
                "For every natural n with 7<=n<=13 the real denominator 4n+2 is positive. Every complex positive-semidefinite trace-one APPT rho on Fin 4 times Fin n has purity at most purityValue(n). There exists an actual rho equal both to normalizedRay(Pi.single(basisZero(n),1)) and to the diagonal with entry 3/(4n+2) at basisZero(n) and 1/(4n+2) elsewhere; it is positive semidefinite, trace one, APPT and has purity exactly purityValue(n). The physical purity set is nonempty, bounded above and has real supremum purityValue(n). The existing normalized_ray theorem proves the physical properties for the unit product vector, and normalized_basis_diagonal supplies the literal diagonal. Membership of its purity and the universal upper bound give the attained real supremum.", DescribeRole.Theorem),
            Paragraph(Text("Ordering is non-strict: ties, zero eigenvalues and singular necessary matrices remain allowed. K1, K2 and L4 are used only as necessary conditions, with no PSD sufficiency assertion or extremal spectral ansatz. The formula and attainer are published prior work; the unrestricted upper bound is the additional inference supplied by the endpoint and dimension transfer. This finite theorem does not settle n>=14, the general-dimensional conjecture, uniqueness of maximizers or world priority.")))));
}
