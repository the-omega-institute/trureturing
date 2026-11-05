using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

// Purity bounds and attaining mixed densities on the five-row matrix family.
internal sealed class FiveRowMaximumPurityDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Desc(string name, string title, string statement, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(
            DescribeId.Create("appt-five-row-maximum-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowMaximumPurity." + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/tran2026spectralappt")),
            Blocks(Paragraph(Text(statement + " " + prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-row APPT maximum-purity assembly over arbitrary complex density matrices.",
        H("Five-row APPT maximum purity"), Blocks(
            Paragraph(Text("For each n >= 5, consider complex matrices on Fin 5 times Fin n that are positive semidefinite, have complex trace one, and remain PPT after every global unitary. Purity is the real part of trace(rho*rho). The upper bound and the attaining density use the same dimension and the same piecewise value.")),
            Desc("bound", "Piecewise exact value",
                "bound(n) is (5*n+8)/(5*n+2)^2 for n <= 18 and 5/(24*n) for n >= 19, with the natural product 5*n formed before coercion to Real.",
                "The definition is used under n >= 5 in the public claim, giving the two ranges 5 <= n <= 18 and n >= 19.", DescribeRole.Definition),
            Desc("claim", "Arbitrary-density maximum and attainment",
                "For every natural n with 5 <= n, every complex matrix rho indexed by Fin 5 times Fin n that is positive semidefinite, has complex trace one, and is APPT has real trace-square purity at most bound(n); and there exists an actual rho with those same properties and purity exactly bound(n).",
                "APPT retains its all-global-unitary predicate. The matrix hypotheses allow repeated and zero eigenvalues and singular densities; no spectral, scalar, extraction, moment or diagonalization premise is assumed.", DescribeRole.Definition),
            Desc("result", "One spectral reduction and two attaining branches",
                "result proves claim by invoking QuadbitQuintitMaximumPurity.diagonal_spectral_reduction exactly once on e = finProdFinEquiv. It keeps the returned ordered nonnegative l, sum l = 1, the APPT labelled diagonal and the trace-square identity. The n <= 18 branch invokes FiveRowP1Physical.physical_upper; the n >= 19 branch invokes FiveRowP2Physical.physical_upper_from_exact_bridges.",
                "The first equality witness is normalizedRay(Pi.single (0,0) 1), supplied by normalized_ray; the second is ContractionAttainment.fiveRowDensity n, supplied by five_row_attainment. Both upper consumers use the single spectrum returned by the reduction.", DescribeRole.Theorem),
            Paragraph(Text("In the small branch, actual_to_hyp derives every P1 necessary inequality from the same actual APPT spectrum. The top-three tail estimate gives the charge disjunction, and scalar_bound covers the closed real interval 10 <= j <= 5n-15, including n = 5 and j = 10. The physical transfer retains arbitrary mass and the U^2 energy scale, with zero U handled before division. The returned trace-square equality transports the resulting spectral bound to the original rho.")),
            Paragraph(Text("With v = Pi.single (0,0) 1, normalizedRay(v) = (I+2vv*)/(5*n+2). This is a full-rank mixed density, not the pure matrix vv*. Its eigenvalues are 3/(5*n+2) once and 1/(5*n+2) with multiplicity 5*n-1. Its purity is (9+(5*n-1))/(5*n+2)^2 = (5*n+8)/(5*n+2)^2.")),
            Paragraph(Text("The contraction density is fiveRowDensity n = (4I+2P)/(24*n), where P is the coordinate projector of rank 2*n. The density is full-rank and mixed: its eigenvalues are 1/(4*n) with multiplicity 2*n and 1/(6*n) with multiplicity 3*n. Thus its purity is 2*n/(4*n)^2 + 3*n/(6*n)^2 = 5/(24*n).")),
            Paragraph(Text("The normalized-ray and five-row contraction families are known constructions. The Ahiable--Kothakonda--Winter inner-polytope spectra and the prior n >= 118 literature/formal boundary are prior context; the inner-polytope formulas and attainers are distinct from the unrestricted APPT upper bound.")),
            Paragraph(Text("The two displayed spectra each have total mass one. Their positive eigenvalues give actual mixed-density equality witnesses in the respective ranges, while the upper-bound claim continues to quantify over all PSD trace-one APPT matrices, including singular ones."))
        )));
}
