using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeFourCurrentTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite four-current traces on the original complete energy grades.",
        H("Finite Four-Current Trace"),
        Blocks(
            Definition("four-current-matchings", "PM4", "Ten labeled partial matchings",
                "The slots are Fin 4. There is one empty matching, six single-edge matchings, and three two-edge matchings. Every edge is ordered by its two slot labels; different edges remain distinct when their frequencies coincide."),
            Definition("four-current-matching-edges", "PM4.edges", "Labeled edge sets",
                "Each partial matching has its literal finite set of ordered pairs of distinct slots. The edge assignments in the coefficient are functions on this set, including its empty domain."),
            Definition("lattice-four-current-cycle", "actualFourCurrentCycleTrace", "Original finite four-current cycle trace",
                "For every original LatticeData D with positive-definite real Gram matrix, every i : Fin 4 → Fin D.rank and every n : Fin 4 → Nat, the trace is the finite complex LinearMap.trace on the original grade n(0) of B0 composed with B1 composed with B2 composed with B3. Here Ba is the literal existing actualCurrentBlock D (i(a)) (n(a)) (n(a+1)), with cyclic indices. The rightmost block acts first. All charge and oscillator labels of each full grade remain in the domain, and the current-label domain retains rank zero."),
            Definition("lattice-four-current-coefficient", "boundedFourCurrentCoefficient", "Bounded ten-matching coefficient",
                "The coefficient sums over the positive charge cutoff, the ten labeled matchings, bounded positive frequencies, two arc choices, bounded windings, and bounded residual grade, with guarded full-grade equalities and signed Gram and zero-mode factors."),
            Paragraph(Text("The internal source bridge identifies this literal four-block composition with the restriction and projection of the original neutral-mode word, using the original all-integer energy homogeneity theorem. Positivity proves that every negative original grade is zero. Finite rectangular trace cyclicity therefore applies across signed grades without an infinite trace or an imposed truncation.")),
            Paragraph(Text("For a word of total mode zero, the finite Heisenberg commutator gives T(N)-T(N-ell) as the three labeled contractions against the corresponding original two-mode word traces. For positive ell, a finite telescoping sum runs from k=0 through floor(N/ell); its terminal trace vanishes on a negative grade. A cyclic rotation is proved directly for the original four blocks. The remaining two-mode word is identified with the original two-block trace when both grades are nonnegative, and is zero when its intermediate grade is negative. The all-zero-mode trace is computed on the original full fiber as the charge-cutoff sum of the four charge weights times ordinary oscillator multiplicity.")),
            Paragraph(Text("The remaining finite theorem is the equality of the original four-current trace and boundedFourCurrentCoefficient for every grade quadruple. It requires the labeled matching bijections and exact arc and winding transport, including repeated frequencies. Four-point joint absolute convergence, thermal summation, modularity, sewing, Monster realization, and the full string/AdS program remain separate obligations.")))));

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
