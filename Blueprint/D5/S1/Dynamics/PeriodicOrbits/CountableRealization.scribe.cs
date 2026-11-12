using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.PeriodicOrbits;

internal sealed class CountableRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual countable cycles realize all positive indices simultaneously.",
        H("Countable and signed realization"), Blocks(
            Paragraph(Text("This construction extends the existing finite divisor-table supplier to a single all-length carrier. It supplies the cycle-realization step required by the complete Jaidee manuscript, but the actual block valuation/transform identification, bounded half-residue arithmetic and formal zeta Euler identities need their own proofs. See the complete scope and attribution in "), Ref("D5/L/Scale/jaidee2026blockdold"), Text(". Registration is unfinished under issue 29392; no declared_validated status is claimed.")),
            Describe.Lean(DescribeId.Create("countable-countable-and-locally-finite"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/CountableRealization.countable_and_locally_finite"),
                H("countable_and_locally_finite"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(Paragraph(Text("For every natural multiplicity function c, the single carrier of triples (positive length d, copy j in Fin(c d), phase in ZMod d) is countable. The rotation preserves length and copy and advances the phase. At each positive time n the actual fixed set is finite, via an explicit equivalence to the existing finite divisor carrier for n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("countable-fixed-card"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/CountableRealization.fixed_card"),
                H("fixed_card"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(Paragraph(Text("For every c and every positive n, the cardinality of the actual fixed set of the nth iterate equals the sum over d dividing n of d*c(d). The same carrier and permutation are used at all indices. At time zero an infinite carrier need not have a finite fixed set; no zero-time claim is made."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("countable-delta-fixed-card"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/CountableRealization.delta_fixed_card"),
                H("delta_fixed_card"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(Paragraph(Text("At each positive n the integer Mobius transform of the actual fixed-point counts equals n*c(n). This uses exact Mobius inversion, not an assumed orbit-count formula."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("countable-realization-iff"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/CountableRealization.realization_iff"),
                H("realization_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(Paragraph(Text("A natural sequence a is realized at every positive time by one canonical countable-cycle permutation if and only if every positive-index integer Mobius transform is nonnegative and divisible by its index. The converse chooses c(d)=delta(a,d)/d using nonnegativity and exact divisibility. This goes beyond a separate finite-prefix or divisor-table model for each bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("countable-finite-carrier-of-support"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/CountableRealization.finite_carrier_of_support"),
                H("finite_carrier_of_support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(Paragraph(Text("If the nonzero multiplicities are supported on divisors of one positive exponent M, the whole carrier is finite by an explicit equivalence to the finite divisor carrier. This supplies actual finite carriers when bounded sample arithmetic establishes finite support."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("countable-signed-realization"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/CountableRealization.signed_realization"),
                H("signed_realization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(Paragraph(Text("Every integer sequence whose Mobius transforms are divisible by their positive indices is the difference of the actual fixed counts of two single countable-cycle permutations, simultaneously at all positive times. The positive and negative parts of the integral orbit quotients give the two multiplicity functions. This does not assert positivity or finite total support."))), DescribeRole.Theorem))));
}
