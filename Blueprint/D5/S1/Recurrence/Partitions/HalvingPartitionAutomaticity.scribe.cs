using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionAutomaticityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionAutomaticity", H("HalvingPartitionAutomaticity"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("Actual weighted SourceLists counts are excluded from finite canonical MSDF machines, even with unconstrained zero output, in every base 2^h with h≥1. Finite nonzero rings also use the adopted genuine all-word LSDF machine equivalence. The ordinary remainder a(n)%q is connected to its actual ZMod q cast for every q≥2, including composite moduli. No canonical/padding claim is inferred merely by renaming the finite-kernel predicate. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("weighted_not_canonical_automatic", "Exact source declaration: theorem weighted_not_canonical_automatic {R : Type*} [CommRing R] [Nontrivial R] (t : R) (h : ℕ) (hh : 1 ≤ h) : ¬ CanonicalAutomatic (2 ^ h) (powerBase_ge_two h hh) (weightedCount t)", DescribeRole.Theorem),
            Node("weighted_not_lsdf_automatic", "Exact source declaration: theorem weighted_not_lsdf_automatic {R : Type} [CommRing R] [Nontrivial R] [Fintype R] (t : R) (h : ℕ) (hh : 1 ≤ h) : ¬ IsKAutomaticSequence (2 ^ h) (weightedCount t)", DescribeRole.Theorem),
            Node("count_mod_not_canonical", "Exact source declaration: theorem count_mod_not_canonical (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) : ¬ CanonicalAutomatic (2 ^ h) (powerBase_ge_two h hh) (fun n => count n % q)", DescribeRole.Theorem),
            Node("count_mod_not_lsdf", "Exact source declaration: theorem count_mod_not_lsdf (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) : letI : NeZero q := ⟨by omega⟩; ¬ IsKAutomaticSequence (2 ^ h) (fun n => (count n : ZMod q))", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitionautomaticity-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(statement))), role);
}
