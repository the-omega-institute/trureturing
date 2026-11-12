using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class PowerBaseDecimationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/PowerBaseDecimation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "PowerBaseDecimation", H("PowerBaseDecimation"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("An arbitrary commutative unital coefficient ring R is fixed. Intermediate binary decimations of levels below h give a finite indexed family from a literal base-2^h family, for every h at least one. Coefficients are fixed and no independence or invertibility is assumed. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("BaseFamily", "Exact source declaration: def BaseFamily (k : ℕ) (a : ℕ → R) : Prop := ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι; ∃ (b : ι → ℕ → R) (i0 : ι) (c : Fin k → ι → ι → R), (∀ n, b i0 n = a n) ∧ (∀ (r : Fin k) i n, b i (k * n + r.val) = ∑ j, c r i j * b j n)", DescribeRole.Definition),
            Node("powerBase_binary", "Exact source declaration: theorem powerBase_binary (h : ℕ) (hh : 1 ≤ h) (a : ℕ → R) (ha : BaseFamily (2 ^ h) a) : ArbitraryFamily a", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("powerbasedecimation-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(statement))), role);
}
