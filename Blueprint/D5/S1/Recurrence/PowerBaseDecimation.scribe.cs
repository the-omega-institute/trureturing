using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class PowerBaseDecimationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/PowerBaseDecimation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "PowerBaseDecimation",
        H("PowerBaseDecimation"),
        Blocks(
            Paragraph(Text("These common algebraic mechanisms use fixed coefficients on every natural input. There is no independence, invertibility, domain, characteristic-zero or Noetherian hypothesis. Cayley-Hamilton and linear-recurrence uniqueness are reused from the pinned Mathlib.")),
            Node("BaseFamily", "Every base-k digit acts by fixed coefficients on a literal finite indexed family. No basis, independence or invertibility is assumed.", DescribeRole.Definition),
            Node("powerBase_binary", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem))));

    private static string Exact(string name) => name switch
    {
        "BaseFamily" => "Exact source statement: def BaseFamily (k : ℕ) (a : ℕ → R) : Prop := ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι; ∃ (b : ι → ℕ → R) (i0 : ι) (c : Fin k → ι → ι → R), (∀ n, b i0 n = a n) ∧ (∀ (r : Fin k) i n, b i (k * n + r.val) = ∑ j, c r i j * b j n)",
        "powerBase_binary" => "Exact source statement: theorem powerBase_binary (h : ℕ) (hh : 1 ≤ h) (a : ℕ → R) (ha : BaseFamily (2 ^ h) a) : ArbitraryFamily a",
        _ => name
    };

    private static DocumentBlock Node(string name, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("powerbasedecimation-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose)), Paragraph(Text(Exact(name)))), role);
}
