using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class FiniteMasksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/FiniteMasks.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite selection masks", H("Exact finite selection masks"),
        Blocks(Paragraph(Text("For every natural n, including zero, the bounded masks Fin(2^n) are in bijection with Boolean selections of Fin n. Bit functions are injective because all higher bits vanish; equality of the finite cardinalities gives surjectivity. Every actual finite subset is therefore represented, and the original supplier List.finRange filter count equals its canonical Finset cardinality. No bounded verification replaces a theorem over unbounded graph orders.")),
            Node("bits", "bits", "Exact declaration: def bits (n : ℕ) (mask : Fin (2 ^ n)) (v : Fin n) : Bool.", DescribeRole.Definition),
            Node("bits_injective", "bits injective", "Exact declaration: theorem bits_injective (n : ℕ) : Function.Injective (bits n).", DescribeRole.Theorem),
            Node("bits_surjective", "bits surjective", "Exact declaration: theorem bits_surjective (n : ℕ) : Function.Surjective (bits n).", DescribeRole.Theorem),
            Node("selection_mask", "selection mask", "Exact declaration: theorem selection_mask {n : ℕ} (S : Finset (Fin n)) : ∃ mask : Fin (2 ^ n), ∀ v, mask.val.testBit v.val = true ↔ v ∈ S.", DescribeRole.Theorem),
            Node("list_count", "list count", "Exact declaration: theorem list_count {n : ℕ} (p : Fin n → Bool) : ((List.finRange n).filter p).length = (Finset.univ.filter (fun v => p v = true)).card.", DescribeRole.Theorem)), []));
}
