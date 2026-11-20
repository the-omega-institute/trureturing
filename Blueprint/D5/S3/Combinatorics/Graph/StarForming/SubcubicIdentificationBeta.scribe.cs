using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SubcubicIdentificationBetaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/SubcubicIdentificationBeta.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dissociation and single-counted port attainment", H("Dissociation and single-counted port attainment"),
        Blocks(Paragraph(Text("The original twelve-vertex port-state cap is applied to every actual block slice. Summing these slices counts each shared port twice and every other vertex once; the touched-block count is at most both the block count and twice the selected-port count. This proves two beta at most thirteen times the cell count. Alternating phases restrict exactly to the original attaining port witnesses and produce the matching lower bound. The full statement requires a fixed-point-free permutation and an explicit alternating Boolean phase, so odd cyclic sizes are not silently included.")),
            Node("label", "label", "Exact declaration: def label (next : Equiv.Perm I) (i : I) (v : Fin 12) : I × Fin 11.", DescribeRole.Definition),
            Node("blockSlice", "blockSlice", "Exact declaration: def blockSlice (next : Equiv.Perm I) (S : Finset (I × Fin 11)) (i : I) : Finset (Fin 12).", DescribeRole.Definition),
            Node("ports", "ports", "Exact declaration: def ports (S : Finset (I × Fin 11)) : Finset I.", DescribeRole.Definition),
            Node("touched", "touched", "Exact declaration: def touched (next : Equiv.Perm I) (S : Finset (I × Fin 11)) : Finset I.", DescribeRole.Definition),
            Node("block_cap", "block cap", "Exact declaration: theorem block_cap (next : Equiv.Perm I) (nf : ∀ i, next i≠i) (S : Finset (I × Fin 11)) (hS : IsKIndependent (graph next) 2 S) (i : I) : (blockSlice next S i).card≤6+(if i∈touched next S then 1 else 0).", DescribeRole.Theorem),
            Node("block_sum", "block sum", "Exact declaration: theorem block_sum (next : Equiv.Perm I) (S : Finset (I × Fin 11)) : ∑ i : I, (blockSlice next S i).card=S.card+(ports S).card.", DescribeRole.Theorem),
            Node("beta_upper", "beta upper", "Exact declaration: theorem beta_upper (next : Equiv.Perm I) (nf : ∀ i, next i≠i) : 2*beta (graph next) 2≤13*Fintype.card I.", DescribeRole.Theorem),
            Node("witness", "witness", "Exact declaration: def witness (phase : I → Bool) (x : I × Fin 11) : Prop.", DescribeRole.Definition),
            Node("witness_restriction", "witness restriction", "Exact declaration: theorem witness_restriction (next : Equiv.Perm I) (phase : I → Bool) (hp : ∀ i, phase (next i)= !(phase i)) (i : I) (v : Fin 12) : witness phase (label next i v) ↔ Subcubic.membership (Subcubic.portWitness (phase i) (phase (next i))) v=true.", DescribeRole.Theorem),
            Node("beta_exact", "beta exact", "Exact declaration: theorem beta_exact (next : Equiv.Perm I) (nf : ∀ i, next i≠i) (phase : I → Bool) (hp : ∀ i, phase (next i)= !(phase i)) : 2*beta (graph next) 2=13*Fintype.card I.", DescribeRole.Theorem)), []));
}
