using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodSwitchingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Fano switching quotient", H("The actual Fano switching quotient"),
        Blocks(Paragraph(Text("The twenty-one binary Fano flags define the linear outer-product invariant Phi. Symbolic switching annihilation, an explicit preimage for every traceless matrix, a spanning-tree kernel argument and rank-nullity prove that signings modulo vertex switches are linearly isomorphic to the eight-dimensional traceless matrix space. This is the actual quotient map; graph-switching isomorphisms, conjugacy classification and connectedness transfer remain separate obligations.")),
            Node("F2", "F2", "Exact declaration: abbrev F2.", DescribeRole.Definition),
            Node("Mat", "Mat", "Exact declaration: abbrev Mat.", DescribeRole.Definition),
            Node("Signing", "Signing", "Exact declaration: abbrev Signing.", DescribeRole.Definition),
            Node("Switches", "Switches", "Exact declaration: abbrev Switches.", DescribeRole.Definition),
            Node("coordinate", "coordinate", "Exact declaration: def coordinate (p : Fin 7) (j : Fin 3) : F2.", DescribeRole.Definition),
            Node("flags", "flags", "Exact declaration: def flags : Fin 21 → Fin 7 × Fin 7.", DescribeRole.Definition),
            Node("flags_complete", "flags complete", "Exact declaration: theorem flags_complete : ∀ p l : Fin 7, (∑ j : Fin 3, coordinate p j * coordinate l j) = 0 ↔ ∃! e : Fin 21, flags e = (p,l).", DescribeRole.Theorem),
            Node("phi", "phi", "Exact declaration: def phi : Signing →ₗ[F2] Mat.", DescribeRole.Definition),
            Node("switching", "switching", "Exact declaration: def switching : Switches →ₗ[F2] Signing.", DescribeRole.Definition),
            Node("trace_phi", "trace phi", "Exact declaration: theorem trace_phi (s : Signing) : Matrix.trace (phi s) = 0.", DescribeRole.Theorem),
            Node("phi_switching", "phi switching", "Exact declaration: theorem phi_switching (s : Switches) : phi (switching s) = 0.", DescribeRole.Theorem),
            Node("phi_preimage", "phi preimage", "Exact declaration: theorem phi_preimage (M : Mat) (hM : Matrix.trace M = 0) : phi (preimage M) = M.", DescribeRole.Theorem),
            Node("traceless", "traceless", "Exact declaration: def traceless : Submodule F2 Mat.", DescribeRole.Definition),
            Node("range_phi", "range phi", "Exact declaration: theorem range_phi : LinearMap.range phi = traceless.", DescribeRole.Theorem),
            Node("traceless_dimension", "traceless dimension", "Exact declaration: theorem traceless_dimension : Module.finrank F2 traceless = 8.", DescribeRole.Theorem),
            Node("kernel_phi_eq_switching", "kernel phi eq switching", "Exact declaration: theorem kernel_phi_eq_switching : LinearMap.ker phi = LinearMap.range switching.", DescribeRole.Theorem)), []));
}
