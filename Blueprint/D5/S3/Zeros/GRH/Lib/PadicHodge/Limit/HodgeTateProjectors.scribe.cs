using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Limit;

internal sealed class HodgeTateProjectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hodge Tate Projectors", H("Hodge Tate Projectors"),
        Blocks(
            Paragraph(Text("Crystalline cocycles modulo p^m: continuity, kernel of reduction, stability under corestriction. Hodge–Tate projectors of crystalline lattices with bounded weights have rank-free bounded denominators.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Limit/HodgeTateProjectors.exists_uniform_trace_sum_eq_jump"),
                H("exists_uniform_trace_sum_eq_jump"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Uniform reading of jumps, for j of open image. Some t in C_p, depending only on j, n, w, works for all crystalline lattices T with jumps in [0,n], bases ε and x in T: there are z_s, |z_s| ≤ 1, with t Σ z_s γ(tr u(ε_s)) the multiplicity of the jump w of r at γ, whenever r is potentially crystalline, u(gy) = r(g)u(y), u(x) = 1.")))))));
}
