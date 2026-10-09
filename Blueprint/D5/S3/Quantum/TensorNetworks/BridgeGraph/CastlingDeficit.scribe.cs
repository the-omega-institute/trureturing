using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class CastlingDeficitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/CastlingDeficit";
    private static readonly LibraryNoteRef Paper = LibraryNoteRef.Create("D5/L/QuantumBounds/gesmundo2025bridge");
    private static Formula Qualified(params Formula[] names) => Seq(Operatorname, Grp(names));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CastlingDeficit supplies the width-three bridge max-flow proof.",
        H("CastlingDeficit"), Blocks(
            Paragraph(Text("Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.")),
            Describe.Lean(DescribeId.Create("gls-castlingdeficit-castling-proved"),
                DeclarationHandle.Create(Owner + ".castling_proved"),
                H("castling_proved"), StatementSource.FromAuthor(Disp(Statement0())),
                AssessedProvenance.FromLiterature(Paper),
                Blocks(Paragraph(Text("The width-three castling transformation preserves the displayed quantum max-flow deficit by passing to common kernels and annihilator complements over a field, then applying the construction to complex maximizing assignments. QuantumMaxFlowMinCut.full_rank_of_descent uses this identity to transfer full rank from the descended dimensions; the identity does not assume the source Theorem 3.1."))),
                DescribeRole.Theorem))));

    private static Formula Statement0() =>
        Qualified(F.Id("QuantumMaxFlowBound"), Dot, F.Id("Castling"));

}
