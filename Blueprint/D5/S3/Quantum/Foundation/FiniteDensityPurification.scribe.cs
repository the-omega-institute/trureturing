using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;
internal sealed class FiniteDensityPurificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite density state has a canonical normalized purification with exact reduced marginal.",
        H("Finite Density Purification"), Blocks(Describe.Lean(
            DescribeId.Create("finite-density-purification"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteDensityPurification.purification"),
            H("Canonical purification with exact marginal and matrix"),
            StatementSource.FromAuthor(Disp(Seq(Psi, Eq, Operatorname, Grp(F.Id("purify")), Open, Operatorname, Grp(F.Id("toMState")), Open, Rho, Close, Close, Comma, Sp, Operatorname, Grp(F.Id("marginalRight")), Open, Operatorname, Grp(F.Id("toDensity")), Open, Operatorname, Grp(F.Id("pure")), Open, Psi, Close, Close, Close, Eq, Rho, Dot))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/meiburg2026ssa")), Blocks(
                Paragraph(Text("For a density state ρ on a finite index type a with DecidableEq, purification returns the normalized ket ψ = MState.purify (toMState ρ) on a × a, bundled with marginalRight (toDensity (MState.pure ψ)) = ρ. The same-matrix conversion toMState uses the shared supplier carrier; toDensity returns to the project's canonical density states.")),
                Paragraph(Text("The returned subtype also certifies CStarMatrix.ofMatrix.symm (toDensity (MState.pure ψ)).1 = Matrix.vecMulVec ψ (fun i => star (ψ i)). Normalization is part of Ket. Singular states are included: the construction imposes no invertibility hypothesis.")),
                Paragraph(Text("This is the project's DensityState construction using the attributed Physlib MState.purify and MState.purify_spec from States/Mixed/MState at immutable revision 2725b6f621901d4cd330869e9b77105045c1582e. The supplier theorem states (MState.pure σ.purify).traceRight = σ for MState σ; the project construction transports that identity to marginalRight. The original copyright and Apache-2.0 notices remain in the consumed Lean sources."))),
            DescribeRole.Definition))));
}
