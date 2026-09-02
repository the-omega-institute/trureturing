using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class LegacyRelativeEntropyBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen scalar quantum relative entropy is identified as the "
            + "finite support-conditioned branch.",
        H("Legacy Relative-Entropy Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("legacy-entropy-finite-branch"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/LegacyRelativeEntropyBoundary.legacy_quantumRelativeEntropy_eq_finite_branch"),
                H("The frozen scalar expression is the finite branch"),
                StatementSource.FromAuthor(BoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Lossless adapters identify the frozen local density-state and channel carriers with the canonical owners, in both directions, without touching the frozen node.")),
                    Paragraph(Text(
                        "Under these adapters the frozen real-valued trace-log expression is definitionally the finite branch of the support-aware construction.")),
                    Paragraph(Text(
                        "On an unsupported pair the corrected semantics is infinite while the frozen scalar stays finite; this states the exact semantic boundary of the legacy expression."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula BoundaryFormula() => Disp(Seq(
        Call("quantumRelativeEntropy",
            Call("toLegacy", Rho), Call("toLegacy", SigmaLower)),
        Sp, Eq, Sp,
        Call("finiteTraceLogRelativeEntropy", Rho, SigmaLower)));
}
