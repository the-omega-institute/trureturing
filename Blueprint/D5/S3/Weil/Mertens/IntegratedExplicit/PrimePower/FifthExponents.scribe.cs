using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class FifthExponentsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/FifthExponents";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common Chebyshev exponent sum",
        H("Support at a shared real cutoff"),
        Blocks(Describe.Lean(
            DescribeId.Create("common-exponent-sum"),
            DeclarationHandle.Create(Owner + ".psi_sub_roots_eq_sum"),
            H("The square, cube and fifth-root cutoffs"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For t ≥ 2 choose N at least the natural floor of log(t)/log(2). "
                + "Subtract θ(t) and the square, cube and fifth ψ cutoffs from ψ(t). "
                + "Their common finite support gives a sum over exponents k from 6 through N. "
                + "The term θ(t^(1/k)) has coefficient 1 minus the three divisibility indicators "
                + "for 2, 3 and 5. All coefficients from degree two through degree five vanish."))),
            DescribeRole.Theorem))));
}
