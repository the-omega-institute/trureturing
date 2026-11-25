using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class AffineNineBasisConcreteDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineBasisConcrete";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric unitary bases in powers of nine.",
        H("Symmetric unitary bases in powers of nine"),
        Blocks(Describe.Lean(
            DescribeId.Create("unitary-basis-power-nine"),
            DeclarationHandle.Create(Module + ".exists_f9Basis"),
            H("Orthogonal unitaries span the symmetric subspace"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("n"), Sp, Eq, Sp, new Formula.Power(D(9), F.Id("d")), Comma, Quad,
                Call("hs", new Formula.Subscript(F.Id("b"), F.Id("i")),
                    new Formula.Subscript(F.Id("b"), F.Id("j"))),
                Sp, Eq, Sp, F.Id("n"), new Formula.Subscript(DeltaLower, Seq(F.Id("i"), F.Id("j")))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(DefinitionDsl.Text(
                "For every natural exponent d at least two, there exists a basis b over the complex numbers of the entire space "
                + "of n by n complex symmetric matrices. It has n(n+1)/2 elements, each of which is unitary, "
                + "and the pairing formula holds for all basis indices i and j. "
                + "The construction applies the order-nine seed and the edge labeling to affine lines."))),
            DescribeRole.Theorem))));
}
