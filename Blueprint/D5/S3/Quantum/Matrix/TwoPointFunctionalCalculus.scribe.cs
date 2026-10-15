using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class TwoPointFunctionalCalculusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared existing functional calculus for self-adjoint matrix involutions.",
        H("Two-point functional calculus"), Blocks(
            Describe.Lean(DescribeId.Create("involution-spectrum"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus.involution_spectrum"),
                H("Spectrum of a self-adjoint involution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite index type n with Fintype and DecidableEq instances, "
                    + "a self-adjoint complex matrix H with H H = I has real spectrum "
                    + "contained in {1,-1}. This is the existing proof extracted from the "
                    + "cumulant-Renyi refutation, consumed there and by the Hiai TILDE classification."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-point-cfc"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/TwoPointFunctionalCalculus.two_point_cfc"),
                H("Exact affine involution calculus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite index type n with Fintype and DecidableEq instances, "
                    + "any self-adjoint complex matrix H with H H = I, every real function f, and all "
                    + "real a and b, the actual matrix CFC of a I + b H equals "
                    + "((f(a+b)+f(a-b))/2) I + ((f(a+b)-f(a-b))/2) H. The finite spectrum "
                    + "requires no global continuity assumption on f. Both existing consumers "
                    + "reuse the one extracted proof. This refactor claims no independent mathematical gain."))),
                DescribeRole.Theorem))));
}
