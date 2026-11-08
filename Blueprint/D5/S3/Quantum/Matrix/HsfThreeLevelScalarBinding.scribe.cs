using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfThreeLevelScalarBindingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uncompiled mathematical source candidate: complex PSD3 cubic geometry and exact scalar coefficients.",
        H("HsfThreeLevelScalarBinding"),
        Blocks(
            Entry("scalar_p396_margin", "scalar p396 margin",
                "The cleared certificate establishes the P396 bound for the actual rho and Xi, with every denominator proved positive.", DescribeRole.Theorem),
            Entry("coefficient_domination", "coefficient domination",
                "For every positive triple, actual Xi is at most the Gram allowance of the actual three rho weights. The all-equal case and all other collisions are included.", DescribeRole.Theorem),
            Entry("closed_cubic_nonneg", "closed cubic nonneg",
                "For all positive p,q,r and every complex PSD three by three S, the actual closed cubic is nonnegative. The statement places no restriction on source rank, complex phases or level collisions.", DescribeRole.Theorem),
            Paragraph(Text("These are source candidates, not compiled or frozen results. "
                + "The scalar P396 source was inspected as fallible mathematical input; "
                + "its separate independent audit was not read. No novelty is claimed. "
                + "The commutant equality classification, original integral-to-moment bridge "
                + "and original HSF derivative/source bridge remain unformalized here. "
                + "Required Lean, axiom, Scribe and registration checks have not run.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsfthreelevelscalarbinding-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
