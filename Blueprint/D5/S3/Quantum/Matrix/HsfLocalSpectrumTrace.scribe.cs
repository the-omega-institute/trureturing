using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfLocalSpectrumTraceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfLocalSpectrumTrace";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic and cubic trace normalization of actual noncommutative two-thirds CFC jets.",
        H("Actual CFC trace normalization"),
        Blocks(
            Describe.Lean(DescribeId.Create("hsf-local-spectrum-trace-normalization"),
                DeclarationHandle.Create(Module + ".actual_trace_normalization"),
                H("General finite Hermitian pencils"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On an arbitrary finite index type let Y be a positive "
                        + "definite complex Hermitian matrix and K an arbitrary Hermitian "
                        + "direction. Put P=CFC.rpow(Y,1/3), Q=K(P inverse) cubed, and let "
                        + "B_j be the actual jth derivative at zero of P inverse "
                        + "CFC.rpow(Y+tK,2/3) P inverse divided by j factorial. Then the "
                        + "complex trace identities are Tr B_2-(1/2)Tr(B_1 squared)="
                        + "-(1/3)Tr(Q squared) and Tr B_3-Tr(B_1 B_2)+(1/3)Tr(B_1 cubed)="
                        + "(2/9)Tr(Q cubed). These are identities of actual CFC derivatives, "
                        + "with no assumed trace formula or restriction on spectral levels.")),
                    Paragraph(Text("The proof first establishes finite degree-two and "
                        + "degree-three trace-log polynomials on ordered coefficient triples "
                        + "with identity constant term. Their values add under multiplication "
                        + "of triples and are invariant under fixed unit conjugation. The "
                        + "cube-root recurrences express the normalized linear pencil as "
                        + "a product of three conjugated triples, and the normalized "
                        + "two-thirds jet as a product of two. Eliminating the common "
                        + "trace-log values gives the displayed identities. Only cyclic "
                        + "trace is used; no matrix logarithm, determinant derivative, "
                        + "commutation, or differentiated eigenbasis is introduced.")),
                    Paragraph(Text("RpowPencilTaylor.cubeRoot_jet_recurrences and "
                        + "normalized_twoThirds_jet provide the actual ordered coefficients. "
                        + "Positive definiteness supplies the genuine inverse of P. "
                        + "HsfLocalSpectrumSupplier consumes these identities after "
                        + "diagonal balancing, where Q is similar to the balanced direction. "
                        + "The identities alone assert no inequality or HSF resolution."))),
                DescribeRole.Theorem),
            Paragraph(Text("The typed Reg attempt preserves the complete finite-index "
                + "telescope and both trace equations. Source-selection reconstruction "
                + "and the escape coordinate remain unfinished under "
                + "https://github.com/the-omega-institute/trureturing/issues/23103; "
                + "declared_validated is not claimed.")))));
}
