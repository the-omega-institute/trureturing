using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class IntegerRecoveryStructureSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/IntegerRecoveryStructureSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CRT recovery and the spectral layer compose, but similarity retains a witness.",
        H("Integer Recovery And Structure Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-residues-agree"),
                Handle("localResiduesAgree"),
                H("Local residue agreement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two bounded integer values have identical prime-power residue readouts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bounded-integer-trace-data"),
                Handle("boundedIntegerTraceData"),
                H("Bounded integer trace data"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The trace-code family uses the exact Fin N carrier from the CRT theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("initial-power-traces-agree"),
                Handle("initialPowerTracesAgree"),
                H("Initial power-trace agreement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first n positive matrix power traces agree."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("newton-characteristic-polynomial-bridge"),
                Handle("NewtonCharacteristicPolynomialBridge"),
                H("Newton characteristic-polynomial bridge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This explicit premise records the forward trace-to-charpoly step, "
                        + "which the imported saturation theorem does not provide."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-power-traces-agree"),
                Handle("positivePowerTracesAgree"),
                H("All positive power-trace agreement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every positive matrix power has the same trace."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-residue-recovery-is-exact"),
                DeclarationHandle.Create(Prefix + "local_residue_recovery_is_exact"),
                H("The bounded CRT layer has no residual"),
                StatementSource.FromAuthor(LocalRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under pointwise prime support and a product capacity bound, equal "
                        + "local residues force equality of the bounded integer values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-recovery-structure-recovery-chain"),
                DeclarationHandle.Create(Prefix + "integer_recovery_structure_recovery_chain"),
                H("Integer recovery then structure recovery"),
                StatementSource.FromAuthor(ChainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Residues and height recover the trace codes; alignment and the explicit "
                        + "Newton bridge recover the characteristic polynomial; imported "
                        + "saturation then recovers all positive traces."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-dimensional-charpoly-determines-similarity"),
                DeclarationHandle.Create(
                    Prefix + "one_dimensional_charpoly_determines_similarity"),
                H("Dimension one has no Jordan residual"),
                StatementSource.FromAuthor(OneDimensionalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For one-by-one matrices, equal characteristic polynomials force equality "
                        + "and therefore conjugacy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("power-trace-similarity-residual-witness"),
                DeclarationHandle.Create(Prefix + "power_trace_similarity_residual_witness"),
                H("The two-dimensional residual witness"),
                StatementSource.FromAuthor(ResidualFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The imported zero matrix and nonzero square-zero block have equal "
                        + "characteristic polynomial but are not conjugate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-support-is-necessary-for-chain"),
                DeclarationHandle.Create(Prefix + "prime_support_is_necessary_for_chain"),
                H("Prime support is necessary"),
                StatementSource.FromAuthor(PrimeSupportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Overlapping nonprime coordinates make the product-capacity criterion "
                        + "false, as witnessed by the imported concrete pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("height-bound-is-necessary-for-chain"),
                DeclarationHandle.Create(Prefix + "height_bound_is_necessary_for_chain"),
                H("The height bound is necessary"),
                StatementSource.FromAuthor(HeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Without capacity, empty support identifies two distinct values in Fin 2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-height-bound-first-layer"),
                DeclarationHandle.Create(Prefix + "zero_height_bound_first_layer"),
                H("Height zero is vacuously injective"),
                StatementSource.FromAuthor(ZeroHeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At height zero the bounded carrier is empty, so every residue readout "
                        + "is injective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("newton-bridge-is-necessary"),
                DeclarationHandle.Create(Prefix + "newton_bridge_is_necessary"),
                H("The Newton bridge is necessary"),
                StatementSource.FromAuthor(NewtonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In characteristic two, zero and identity have equal first traces but "
                        + "different characteristic polynomials."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-alignment-is-necessary"),
                DeclarationHandle.Create(Prefix + "trace_alignment_is_necessary"),
                H("Trace alignment is necessary"),
                StatementSource.FromAuthor(AlignmentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equal residue codes alone can be unrelated to matrix traces, even when "
                        + "a vacuous Newton bridge holds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-dimension-chain"),
                DeclarationHandle.Create(Prefix + "zero_dimension_chain"),
                H("The zero-dimensional audit"),
                StatementSource.FromAuthor(ZeroDimensionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Fin 0, the trace family is empty and the composed conclusion remains "
                        + "valid."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-and-identity-layer-audit"),
                DeclarationHandle.Create(Prefix + "zero_and_identity_layer_audit"),
                H("Zero and identity audits"),
                StatementSource.FromAuthor(ZeroIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Empty support is injective only on the singleton window; zero and identity "
                        + "are separated by charpoly and conjugacy."))),
                DescribeRole.Theorem))));

    private static Formula PredicateFormula(Formula name) =>
        Disp(Seq(name, Sp, Colon, Sp, F.Id("Prop"), Dot));

    private static Formula LocalRecoveryFormula() =>
        Disp(Seq(F.Id("localResiduesAgree"), Sp, Rightarrow, Sp, F.Id("equal"), Dot));

    private static Formula ChainFormula() =>
        Disp(Seq(F.Id("localResidues"), Sp, Rightarrow, Sp, F.Id("integerTraces"), Sp,
            Rightarrow, Sp, F.Id("charpoly"), Sp, Land, Sp, F.Id("allTraces"), Dot));

    private static Formula OneDimensionalFormula() =>
        Disp(Seq(F.Id("charpolyEqual"), Sp, Rightarrow, Sp, F.Id("conjugate"), Dot));

    private static Formula ResidualFormula() =>
        Disp(Seq(F.Id("charpolyEqual"), Sp, Land, Sp, F.Id("notConjugate"), Dot));

    private static Formula PrimeSupportFormula() =>
        PredicateFormula(F.Id("primeSupportNecessary"));

    private static Formula HeightFormula() =>
        PredicateFormula(F.Id("heightBoundNecessary"));

    private static Formula NewtonFormula() =>
        PredicateFormula(F.Id("newtonBridgeNecessary"));

    private static Formula ZeroHeightFormula() =>
        PredicateFormula(F.Id("zeroHeightFirstLayer"));

    private static Formula AlignmentFormula() =>
        PredicateFormula(F.Id("traceAlignmentNecessary"));

    private static Formula ZeroDimensionFormula() =>
        PredicateFormula(F.Id("zeroDimensionChain"));

    private static Formula ZeroIdentityFormula() =>
        PredicateFormula(F.Id("zeroIdentityLayerAudit"));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        Prefix + name);
}
