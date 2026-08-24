using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class ExperimentValueIsKernelReductionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Experiment/ExperimentValueIsKernelReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An experiment is valuable when it removes target residual pairs, independently of "
            + "the nominal size of its response space.",
        H("Experiment Value Is Kernel Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-identifiability-is-factorization"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "targetIdentifiable_iff_factorization"),
                H("No target residual pair is equivalent to factorization"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A target residual pair consists of two states that every allowed "
                            + "experiment treats alike even though the target separates them. "
                            + "Target identifiability is exactly the absence of such a pair.")),
                    Paragraph(Text(
                        "For a nonempty state space, absence of residual pairs says that the "
                            + "target is constant on every fiber of the joint allowed-experiment "
                            + "readout. The existing identifiability criterion then supplies a "
                            + "single map that recovers the target from the complete response "
                            + "tuple, and any such factorization rules out a residual pair.")),
                    Paragraph(Text(
                        "Indexing the joint response tuple by the subtype of allowed experiments "
                            + "ensures that the factorization uses precisely the admitted family, "
                            + "not experiments outside it."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("experiment-value-is-target-kernel-reduction"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "experiment_value_is_kernel_reduction"),
                H("Experiment value is reduction of the target residual kernel"),
                StatementSource.FromAuthor(KernelReductionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the Boolean state space, the large-output experiment is constant: "
                            + "both states receive the same element of a response type with one "
                            + "thousand symbols. Allowing that experiment therefore leaves the "
                            + "residual-pair set unchanged and does not improve target "
                            + "identifiability.")),
                    Paragraph(Text(
                        "With no allowed bit experiment, the identity target has exactly the two "
                            + "ordered off-diagonal Boolean residual pairs. Once the identity bit "
                            + "experiment is allowed, equal responses force equal states, so the "
                            + "residual-pair set becomes empty and the target is identifiable.")),
                    Paragraph(Text(
                        "Thus a two-symbol response can be decisive while a strictly larger "
                            + "response space is inert. The mathematical value of the experiment "
                            + "is the target-relevant kernel it removes, rather than the cardinality "
                            + "of its nominal output alphabet."))),
                DescribeRole.Theorem))));

    private static Formula FactorizationFormula()
    {
        Formula experimentType = F.Id("E");
        Formula stateType = F.Id("X");
        Formula responseType = F.Id("R");
        Formula targetType = F.Id("Y");
        Formula allowed = F.Id("A");
        Formula run = F.Id("r");
        Formula target = F.Id("t");
        Formula factor = F.Id("f");
        Formula coordinate = F.Id("a");
        Formula responseTuple = Seq(
            Open, Forall, Sp, coordinate, Colon, Sp, allowed, Comma, Sp,
            responseType, Close);
        Formula restrictedReadout = Call("jointReadout", Call("restrict", run, allowed));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, experimentType, Comma, Sp, stateType, Comma, Sp,
                responseType, Comma, Sp, targetType, Colon, Sp, TypeUniverse(), Comma),
            Seq(
                allowed, Colon, Sp, Call("Set", experimentType), Comma, Sp,
                run, Colon, Sp, Arrow(experimentType, Arrow(stateType, responseType)), Comma, Sp,
                target, Colon, Sp, Arrow(stateType, targetType), Comma),
            Seq(
                Call("Nonempty", stateType), Sp, Rightarrow, Sp,
                Call("TargetIdentifiable", allowed, run, target), Sp, Iff, Sp,
                Exists, Sp, factor, Colon, Sp,
                responseTuple, Sp, To, Sp, targetType, Comma, Sp,
                target, Sp, Eq, Sp,
                Seq(factor, Sp, Circ, Sp, restrictedReadout), Dot),
        ]));
    }

    private static Formula KernelReductionFormula()
    {
        Formula large = F.Id("large");
        Formula bit = F.Id("bit");
        Formula target = F.Id("target");
        Formula all = F.Id("univ");
        Formula boolType = F.Id("Bool");
        Formula offDiagonalPairs = Seq(
            OpenBrace,
            Open, F.Id("false"), Comma, Sp, F.Id("true"), Close,
            Comma, Sp,
            Open, F.Id("true"), Comma, Sp, F.Id("false"), Close,
            CloseBrace);

        return Disp(new Formula.Aligned([
            Seq(
                Open,
                Call("card", Call("Fin", D(1, 0, 0, 0))), Sp, Gt, Sp,
                Call("card", boolType), Sp, Land, Sp),
            Seq(
                ResidualPairs(Emptyset, large, target), Sp, Eq, Sp,
                ResidualPairs(all, large, target), Sp, Land, Sp),
            Seq(
                Open,
                Identifiable(Emptyset, large, target), Sp, Iff, Sp,
                Identifiable(all, large, target),
                Close, Close, Sp, Land, Sp),
            Seq(
                Open,
                Call("card", boolType), Sp, Eq, Sp, D(2), Sp, Land, Sp),
            Seq(
                ResidualPairs(Emptyset, bit, target), Sp, Eq, Sp,
                offDiagonalPairs, Sp, Land, Sp),
            Seq(
                ResidualPairs(all, bit, target), Sp, Eq, Sp, Emptyset, Sp, Land, Sp),
            Seq(
                Neg, Sp, Identifiable(Emptyset, bit, target), Sp, Land, Sp,
                Identifiable(all, bit, target),
                Close, Dot),
        ]));
    }

    private static Formula ResidualPairs(
        Formula allowed, Formula experiment, Formula target) =>
        Call("residualPairs", allowed, experiment, target);

    private static Formula Identifiable(
        Formula allowed, Formula experiment, Formula target) =>
        Call("TargetIdentifiable", allowed, experiment, target);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
}
