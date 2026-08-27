using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OperationalObservationKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Measurement/OperationalObservationKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive weighted centered effects induce the residual kernel and operational metric.",
        H("Operational Observation Kernel and Metric"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-effect-analysis"),
                DeclarationHandle.Create(Prefix + "weightedEffectAnalysis"),
                H("Centered effects construct a weighted Euclidean analysis map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each real trace-zero Hermitian direction is paired with every centered "
                        + "effect and scaled by the square root of its source weight."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("operational-observation-seminorm"),
                DeclarationHandle.Create(Prefix + "operationalObservationSeminorm"),
                H("The observation seminorm is the weighted analysis norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Euclidean norm of the weighted analysis vector is exactly the source's "
                        + "positive weighted observation seminorm."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-density-readout"),
                DeclarationHandle.Create(Prefix + "weightedDensityReadout"),
                H("Density states have weighted centered-effect readouts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A positive trace-one density state is sent to its finite vector of real "
                        + "trace pairings, with the same square-root weights."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("operational-state-distance"),
                DeclarationHandle.Create(Prefix + "operationalStateDistance"),
                H("State distance is Euclidean readout distance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The induced distance compares only observer-accessible weighted readouts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("operational-state-quotient"),
                DeclarationHandle.Create(Prefix + "OperationalStateQuotient"),
                H("The operational quotient identifies equal readouts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier is the canonical quotient by the kernel Setoid of the weighted "
                        + "density-state readout."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("operational-quotient-distance"),
                DeclarationHandle.Create(Prefix + "operationalQuotientDistance"),
                H("Readout distance descends to operational classes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Quotient.liftOn2 constructs the representative-independent distance directly "
                        + "on operational classes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("operational-kernel-and-metric"),
                DeclarationHandle.Create(
                    Prefix + "operational_observation_kernel_and_metric"),
                H("The seminorm kernel is the invisible residual"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Strictly positive weights make a zero weighted coordinate equivalent to "
                            + "a zero trace pairing. Orthogonality to every effect therefore equals "
                            + "orthogonality to their real span.")),
                    Paragraph(Text(
                        "Euclidean readout distance supplies the state pseudometric laws. Its "
                            + "canonical kernel quotient is separated and retains symmetry and the "
                            + "triangle inequality.")),
                    Paragraph(Text(
                        "Because every square-root weight is nonzero, the weighted and unweighted "
                            + "state signatures have the same fibers. Full-state separation is "
                            + "therefore equivalent to informational completeness."))),
                DescribeRole.Theorem))));

    private static Formula Apply2(Formula function, Formula first, Formula second) =>
        Seq(function, Open, first, Comma, Sp, second, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), indexType = F.Id("A"), index = F.Id("i");
        Formula effects = F.Id("E"), weight = F.Id("w"), direction = F.Id("D");
        Formula rho = Rho, sigma = SigmaLower, tau = F.Id("tau");
        Formula first = F.Id("u"), second = F.Id("v"), third = F.Id("z");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula hermitian = Seq(
            Operatorname, Grp(F.Id("Herm")), Underscore, Grp(d),
            Caret, Grp(D(0)));
        Formula stateType = Call("DensityState", Call("Fin", d));
        Formula effect = Seq(effects, Underscore, Grp(index));
        Formula inner = Seq(
            Langle, Sp, direction, Comma, Sp, effect, Sp, Rangle,
            Underscore, Grp(reals));
        Formula seminorm = Seq(
            new Formula.Norm(direction), Underscore, Grp(F.Id("O")));
        Formula seminormDefinition = Seq(
            Forall, Sp, Typed(direction, hermitian), Comma, Sp,
            seminorm, Sp, Eq, Sp, Sqrt, Grp(
                Sum, Underscore, Grp(index, Sp, InMacro, Sp, indexType), Sp,
                Apply(weight, index), Sp, inner, Caret, Grp(D(2))));

        Formula unweightedReadout(Formula state) => Seq(
            F.Id("q"), Open, state, Close, Open, index, Close);
        Formula unweightedReadoutDefinition = Seq(
            Forall, Sp, Typed(rho, stateType), Comma, Sp,
            Typed(index, indexType), Comma, Sp,
            unweightedReadout(rho), Sp, Eq, Sp, Re, Sp,
            Call("Tr", Seq(Call("matrix", rho), Sp, effect)));
        Formula weightedReadout(Formula state) => Seq(
            F.Id("q"), Underscore, Grp(weight),
            Open, state, Close, Open, index, Close);
        Formula weightedReadoutDefinition = Seq(
            Forall, Sp, Typed(rho, stateType), Comma, Sp,
            Typed(index, indexType), Comma, Sp,
            weightedReadout(rho), Sp, Eq, Sp,
            Sqrt, Grp(Apply(weight, index)), Sp, unweightedReadout(rho));
        Formula stateDistance(Formula left, Formula right) =>
            Apply2(new Formula.Subscript(F.Id("d"), F.Id("O")), left, right);
        Formula stateDistanceDefinition = Seq(
            Forall, Sp, Typed(rho, stateType), Comma, Sp,
            Typed(sigma, stateType), Comma, Sp,
            stateDistance(rho, sigma), Sp, Eq, Sp,
            new Formula.Norm(Seq(
                F.Id("q"), Underscore, Grp(weight), Open, rho, Close,
                Sp, Minus, Sp,
                F.Id("q"), Underscore, Grp(weight), Open, sigma, Close)),
            Underscore, Grp(D(2)));
        Formula quotient = new Formula.Subscript(F.Id("Q"), F.Id("O"));
        Formula quotientDefinition = Seq(
            quotient, Sp, Eq, Sp, stateType, Sp, Slash, Sp,
            Call("ker", Seq(F.Id("q"), Underscore, Grp(weight))));
        Formula pointClass(Formula state) => Seq(OpenBracket, state, CloseBracket);
        Formula quotientDistance(Formula left, Formula right) =>
            Apply2(new Formula.Subscript(F.Id("d"), F.Id("quot")), left, right);
        Formula quotientDistanceDefinition = Seq(
            Forall, Sp, Typed(rho, stateType), Comma, Sp,
            Typed(sigma, stateType), Comma, Sp,
            quotientDistance(pointClass(rho), pointClass(sigma)), Sp, Eq, Sp,
            stateDistance(rho, sigma));

        Formula visible = Call("span", Seq(
            reals, Comma, Sp,
            OpenBrace, effect, Colon, Sp, index, Sp, InMacro, Sp,
            indexType, CloseBrace));
        Formula kernelClause = Seq(
            Call("ker", Seq(direction, Sp, Mapsto, Sp, seminorm)), Sp, Eq, Sp,
            visible, Caret, Grp(Perp));
        Formula stateNonnegative = Seq(
            Forall, Sp, Typed(rho, stateType), Comma, Sp,
            Typed(sigma, stateType), Comma, Sp,
            D(0), Sp, Leq, Sp, stateDistance(rho, sigma));
        Formula stateSelf = Seq(
            Forall, Sp, Typed(rho, stateType), Comma, Sp,
            stateDistance(rho, rho), Sp, Eq, Sp, D(0));
        Formula stateSymmetry = Seq(
            Forall, Sp, Typed(rho, stateType), Comma, Sp,
            Typed(sigma, stateType), Comma, Sp,
            stateDistance(rho, sigma), Sp, Eq, Sp, stateDistance(sigma, rho));
        Formula stateTriangle = Seq(
            Forall, Sp, Typed(rho, stateType), Comma, Sp,
            Typed(sigma, stateType), Comma, Sp, Typed(tau, stateType), Comma, Sp,
            stateDistance(rho, tau), Sp, Leq, Sp,
            stateDistance(rho, sigma), Sp, Plus, Sp, stateDistance(sigma, tau));

        Formula quotientNonnegative = Seq(
            Forall, Sp, Typed(first, quotient), Comma, Sp, Typed(second, quotient),
            Comma, Sp, D(0), Sp, Leq, Sp, quotientDistance(first, second));
        Formula quotientSelf = Seq(
            Forall, Sp, Typed(first, quotient), Comma, Sp,
            quotientDistance(first, first), Sp, Eq, Sp, D(0));
        Formula quotientSymmetry = Seq(
            Forall, Sp, Typed(first, quotient), Comma, Sp, Typed(second, quotient),
            Comma, Sp, quotientDistance(first, second), Sp, Eq, Sp,
            quotientDistance(second, first));
        Formula quotientTriangle = Seq(
            Forall, Sp, Typed(first, quotient), Comma, Sp, Typed(second, quotient),
            Comma, Sp, Typed(third, quotient), Comma, Sp,
            quotientDistance(first, third), Sp, Leq, Sp,
            quotientDistance(first, second), Sp, Plus, Sp,
            quotientDistance(second, third));
        Formula quotientSeparates = Seq(
            Forall, Sp, Typed(first, quotient), Comma, Sp, Typed(second, quotient),
            Comma, Sp, quotientDistance(first, second), Sp, Eq, Sp, D(0), Sp,
            Iff, Sp, first, Sp, Eq, Sp, second);

        Formula stateSeparates = Seq(
            Forall, Sp, Typed(rho, stateType), Comma, Sp,
            Typed(sigma, stateType), Comma, Sp,
            stateDistance(rho, sigma), Sp, Eq, Sp, D(0), Sp, Iff, Sp,
            rho, Sp, Eq, Sp, sigma);
        Formula signature = Seq(
            rho, Colon, Sp, stateType, Sp, Mapsto, Sp,
            Open, index, Colon, Sp, indexType, Sp, Mapsto, Sp,
            unweightedReadout(rho), Close);
        Formula completeness = Seq(
            Open, stateSeparates, Close, Sp, Iff, Sp,
            Call("Injective", signature));
        Formula positiveWeights = Seq(
            Forall, Sp, index, InMacro, Sp, indexType, Comma, Sp,
            D(0), Sp, Lt, Sp, Apply(weight, index));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(d, naturals), Comma, Sp, Call("NeZero", d),
            Comma, Sp, Typed(indexType, type), Comma,
            RowBreak, Grp(),
            Seq(OpenBracket, Call("Fintype", indexType), CloseBracket), Comma, Sp,
            Typed(effects, Arrow(indexType, hermitian)), Comma, Sp,
            Typed(weight, Arrow(indexType, reals)), Comma,
            RowBreak, Grp(),
            Open, positiveWeights, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Sp,
            seminormDefinition, Comma,
            RowBreak, Grp(),
            unweightedReadoutDefinition, Comma, Sp,
            weightedReadoutDefinition, Comma,
            RowBreak, Grp(),
            stateDistanceDefinition, Comma, Sp, quotientDefinition, Comma,
            RowBreak, Grp(),
            quotientDistanceDefinition, Comma,
            RowBreak, Grp(),
            kernelClause, Sp, Land,
            RowBreak, Grp(),
            Open, stateNonnegative, Close, Sp, Land, Sp,
            Open, stateSelf, Close, Sp, Land,
            RowBreak, Grp(),
            Open, stateSymmetry, Close, Sp, Land, Sp,
            Open, stateTriangle, Close, Sp, Land,
            RowBreak, Grp(),
            Open, quotientNonnegative, Close, Sp, Land, Sp,
            Open, quotientSelf, Close, Sp, Land,
            RowBreak, Grp(),
            Open, quotientSymmetry, Close, Sp, Land, Sp,
            Open, quotientTriangle, Close, Sp, Land,
            RowBreak, Grp(),
            Open, quotientSeparates, Close, Sp, Land,
            RowBreak, Grp(),
            Open, completeness, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
