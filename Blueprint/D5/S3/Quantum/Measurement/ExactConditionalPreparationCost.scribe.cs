using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ExactConditionalPreparationCostDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Measurement/ExactConditionalPreparationCost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact universal conditional preparation is a scalar square-root filter, with optimal worst-case success equal to the spectral endpoint ratio.",
        H("Exact Conditional Preparation Cost"),
        Blocks(
            Entry("exact-preparation-contract", "ExactPreparationContract",
                "Exact conditional preparation contract", ContractFormula(),
                "On every positive trace-one input, the output has positive real trace and is the normalized positive-square-root sandwich associated with the effect; the Kraus family is trace-nonincreasing.",
                DescribeRole.Definition),
            Entry("trace-nonincreasing", "TraceNonincreasing",
                "Trace-nonincreasing Kraus family", TraceNonincreasingFormula(),
                "A Kraus family is trace-nonincreasing when the identity minus its total effect is positive semidefinite.",
                DescribeRole.Definition),
            Entry("least-eigenvalue", "leastEigenvalue", "Least eigenvalue",
                LeastEigenvalueFormula(),
                "The least eigenvalue is the infimum of the finite Hermitian eigenvalue family.",
                DescribeRole.Definition),
            Entry("greatest-eigenvalue", "greatestEigenvalue", "Greatest eigenvalue",
                GreatestEigenvalueFormula(),
                "The greatest eigenvalue is the supremum of the finite Hermitian eigenvalue family.",
                DescribeRole.Definition),
            Entry("exact-conditional-preparation-cost", "exact_conditional_preparation_cost",
                "Rigidity, optimal cost, and determinism", TheoremFormula(),
                "Every exact universal preparation family is a positive scalar multiple of the square-root sandwich channel. Its total effect is the same scalar multiple of the prescribed effect, so trace nonincrease bounds the scalar by the reciprocal largest eigenvalue. A largest-eigenvalue input gives the upper bound, while the reciprocal-square-root filter attains the least-to-largest eigenvalue ratio. Deterministic preparation is possible exactly when the effect is a positive scalar identity.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string text, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Open, source, Close, Sp, To, Sp, target);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula Less(Formula left, Formula right) =>
        Seq(left, Sp, Lt, Sp, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        Seq(left, Sp, Le, Sp, right);

    private static Formula Imply(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Rightarrow, Sp, right);

    private static Formula ForAll(Formula value, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(value, type), Comma, Sp, body);

    private static Formula ExistsTyped(Formula value, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(value, type), Comma, Sp, body);

    private static Formula Multiply(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Scale(Formula scalar, Formula value) =>
        Multiply(scalar, value);

    private static Formula Conjoin(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(index == 0
                ? Seq(Open, clauses[index], Close)
                : Seq(RowBreak, Open, clauses[index], Close));
        }

        return Seq([.. items]);
    }

    private static Formula IndexType => F.Id("Iota");
    private static Formula Effect => F.Id("R");
    private static Formula Family => F.Id("K");
    private static Formula State => F.Id("rho");
    private static Formula Input => F.Id("X");
    private static Formula Count => F.Id("m");
    private static Formula Coefficient => F.Id("c");
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Type => Seq(Operatorname, Grp(F.Id("Type")));
    private static Formula MatrixType => Call("Matrix", IndexType, IndexType, Complex);
    private static Formula FinCount => Call("Fin", Count);
    private static Formula FamilyType => Arrow(FinCount, MatrixType);
    private static Formula SqrtEffect => Call("sqrt", Effect);
    private static Formula Identity => F.Id("I");
    private static Formula Minimum => Call("leastEigenvalue", Effect);
    private static Formula Maximum => Call("greatestEigenvalue", Effect);
    private static Formula Ratio => Seq(Minimum, Sp, Slash, Sp, Maximum);

    private static Formula Action(Formula family, Formula input) =>
        Call("PhyslibLeaf.MatrixMap.of_kraus", family, family, input);

    private static Formula Trace(Formula value) => Call("Tr", value);
    private static Formula RealPart(Formula value) => Call("Re", value);
    private static Formula PositiveSemidefinite(Formula value) => Call("PosSemidef", value);
    private static Formula Contract(Formula family) =>
        Call("ExactPreparationContract", Effect, family);
    private static Formula TraceNonincrease(Formula family) =>
        Call("TraceNonincreasing", family);
    private static Formula Sandwich(Formula input) =>
        Multiply(Multiply(SqrtEffect, input), SqrtEffect);
    private static Formula Density(Formula state) =>
        Conjoin(PositiveSemidefinite(state), Equal(Trace(state), D(1)));

    private static Formula ContractFormula()
    {
        Formula outputTrace = Trace(Action(Family, State));
        Formula denominator = Trace(Multiply(Effect, State));
        Formula normalizedScale = Seq(outputTrace, Sp, Slash, Sp, denominator);
        Formula clauses = Conjoin(
            Less(D(0), RealPart(outputTrace)),
            Equal(Action(Family, State), Scale(normalizedScale, Sandwich(State))),
            TraceNonincrease(Family));
        return ForAll(State, MatrixType, Imply(Density(State), clauses));
    }

    private static Formula TraceNonincreasingFormula()
    {
        Formula j = F.Id("j");
        Formula branch = Apply(Family, j);
        Formula effectSum = Seq(
            Sum, Underscore, Grp(j, Sp, InMacro, Sp, FinCount), Sp,
            Multiply(Call("star", branch), branch));
        return PositiveSemidefinite(Seq(Identity, Sp, Minus, Sp, effectSum));
    }

    private static Formula LeastEigenvalueFormula() =>
        Equal(Minimum, Call("inf", Call("eigenvalues", Effect)));

    private static Formula GreatestEigenvalueFormula() =>
        Equal(Maximum, Call("sup", Call("eigenvalues", Effect)));

    private static Formula ScalarAction(Formula family, Formula coefficient)
    {
        Formula equality = Equal(
            Action(family, Input),
            Scale(coefficient, Sandwich(Input)));
        return ForAll(Input, MatrixType, equality);
    }

    private static Formula FinOneFamilyType =>
        Arrow(Call("Fin", D(1)), MatrixType);

    private static Formula ScalarFamily(Formula family, Formula coefficient)
    {
        Formula scale = Scale(Call("sqrt", coefficient), SqrtEffect);
        return Seq(family, Sp, Colon, Sp, FinOneFamilyType, Sp, Colon, Eq, Sp,
            F.Id("fun"), Sp, Underscore, Sp, Mapsto, Sp, scale);
    }

    private static Formula RigidityClause()
    {
        Formula body = ExistsTyped(Coefficient, Real,
            Conjoin(Less(D(0), Coefficient), ScalarAction(Family, Coefficient)));
        return ForAll(Count, Nat,
            ForAll(Family, FamilyType, Imply(Contract(Family), body)));
    }

    private static Formula ScalarConverseClause()
    {
        Formula family = F.Id("Kc");
        Formula outputTrace = Trace(Action(family, State));
        Formula denominator = Trace(Multiply(Effect, State));
        Formula normalizedScale = Seq(outputTrace, Sp, Slash, Sp, denominator);
        Formula conditional = ForAll(State, MatrixType,
            Imply(Density(State), Conjoin(
                Less(D(0), RealPart(outputTrace)),
                Equal(Action(family, State),
                    Scale(normalizedScale, Sandwich(State))))));
        Formula tni = Seq(
            TraceNonincrease(family), Sp, Iff, Sp,
            PositiveSemidefinite(Seq(
                Identity, Sp, Minus, Sp, Scale(Coefficient, Effect))));
        Formula body = Seq(
            Operatorname, Grp(F.Id("let")), Sp, ScalarFamily(family, Coefficient), Semi, Sp,
            Conjoin(conditional, tni));
        return ForAll(Coefficient, Real,
            Imply(Less(D(0), Coefficient), body));
    }

    private static Formula EffectClause()
    {
        Formula target = Seq(
            TraceNonincrease(Family), Sp, Iff, Sp,
            PositiveSemidefinite(Seq(
                Identity, Sp, Minus, Sp, Scale(Coefficient, Effect))));
        Formula body = Imply(
            Less(D(0), Coefficient),
            Imply(ScalarAction(Family, Coefficient), target));
        return ForAll(Count, Nat,
            ForAll(Family, FamilyType,
                ForAll(Coefficient, Real, body)));
    }

    private static Formula WorstCaseClause()
    {
        Formula witness = ExistsTyped(State, MatrixType,
            Conjoin(
                Density(State),
                LessEqual(RealPart(Trace(Action(Family, State))), Ratio)));
        Formula body = Imply(
            Contract(Family),
            Imply(TraceNonincrease(Family), witness));
        return ForAll(Count, Nat, ForAll(Family, FamilyType, body));
    }

    private static Formula OptimalFamily()
    {
        Formula scale = Seq(D(1), Sp, Slash, Sp, Sqrt, Grp(Maximum));
        return Seq(
            F.Id("Kopt"), Sp, Colon, Sp, FinOneFamilyType, Sp, Colon, Eq, Sp,
            F.Id("fun"), Sp, Underscore, Sp, Mapsto, Sp,
            Scale(scale, SqrtEffect));
    }

    private static Formula Adjoint(Formula value) => Call("conjTranspose", value);

    private static Formula AttainmentClause()
    {
        Formula optimal = F.Id("Kopt");
        Formula failure = F.Id("Kfail");
        Formula lower = ForAll(State, MatrixType,
            Imply(Density(State),
                LessEqual(Ratio, RealPart(Trace(Action(optimal, State))))));
        Formula tracePreserving = Equal(
            Seq(Adjoint(Apply(optimal, D(0))), Sp, Cdot, Sp, Apply(optimal, D(0)), Sp,
                Plus, Sp, Adjoint(failure), Sp, Cdot, Sp, failure),
            Identity);
        return Seq(
            Operatorname, Grp(F.Id("let")), Sp, OptimalFamily(), Semi, Sp,
            Operatorname, Grp(F.Id("let")), Sp, failure, Sp, Colon, Sp, MatrixType,
            Sp, Colon, Eq, Sp, Call("sqrt", Seq(
                D(1), Sp, Minus, Sp,
                Scale(Seq(D(1), Sp, Slash, Sp, Maximum), Effect))), Semi, Sp,
            Conjoin(Contract(optimal), TraceNonincrease(optimal), tracePreserving, lower));
    }

    private static Formula DeterminismClause()
    {
        Formula deterministic = ExistsTyped(Count, Nat,
            ExistsTyped(Family, FamilyType,
                Conjoin(
                    Contract(Family),
                    TraceNonincrease(Family),
                    ForAll(State, MatrixType,
                        Imply(Density(State),
                            Equal(Trace(Action(Family, State)), D(1)))))));
        Formula scalar = F.Id("lambda");
        Formula scalarIdentity = ExistsTyped(scalar, Real,
            Conjoin(
                Less(D(0), scalar),
                Equal(Effect, Scale(scalar, Identity))));
        return Seq(Open, deterministic, Close, Sp, Iff, Sp, scalarIdentity);
    }

    private static Formula TheoremFormula()
    {
        Formula assumptions = Seq(
            Forall, Sp, Typed(IndexType, Type), Comma, Sp,
            Call("Fintype", IndexType), Comma, Sp,
            Call("DecidableEq", IndexType), Comma, Sp,
            Call("Nonempty", IndexType), Comma, RowBreak, Grp(),
            Typed(Effect, MatrixType), Comma, Sp,
            Call("PosDef", Effect), Comma, RowBreak, Grp());
        return Seq(
            assumptions,
            Conjoin(
                RigidityClause(),
                ScalarConverseClause(),
                EffectClause(),
                WorstCaseClause(),
                AttainmentClause(),
                DeterminismClause()),
            Dot);
    }
}
