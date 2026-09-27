using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ConditioningTraceDistanceConstantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive conditioning filters have sharp trace-distance constant equal to the spectral condition number.",
        H("Conditioning Trace-Distance Constant"),
        Blocks(
            Describe.Lean(DescribeId.Create("conditioning-is-density"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.IsDensity"),
                H("Density matrices are positive semidefinite and trace one"),
                StatementSource.FromAuthor(IsDensityFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A density matrix is a positive semidefinite matrix whose trace is one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-distance-definition"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.traceDistance"),
                H("Trace distance is half the trace norm"),
                StatementSource.FromAuthor(TraceDistanceFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace distance is one half of the trace norm of the difference."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("maximum-eigenvalue-definition"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMax"),
                H("The maximum eigenvalue"),
                StatementSource.FromAuthor(RMaxFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The maximum eigenvalue is the first entry of the ordered eigenvalue list."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("minimum-eigenvalue-definition"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.rMin"),
                H("The minimum eigenvalue"),
                StatementSource.FromAuthor(RMinFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The minimum eigenvalue is the last entry of the ordered eigenvalue list."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("condition-number-definition"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionNumber"),
                H("The spectral condition number"),
                StatementSource.FromAuthor(ConditionNumberFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The spectral condition number is the ratio of the maximum to the minimum eigenvalue."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conditioned-state-definition"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditionedState"),
                H("The normalized conditioned state"),
                StatementSource.FromAuthor(ConditionedStateFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A positive filter is applied on both sides and normalized by its real trace."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conditioning-trace-distance-constant"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditioning_trace_distance_constant"),
                H("Conditioning has sharp constant equal to the condition number"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive definite filter in dimension at least two, conditioning preserves density matrices and changes trace distance by at most the spectral condition number and at least its reciprocal.")),
                    Paragraph(Text("The condition number is sharp: it is the least upper bound of all nontrivial ratios of conditioned to unconditioned trace distance."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Div(Formula left, Formula right) =>
        new Formula.Fraction(left, right);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Matrix(Formula d) => Call("Matrix", Call("Fin", d), Call("Fin", d), Complex());
    private static Formula Trace(Formula x) => Call("Tr", x);
    private static Formula Density(Formula x) => Call("IsDensity", x);
    private static Formula Distance(Formula x, Formula y) => Call("traceDistance", x, y);
    private static Formula Tau(Formula r, Formula x) => Call("conditionedState", r, x);

    private static Formula IsDensityFormula()
    {
        Formula d = F.Id("d"), rho = F.Id("rho");
        return Disp(Seq(Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(rho, Matrix(d)), Sp, Eq, Sp,
            And(Call("PosSemidef", rho), Equal(Trace(rho), D(1))), Dot));
    }

    private static Formula TraceDistanceFormula()
    {
        Formula d = F.Id("d"), x = F.Id("X"), y = F.Id("Y");
        return Disp(Seq(Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(x, Matrix(d)), Comma, Sp, Typed(y, Matrix(d)), Sp, Eq, Sp,
            Div(Call("traceNorm", Seq(x, Sp, Minus, Sp, y)), D(2)), Dot));
    }

    private static Formula RMaxFormula()
    {
        Formula d = F.Id("d"), r = F.Id("R"), h = F.Id("hR");
        return Disp(Seq(Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(r, Matrix(d)), Comma, Sp, Typed(h, Call("IsHermitian", r)), Sp,
            Equal(Call("rMax", d, r, h), Call("eigenvalueFirst", r)), Dot));
    }

    private static Formula RMinFormula()
    {
        Formula d = F.Id("d"), r = F.Id("R"), h = F.Id("hR");
        return Disp(Seq(Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(r, Matrix(d)), Comma, Sp, Typed(h, Call("IsHermitian", r)), Sp,
            Equal(Call("rMin", d, r, h), Call("eigenvalueLast", r)), Dot));
    }

    private static Formula ConditionNumberFormula()
    {
        Formula d = F.Id("d"), r = F.Id("R"), h = F.Id("hR");
        return Disp(Seq(Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(r, Matrix(d)), Comma, Sp, Typed(h, Call("IsHermitian", r)), Sp,
            Equal(Call("conditionNumber", d, r, h),
                Div(Call("rMax", d, r, h), Call("rMin", d, r, h))), Dot));
    }

    private static Formula ConditionedStateFormula()
    {
        Formula d = F.Id("d"), r = F.Id("R"), rho = F.Id("rho");
        Formula root = Call("sqrt", r);
        return Disp(Seq(Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(r, Matrix(d)), Comma, Sp, Typed(rho, Matrix(d)), Sp, Eq, Sp,
            Mul(Div(D(1), Call("Re", Trace(Mul(r, rho)))),
                Mul(Mul(root, rho), root)), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), r = F.Id("R"), rho = F.Id("rho"), sigma = F.Id("sigma");
        Formula k = Call("conditionNumber", d, r, Call("hR", r));
        Formula source = Distance(rho, sigma), image = Distance(Tau(r, rho), Tau(r, sigma));
        Formula twoSided = And(Le(Mul(Call("inv", k), source), image), Le(image, Mul(k, source)));
        Formula ratioSet = Seq(OpenBrace, F.Id("x"), Sp, Mid, Sp,
            Call("exists", rho, Sp, sigma, Sp, Density(rho), Sp, And(
                Density(sigma), And(Seq(rho, Sp, Neq, Sp, sigma),
                    Equal(F.Id("x"), Div(image, source))))), CloseBrace);
        Formula lubSet = Call("IsLUB", ratioSet, k);
        Formula hypotheses = And(Lt(D(1), d), Call("PosDef", r));
        Formula quantified = Seq(Forall, Sp, Typed(rho, Matrix(d)), Comma, Sp,
            Typed(sigma, Matrix(d)), Comma, Sp, Density(rho), Sp, Rightarrow, Sp,
            Density(sigma), Sp, Rightarrow, Sp, twoSided);
        return Disp(Seq(Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(r, Matrix(d)), Comma, Sp, hypotheses, Sp, Rightarrow, Sp,
            And(quantified, lubSet), Dot));
    }
}
