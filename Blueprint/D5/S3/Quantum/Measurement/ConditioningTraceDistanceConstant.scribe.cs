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
                Blocks(Paragraph(Text("The bundled definition applies the positive filter on both sides, normalizes by its real trace, and returns a DensityState."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conditioning-trace-distance-constant"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/ConditioningTraceDistanceConstant.conditioning_trace_distance_constant"),
                H("Conditioning has sharp constant equal to the condition number"),
                StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive definite filter in dimension at least two, canonical density states obey the two-sided trace-distance bound.")),
                    Paragraph(Text("Equal extreme eigenvalues make the bundled conditioned state equal to the input, and the condition number is the least upper bound of all nontrivial conditioned-to-unconditioned ratios.")),
                    Paragraph(Text("The scoped hypothesis h_0 : 0 < d is derived from h_d : 2 <= d and supplies every positivity proof argument in the displayed statement.")),
                    Paragraph(Text("Here Fin d models the source support space H_P; the construction of H_P and R from a general instrument (Convention 26.1), and the exact values along the sharpness family, are not part of the statement."))),
                DescribeRole.Theorem))));

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

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Scope(Formula body) => Seq(Open, body, Close);

    private static Formula And(Formula left, Formula right) =>
        Scope(new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula Imply(Formula left, Formula right) =>
        Scope(Seq(left, Sp, Rightarrow, Sp, right));

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Div(Formula left, Formula right) =>
        new Formula.Fraction(left, right);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Matrix(Formula d) =>
        Call("Matrix", Call("Fin", d), Call("Fin", d), Complex());
    private static Formula States(Formula d) => Call("DensityState", Call("Fin", d));
    private static Formula Raw(Formula rho) =>
        Apply(Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot, F.Id("ofMatrix"), Dot,
            F.Id("symm"))), Call("val", rho));
    private static Formula Trace(Formula x) => Call("Tr", x);
    private static Formula Distance(Formula x, Formula y) => Call("traceDistance", x, y);
    private static Formula Tau(Formula hd, Formula r, Formula h, Formula rho) =>
        Call("conditionedState", hd, r, h, rho);

    private static Formula EigenvaluesZero() =>
        Seq(Operatorname, Grp(F.Id("eigenvalues")), Underscore, Grp(D(0)));

    private static Formula EigenvalueAt(Formula hermitian, Formula index) =>
        Apply(Apply(EigenvaluesZero(), hermitian), index);

    private static Formula ForallTyped(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Scope(body));

    private static Formula ExistsTyped(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Scope(body));

    private static Formula RMaxFormula()
    {
        Formula hd = Subscript(F.Id("h"), F.Id("d"));
        Formula r = F.Id("R"), h = Subscript(F.Id("h"), F.Id("R"));
        return Disp(Seq(Call("rMax", hd, r, h), Sp, Colon, Eq, Sp,
            EigenvalueAt(h, D(0)), Dot));
    }

    private static Formula RMinFormula()
    {
        Formula d = F.Id("d"), hd = Subscript(F.Id("h"), F.Id("d"));
        Formula r = F.Id("R"), h = Subscript(F.Id("h"), F.Id("R"));
        Formula last = Subtract(Call("card", Call("Fin", d)), D(1));
        return Disp(Seq(Call("rMin", hd, r, h), Sp, Colon, Eq, Sp,
            EigenvalueAt(h, last), Dot));
    }

    private static Formula ConditionNumberFormula()
    {
        Formula hd = Subscript(F.Id("h"), F.Id("d"));
        Formula r = F.Id("R"), h = Subscript(F.Id("h"), F.Id("R"));
        return Disp(Seq(Call("conditionNumber", hd, r, h), Sp, Colon, Eq, Sp,
            Div(Call("rMax", hd, r, h), Call("rMin", hd, r, h)), Dot));
    }

    private static Formula ConditionedStateFormula()
    {
        Formula d = F.Id("d"), hd = Subscript(F.Id("h"), F.Id("d"));
        Formula r = F.Id("R"), h = Subscript(F.Id("h"), F.Id("R"));
        Formula rho = Rho, raw = Raw(rho);
        Formula numerator = Mul(Scope(Mul(Call("sqrt", r), raw)), Call("sqrt", r));
        Formula denominator = Call("Re", Trace(Mul(r, raw)));
        Formula result = Typed(Call("conditionedState", hd, r, h, rho), States(d));
        return Disp(Seq(result, Sp, Colon, Eq, Sp,
            Div(Scope(numerator), Scope(denominator)), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), hd = Subscript(F.Id("h"), F.Id("d"));
        Formula r = F.Id("R"), h = Subscript(F.Id("h"), F.Id("R"));
        Formula h0 = Subscript(F.Id("h"), D(0));
        Formula rho = Rho, sigma = SigmaLower, x = F.Id("x");
        Formula states = States(d);
        Formula hermitian = Call("isHermitian", h);
        Formula k = Call("conditionNumber", h0, r, hermitian);
        Formula image = Distance(Tau(h0, r, h, rho), Tau(h0, r, h, sigma));
        Formula source = Distance(rho, sigma);
        Formula twoSided = And(
            Le(Scope(Mul(Call("inv", k), source)), image),
            Le(image, Scope(Mul(k, source))));
        Formula equalExtreme = ForallTyped(rho, states,
            Imply(Equal(Call("rMin", h0, r, hermitian),
                Call("rMax", h0, r, hermitian)),
                Equal(Tau(h0, r, h, rho), rho)));
        Formula ratioBody = And(
            NotEqual(rho, sigma),
            Equal(x, Scope(Div(
                Distance(Tau(h0, r, h, rho), Tau(h0, r, h, sigma)),
                source))));
        Formula ratioSet = Seq(OpenBrace, x, Sp, Mid, Sp,
            ExistsTyped(rho, states, ExistsTyped(sigma, states, ratioBody)),
            CloseBrace);
        Formula lub = Call("IsLUB", ratioSet, k);
        Formula quantified = ForallTyped(rho, states,
            ForallTyped(sigma, states, twoSided));
        Formula body = And(quantified, And(equalExtreme, lub));
        return Disp(Seq(Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(hd, Le(D(2), d)), Comma, Sp,
            Typed(r, Matrix(d)), Comma, Sp,
            Typed(h, Call("PosDef", r)), Comma, Sp,
            Operatorname, Grp(F.Id("let")), Open,
            Typed(h0, Lt(D(0), d)), Close, SemiSpace,
            body, Dot));
    }
}
