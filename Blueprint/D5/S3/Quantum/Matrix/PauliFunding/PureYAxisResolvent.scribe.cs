using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.PauliFunding;

internal sealed class PureYAxisResolventDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/PauliFunding/PureYAxisResolvent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact parity resolvents and all-order moments of two-dimensional Pauli control blocks.",
        H("Parity resolvents of real control blocks"), Blocks(
            Entry("controlBlock", "Actual control block",
                "For arbitrary real a and t, H(a,t) is the real matrix "
                + "[[(1+a)/4,t/4],[t/4,(1-a)/4]]. For a pure Y-axis source, "
                + "t=mu sqrt(1-a squared) and the two blocks are H(a,t) and H(a,-t).",
                DescribeRole.Definition),
            Entry("controlFilter", "Shifted control filter",
                "For arbitrary real a,t,s, P(a,t,s)=H(a,t)(H(a,t)+sI) inverse. "
                + "The inverse is Mathlib's nonsingular inverse; subsequent statements use s>0.",
                DescribeRole.Definition),
            Entry("h", "Control determinant numerator",
                "For real a,t, h(a,t)=1-a squared-t squared. "
                + "This is sixteen times the determinant of H(a,t).", DescribeRole.Definition),
            Entry("denom", "Shifted determinant numerator",
                "For real a,t,s, R(a,t,s)=8s(1+2s)+h(a,t). "
                + "It is sixteen times the determinant of H(a,t)+sI.", DescribeRole.Definition),
            Entry("alpha", "Half parity trace",
                "Define alpha(a,t,s)=4sa/R(a,t,s) for all real parameters.", DescribeRole.Definition),
            Entry("beta", "Negative parity determinant",
                "Define beta(a,t,s)=h(a,t)/R(a,t,s) for all real parameters.", DescribeRole.Definition),
            Entry("moment", "Actual cyclic product moment",
                "For real a,t,s and natural j, moment(a,t,j,s) is "
                + "the trace of (P(a,-t,s)P(a,t,s)) to the j-th power.", DescribeRole.Definition),
            Entry("resolvent_spectral_data", "Exact shifted resolvent and parity data",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, "
                + "R is strictly positive, alpha and beta are nonnegative, and the exact filter is "
                + "[[(4s+h+4sa)/R,4st/R],[4st/R,(4s+h-4sa)/R]]. "
                + "With Z=diag(1,-1), the negative filter equals ZP(a,t,s)Z, "
                + "the trace of ZP(a,t,s) is 2alpha, and its determinant is -beta. "
                + "These identities include h=0; invertibility is required only after the positive shift.",
                formula: SpectralStatement()),
            Entry("moment_eq_evenMoment", "All-order exact matrix moment",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, "
                + "and every natural j, moment(a,t,j,s) equals "
                + "(alpha+sqrt(alpha squared+beta)) to the power 2j plus "
                + "(alpha-sqrt(alpha squared+beta)) to the power 2j. "
                + "Parity makes P(a,-t,s)P(a,t,s) the square of ZP(a,t,s); "
                + "the Vieta power-trace identity supplies all orders, including repeated roots.",
                formula: MomentStatement()),
            Entry("moment_comparison", "Every-order matrix comparison",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, "
                + "and every natural j, a to the power 2j divided by (1+2s) to the power 2j "
                + "is at most moment(a,t,j,s). The characteristic polynomial evaluated at a/(1+2s) "
                + "equals beta times ((a/(1+2s)) squared-1), which is nonpositive.",
                formula: ComparisonStatement(false)),
            Entry("moment_strict", "Strict comparison in the positive determinant case",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared, h(a,t)>0 and s>0, "
                + "and every natural j>=1, a to the power 2j divided by (1+2s) to the power 2j "
                + "is strictly less than moment(a,t,j,s). The comparison polynomial is strictly negative.",
                formula: ComparisonStatement(true)),
            Entry("moment_boundary", "Exact rank-one boundary",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared, h(a,t)=0 and s>0, "
                + "and every natural j>=1, moment(a,t,j,s) equals a to the power 2j "
                + "divided by (1+2s) to the power 2j. This includes a=0 and the zero product moment.",
                formula: BoundaryStatement()),
            Entry("complexFilter", "Actual complex shifted filter",
                "For real a,t,s, complexFilter(a,t,s) is Hc(Hc+sI) inverse, "
                + "where Hc is the entrywise complex embedding of H(a,t). "
                + "Thus it uses the actual complex matrix inverse rather than an assumed embedding rule.",
                DescribeRole.Definition),
            Entry("complexMoment", "Actual complex sandwich moment",
                "For real a,t,s and natural j, complexMoment(a,t,j,s) is the real part of "
                + "the trace of (sqrt(Pc(a,-t,s))Pc(a,t,s)sqrt(Pc(a,-t,s))) to the j-th power. "
                + "The square root is the positive square root from the continuous functional calculus.",
                DescribeRole.Definition),
            Entry("complex_moment_eq_real", "Complex square-root sandwich and real cyclic product",
                "For every real a,t,s with 0<=a<=1, t squared<=1-a squared and s>0, "
                + "and every natural j, complexMoment(a,t,j,s)=moment(a,t,j,s). "
                + "The embedded shifted filter equals the embedding of the real filter. "
                + "The exact filter formula proves positive semidefiniteness, including h=0; "
                + "the square of its positive square root is therefore the filter itself. "
                + "Cyclicity of power traces proves the equality without requiring either unshifted block "
                + "or either filter to be invertible. In fact the full complex sandwich trace "
                + "is the real embedding of the real product moment.",
                formula: ComplexStatement()))));

    private static DocumentBlock Entry(string name, string title, string prose,
        DescribeRole role = DescribeRole.Theorem, Formula? formula = null) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Module + name), H(title),
            formula is null && role == DescribeRole.Definition ? StatementSource.WithoutFormula() :
                StatementSource.FromAuthor(Disp(formula ?? throw new System.InvalidOperationException(
                    "Theorem entries require their full authored statement."))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula A => V("a");
    private static Formula T => V("t");
    private static Formula S => V("s");
    private static Formula J => V("j");
    private static Formula Hh => Call("h", A, T);
    private static Formula Den => Call("denom", A, T, S);
    private static Formula AlphaValue => Call("alpha", A, T, S);
    private static Formula BetaValue => Call("beta", A, T, S);
    private static Formula Filter => Call("controlFilter", A, T, S);
    private static Formula MomentValue => Call("moment", A, T, J, S);
    private static Formula Reference => Div(Pow(A, Mul(D(2), J)),
        Pow(Add(D(1), Mul(D(2), S)), Mul(D(2), J)));

    private static Formula Telescope(Formula body, bool order = true,
        bool positiveOrder = false, Formula? determinant = null)
    {
        if (order) body = All("j", Nat, positiveOrder ? Imp(Le(D(1), J), body) : body);
        body = Imp(Lt(D(0), S), body);
        if (determinant is not null) body = Imp(determinant, body);
        body = Imp(Le(Pow(T, D(2)), Sub(D(1), Pow(A, D(2)))), body);
        body = Imp(Le(A, D(1)), body);
        body = Imp(Le(D(0), A), body);
        return All("a", Real, All("t", Real, All("s", Real, body)));
    }

    private static Formula SpectralStatement()
    {
        Formula fourS = Mul(D(4), S), fourSA = Mul(fourS, A);
        Formula off = Div(Mul(fourS, T), Den);
        Formula matrix = Seq(Begin, Grp(V("bmatrix")),
            Div(Add(Add(fourS, Hh), fourSA), Den), Amp, off, RowBreak,
            off, Amp, Div(Sub(Add(fourS, Hh), fourSA), Den), End, Grp(V("bmatrix")));
        Formula parityFilter = Mul(V("parity"), Filter);
        return Telescope(And(Lt(D(0), Den), And(Le(D(0), AlphaValue),
            And(Le(D(0), BetaValue), And(Eqn(Filter, matrix),
                And(Eqn(Call("controlFilter", A, new Formula.Negate(T), S), Mul(parityFilter, V("parity"))),
                    And(Eqn(Call("trace", parityFilter), Mul(D(2), AlphaValue)),
                        Eqn(Call("det", parityFilter), new Formula.Negate(BetaValue)))))))), order: false);
    }

    private static Formula MomentStatement() => Telescope(
        Eqn(MomentValue, Call("evenMoment", AlphaValue, BetaValue, J)));
    private static Formula ComparisonStatement(bool strict) => Telescope(
        strict ? Lt(Reference, MomentValue) : Le(Reference, MomentValue),
        positiveOrder: strict, determinant: strict ? Lt(D(0), Hh) : null);
    private static Formula BoundaryStatement() => Telescope(Eqn(MomentValue, Reference),
        positiveOrder: true, determinant: Eqn(Hh, D(0)));
    private static Formula ComplexStatement() => Telescope(
        Eqn(Call("complexMoment", A, T, J, S), MomentValue));
}
