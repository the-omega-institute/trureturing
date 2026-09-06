using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ObserverCriteria;

internal sealed class StopLossWeakCurvatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/ObserverCriteria/StopLossWeakCurvature.";
    private static Formula Delta => F.DeltaLower;
    private static Formula M => F.Id("m");
    private static Formula I => F.Id("I");
    private static Formula Phi => F.Varphi;
    private static Formula W => F.Omega;
    private static Formula Y => F.Id("y");
    private static Formula X => F.Id("x");
    private static Formula T => F.Id("t");
    private static Formula End => Seq(W, Sp, Plus, Sp, Y);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weak second derivative of a finite stop-loss profile is its weighted "
            + "atomic divisor; tail integrals and depth derivatives describe transport.",
        H("Stop-Loss Weak Curvature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("active-pole-height-weak-curvature"),
                DeclarationHandle.Create(Prefix + "active_pole_height_weak_curvature"),
                H("Weak curvature of one kink"),
                StatementSource.FromAuthor(SingleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "The primitive is the product of distance minus position with the first "
                        + "test derivative, plus the test itself. Its derivative cancels the "
                        + "first-derivative terms. Restricting the kink to its lower half-line "
                        + "and applying compact-support FTC leaves the test value at the pole."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("remaining-depth-weak-curvature"),
                DeclarationHandle.Create(Prefix + "remaining_depth_weak_curvature"),
                H("Weak curvature of the finite defect product"),
                StatementSource.FromAuthor(FiniteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "This finite-sum companion consumes the single-kink theorem. Compact "
                        + "support makes every weighted integrand integrable, so integral "
                        + "linearity gives the atomic evaluation sum for arbitrary C2 tests."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stop-loss-transport-and-weak-curvature"),
                DeclarationHandle.Create(Prefix + "stop_loss_transport_and_weak_curvature"),
                H("Tail transport and weak curvature"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(DefinitionDsl.Text(
                        "The displayed local notation expands the canonical "
                            + "ObservationDepthStopLoss functions. Natural tail counts and "
                            + "multiplicities are cast to real numbers when integrated.")),
                    Paragraph(DefinitionDsl.Text(
                        "Source provenance: the observation-layer transport theorem in the "
                            + "observer-adelic-completion-constant-theory input. Its seven "
                            + "displayed identities are public here. Positive pole distances "
                            + "are not needed. This companion consumes the finite weak-curvature "
                            + "theorem. Recovery of arbitrary measures from distributions remains "
                            + "a separate prerequisite and is not a conclusion."))),
                DescribeRole.Theorem))));

    private static Formula SingleFormula() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, Delta, Colon, Sp, Reals(), Comma, Sp, TestBinder(), Comma),
        Seq(TestPremises(), Sp, Rightarrow),
        Equal(Integral(Reals(), Seq(Call("activePoleHeight", Delta, X), Sp, Cdot, Sp,
            Apply(Call("deriv", Call("deriv", Phi)), X))), Apply(Phi, Delta)),
    ]));

    private static Formula FiniteFormula() => Disp(new Formula.Aligned([
        FamilyBinder(),
        Seq(Forall, Sp, TestBinder(), Comma, Sp, TestPremises(), Sp, Rightarrow),
        Equal(Integral(Reals(), Seq(Call("remainingDepth", Delta, M, X), Sp, Cdot, Sp,
            Apply(Call("deriv", Call("deriv", Phi)), X))), AtomicEvaluation()),
    ]));

    private static Formula TransportFormula() => Disp(new Formula.Aligned([
        FamilyBinder(),
        Seq(Op("let"), Sp, F.Id("R"), Colon, Sp, Reals(), Sp, To, Sp, Reals(),
            Sp, Colon, Eq, Sp, Call("remainingDepth", Delta, M), Comma),
        Seq(F.Id("N"), Colon, Sp, Reals(), Sp, To, Sp, Reals(), Sp, Colon, Eq, Sp,
            Open, X, Colon, Sp, Reals(), Sp, Mapsto, Sp,
            AsReal(Call("horizontalTailCount", Delta, M, X)), Close, Comma),
        Seq(F.Id("A"), Colon, Sp, Reals(), Sp, To, Sp, Reals(), Sp, To, Sp, Reals(),
            Sp, Colon, Eq, Sp, Call("doubleDepthDecay", Delta, M), Sp, Op("in")),
        Seq(Open, Forall, Sp, W, Colon, Sp, Reals(), Comma, Sp,
            Equal(Call("R", W), Integral(Call("Ioi", W), Call("N", X))), Close, Sp, Land),
        Seq(Open, DepthBinder(), Nonnegative(Y), Sp, Rightarrow, Sp,
            Equal(Call("A", W, Y), Subtract(Call("R", W), Call("R", End))), Close, Sp, Land),
        Seq(Open, DepthBinder(), Nonnegative(Y), Sp, Rightarrow, Sp,
            Equal(Call("A", W, Y), Seq(F.Int, Underscore, Grp(W), Caret, Grp(End),
                Sp, Call("N", X), Sp, F.Id("d"), X)), Close, Sp, Land),
        Seq(Open, DepthBinder(), Positive(Y), Sp, Rightarrow, Sp, Away(End), Sp, Rightarrow, Sp,
            Equal(DerivativeY(), Call("N", End)), Close, Sp, Land),
        Seq(Open, DepthBinder(), Nonnegative(Y), Sp, Rightarrow, Sp, Away(W), Sp, Rightarrow, Sp,
            Away(End), Sp, Rightarrow, Sp,
            Equal(DerivativeW(), Subtract(Call("N", End), Call("N", W))), Close, Sp, Land),
        Seq(Open, DepthBinder(), Positive(Y), Sp, Rightarrow, Sp, Away(W), Sp, Rightarrow, Sp,
            Away(End), Sp, Rightarrow, Sp,
            Equal(Subtract(DerivativeW(), DerivativeY()), Seq(Minus, Call("N", W))),
            Close, Sp, Land),
        Seq(Open, Forall, Sp, TestBinder(), Comma, Sp, TestPremises(), Sp, Rightarrow, Sp,
            Equal(Integral(Reals(), Seq(Call("R", X), Sp, Cdot, Sp,
                Apply(Call("deriv", Call("deriv", Phi)), X))), AtomicEvaluation()), Close),
    ]));

    private static Formula FamilyBinder() => Seq(
        Forall, Sp, I, Colon, Sp, Op("Type"), Comma, Sp,
        OpenBracket, Call("Fintype", I), CloseBracket, Comma, Sp,
        Delta, Colon, Sp, I, Sp, To, Sp, Reals(), Comma, Sp,
        M, Colon, Sp, I, Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma);

    private static Formula TestBinder() => Seq(Phi, Colon, Sp, Reals(), Sp, To, Sp, Reals());
    private static Formula TestPremises() => Seq(Call("ContDiff", Reals(), D(2), Phi),
        Sp, Land, Sp, Call("HasCompactSupport", Phi));
    private static Formula DepthBinder() => Seq(Forall, Sp, W, Sp, Y, Colon, Sp, Reals(), Comma, Sp);
    private static Formula Nonnegative(Formula value) => Seq(D(0), Sp, Leq, Sp, value);
    private static Formula Positive(Formula value) => Seq(D(0), Sp, Lt, Sp, value);
    private static Formula Away(Formula point) => Seq(Open, Forall, Sp, F.Id("j"), Colon, Sp, I,
        Comma, Sp, point, Sp, Neq, Sp, Apply(Delta, F.Id("j")), Close);
    private static Formula DerivativeY() => Apply(Call("deriv",
        Seq(Open, T, Colon, Sp, Reals(), Sp, Mapsto, Sp, Call("A", W, T), Close)), Y);
    private static Formula DerivativeW() => Apply(Call("deriv",
        Seq(Open, T, Colon, Sp, Reals(), Sp, Mapsto, Sp, Call("A", T, Y), Close)), W);
    private static Formula AtomicEvaluation() => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id("j"), Colon, Sp, I)), Sp,
        AsReal(Apply(M, F.Id("j"))), Sp, Cdot, Sp, Apply(Phi, Apply(Delta, F.Id("j"))));
    private static Formula Integral(Formula domain, Formula body) => Seq(
        new Formula.Subscript(F.Int, Seq(X, Sp, InMacro, Sp, domain)), Sp,
        body, Sp, F.Id("d"), X);
    private static Formula AsReal(Formula value) => Seq(Open, value, Colon, Sp, Reals(), Close);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Subtract(Formula left, Formula right) => Seq(left, Sp, Minus, Sp, right);
}
