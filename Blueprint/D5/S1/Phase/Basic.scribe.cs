using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var m = Id("m");
        var phaseN = Call("goldenPhase", n);
        var phaseValue = new Formula.Modulo(
            Multiply(n, new Formula.Phi()),
            Num(1));
        var injectivity = LeanTheorem(
            "D5/S1/Phase/Basic.goldenPhase_injective");
        var opening = Paragraph(
            Ref("D5/S1/Phase/Basic"),
            Text(" maps an integer "),
            Math(n),
            Text(" to "),
            Math(phaseValue),
            Text(" in the additive circle. The map preserves zero, addition, and negation."));

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Phase/Basic",
                "Integer golden-ratio phases form an injective additive orbit on the unit circle."),
            H("Golden Phase"),
            Blocks(
                opening,
                new DocumentBlock.DisplayFormula(Equal(phaseN, phaseValue)),
                new DocumentBlock.Section(
                    H("Additive laws"),
                    Blocks(
                        new DocumentBlock.Describe(
                            DescribeId.Create("zero"),
                            DescribeKind.Proposition,
                            H("Zero"),
                            DescribeStatement.FromLean(
                                LeanTheorem("D5/S1/Phase/Basic.goldenPhase_zero")),
                            DescribeProvenance.RepoDerived(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(Call("goldenPhase", Num(0)), Num(0))))),
                        new DocumentBlock.Describe(
                            DescribeId.Create("addition"),
                            DescribeKind.Proposition,
                            H("Addition"),
                            DescribeStatement.FromLean(
                                LeanTheorem("D5/S1/Phase/Basic.goldenPhase_add")),
                            DescribeProvenance.RepoDerived(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("goldenPhase", Add(n, m)),
                                    Add(phaseN, Call("goldenPhase", m)))))),
                        new DocumentBlock.Describe(
                            DescribeId.Create("negation"),
                            DescribeKind.Proposition,
                            H("Negation"),
                            DescribeStatement.FromLean(
                                LeanTheorem("D5/S1/Phase/Basic.goldenPhase_neg")),
                            DescribeProvenance.RepoDerived(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("goldenPhase", new Formula.Negate(n)),
                                    new Formula.Negate(phaseN))))))),
                new DocumentBlock.Section(
                    H("Orbit notation"),
                    Blocks(
                        Paragraph(
                            Text("The same orbit has sequence and set presentations:")),
                        new DocumentBlock.DisplayFormula(
                            Equal(new Formula.Subscript(Id("p"), n), phaseValue)),
                        new DocumentBlock.DisplayFormula(
                            new Formula.Sequence(phaseValue, n, new Formula.Integers())),
                        new DocumentBlock.DisplayFormula(
                            new Formula.SetBuilder(phaseValue, n, new Formula.Integers())))),
                new DocumentBlock.Describe(
                    DescribeId.Create("injectivity"),
                    DescribeKind.Theorem,
                    H("Injectivity"),
                    DescribeStatement.FromLean(injectivity),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(
                            Text("Two phases could coincide only if a nonzero integer multiple of "),
                            Math(new Formula.Phi()),
                            Text(" were an integer. Irrationality excludes this. No three-distance theorem is asserted here.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("visible-phase-and-hidden-prime-fiber"),
                    DescribeKind.Remark,
                    H("Visible phase and hidden prime fiber"),
                    DescribeStatement.FromFormula(Equal(Id("visiblePhase"), Id("T"))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The source treats the all-prime hidden fiber K_infinity = product_p Z_p as derived rather than postulated: accepting a compatible family of congruence readings incurs its dual completion. Its phase interpretation is the exact sequence 0 -> K_infinity -> Sigma_infinity -> T -> 0, where T is visible phase, K_infinity is the hidden all-prime fiber, and Sigma_infinity is the complete phase object.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("congruence-readings-close-under-dual-completion"),
                    DescribeKind.Remark,
                    H("Congruence readings close under dual completion"),
                    DescribeStatement.FromFormula(Equal(Id("dualK"), Id("QmodZ"))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "In the source's forward direction, a compatible family of congruence readings determines the completion, so hidden structure is the debt incurred by those readings. In the reverse direction, all continuous readings of the completion recover exactly Q/Z = union_m (1/m)Z/Z. Reading, completion, and reading again therefore form a closed loop on the pure congruence layer; the source points separately to the mixed-layer closure.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("the-two-phase-duality-loops"),
                    DescribeKind.Remark,
                    H("The two phase-duality loops"),
                    DescribeStatement.FromFormula(Equal(Id("dualSigma"), Id("Q"))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The source records both dual loops as closed: the pure congruence layer has K_infinity dual to Q/Z, and the mixed layer has Sigma_infinity dual to Q. Conversely, the dual of Q is the constructional origin assigned to Sigma_infinity. On this interpretation the complete phase object's measurable content is precisely the rational numbers, with readings and completion serving as each other's character groups.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("poisson-summation-is-the-cofinal-analytic-limit"),
                    DescribeKind.Remark,
                    H("Poisson summation is the cofinal analytic limit"),
                    DescribeStatement.FromFormula(Equal(
                        Call("theta", new Formula.Fraction(Num(1), Id("t"))),
                        Multiply(Call("sqrt", Id("t")), Call("theta", Id("t"))))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The source identifies classical Poisson summation and the theta functional equation as the analytic-layer limit of its finite statement along cofinal windows paired with the Archimedean place. It therefore narrows O-9 from reconstructing Poisson summation in general to internalizing that limiting passage. The finite layers are recorded as closed; the transition to the analytic limit remains the residual obligation.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("dense-phase-leaves-and-discrete-switching"),
                    DescribeKind.Remark,
                    H("Dense phase leaves and discrete switching"),
                    DescribeStatement.FromFormula(NotEqual(
                        Call("timeline", Id("a")),
                        Call("timeline", Id("b")))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The source's strict replacement for switchable parallel timelines is an uncountable family K_infinity/Z of leaves with one generator and different hidden offsets. Distinct leaves never intersect, while every leaf is dense, so they remain disjoint yet arbitrarily close everywhere. Continuous switching is ruled out; a genuine switch must be a discrete jump obeying a cocycle composition law, and every finite observation is said to be unable to distinguish such a jump from ordinary motion. The continuous phase leaf and discrete address leaf are then read as wave and particle. Finally, every switch must pass through an address reading and enter the ledger, giving the slogan that observation is bookkeeping.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("quasiperiodic-return-is-not-exact-recurrence"),
                    DescribeKind.Remark,
                    H("Quasiperiodic return is not exact recurrence"),
                    DescribeStatement.FromFormula(NotEqual(
                        new Formula.Modulo(Multiply(Id("k"), new Formula.Phi()), Num(1)),
                        Num(0))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The cosmological reading of eternal recurrence is rejected. Poincare recurrence supplies arbitrarily close return in finite phase space, but exact periodic repetition would require a nonzero k with k*phi equal to zero modulo one, which irrationality forbids. The source reports a smallest sampled distance of 2.3e-6 without equality and, at tolerance 1e-4, a first return at Fibonacci index 6765. Thus the golden rotation permits Fibonacci-scale approximate returns while the minimally complex golden word remains aperiodic: quasiperiodicity is not periodicity, and the three-distance theorem is offered as a counterexample to exact recurrence rather than a proof of it. The weaker mathematical metaphor of approximate return and self-similar reappearance is retained. Nietzsche's ethical imperative is classified outside truth-valued mathematics, because it is a prescription rather than a claim about the world.")))))));
    }
}
