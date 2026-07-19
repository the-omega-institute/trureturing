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
                        "The source records both dual loops as closed. The continuous character group of K_infinity is exactly Q/Z, and the continuous character group of Sigma_infinity is exactly Q. Conversely, the dual of Q is the constructional origin assigned to Sigma_infinity. In this statement, readings mean continuous characters; it does not classify all measurable observables. Reading and completion serve as each other's character groups.")))),
                new DocumentBlock.Describe(
                    DescribeId.Create("dense-phase-leaves-and-discrete-switching"),
                    DescribeKind.Remark,
                    H("Dense phase leaves and discrete switching"),
                    DescribeStatement.FromFormula(NotEqual(
                        Call("timeline", Id("a")),
                        Call("timeline", Id("b")))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The source's strict replacement for switchable parallel timelines is an uncountable family K_infinity/Z of leaves with one generator and different hidden offsets. Distinct leaves never intersect, while every leaf is dense, so they remain disjoint yet arbitrarily close everywhere. Continuous switching is ruled out; a genuine switch must be a discrete jump obeying a cocycle composition law, and every finite observation is said to be unable to distinguish such a jump from ordinary motion. The continuous phase leaf and discrete address leaf are then read as wave and particle. Finally, every switch must pass through an address reading and enter the ledger, giving the slogan that observation is bookkeeping.")))))));
    }
}
