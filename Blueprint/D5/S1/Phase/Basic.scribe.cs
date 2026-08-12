using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = DefinitionDsl.Id("n");
        var m = DefinitionDsl.Id("m");
        var phaseN = Call("goldenPhase", n);
        var phaseValue = new Formula.Modulo(
            Multiply(n, new Formula.Phi()),
            Num(1));
        var opening = Paragraph(
            Ref("D5/S1/Phase/Basic"),
            Text(" maps an integer "),
            Math(n),
            Text(" to "),
            Math(phaseValue),
            Text(" in the additive circle. The map preserves zero, addition, and negation."));

        return DocumentDefinition.Create(ScribeNode.Create("Integer golden-ratio phases form an injective additive orbit on the unit circle.",
H("Golden Phase"),
Blocks(
                opening,
                new DocumentBlock.DisplayFormula(Equal(phaseN, phaseValue)),
                new DocumentBlock.Section(
                    H("Additive laws"),
                    Blocks(
                        Describe.Lean(
                            DescribeId.Create("zero"),
                            DeclarationHandle.Create("D5/S1/Phase/Basic.goldenPhase_zero"),
                            H("Zero"),
                            StatementSource.FromAuthor(In(Seq(Operatorname, Grp(F.Id("goldenPhase")), Open, D(0), Close, Eq, D(0)))),
                            AssessedProvenance.FromRepo(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(Call("goldenPhase", Num(0)), Num(0)))),
                            DescribeRole.Proposition),
                        Describe.Lean(
                            DescribeId.Create("addition"),
                            DeclarationHandle.Create("D5/S1/Phase/Basic.goldenPhase_add"),
                            H("Addition"),
                            StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("n"), Comma, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc, Operatorname, Grp(F.Id("goldenPhase")), Open, F.Id("n"), Plus, F.Id("m"), Close, Eq, Operatorname, Grp(F.Id("goldenPhase")), Open, F.Id("n"), Close, Plus, Operatorname, Grp(F.Id("goldenPhase")), Open, F.Id("m"), Close))),
                            AssessedProvenance.FromRepo(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("goldenPhase", Add(n, m)),
                                    Add(phaseN, Call("goldenPhase", m))))),
                            DescribeRole.Proposition),
                        Describe.Lean(
                            DescribeId.Create("negation"),
                            DeclarationHandle.Create("D5/S1/Phase/Basic.goldenPhase_neg"),
                            H("Negation"),
                            StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc, Operatorname, Grp(F.Id("goldenPhase")), Open, Minus, F.Id("n"), Close, Eq, Minus, Operatorname, Grp(F.Id("goldenPhase")), Open, F.Id("n"), Close))),
                            AssessedProvenance.FromRepo(),
                            Blocks(new DocumentBlock.DisplayFormula(
                                Equal(
                                    Call("goldenPhase", new Formula.Negate(n)),
                                    new Formula.Negate(phaseN)))),
                            DescribeRole.Proposition))),
                new DocumentBlock.Section(
                    H("Orbit notation"),
                    Blocks(
                        Paragraph(
                            Text("The same orbit has sequence and set presentations:")),
                        new DocumentBlock.DisplayFormula(
                            Equal(new Formula.Subscript(DefinitionDsl.Id("p"), n), phaseValue)),
                        new DocumentBlock.DisplayFormula(
                            new Formula.Sequence(phaseValue, n, new Formula.Integers())),
                        new DocumentBlock.DisplayFormula(
                            new Formula.SetBuilder(phaseValue, n, new Formula.Integers())))),
                Describe.Lean(
                    DescribeId.Create("injectivity"),
                    DeclarationHandle.Create("D5/S1/Phase/Basic.goldenPhase_injective"),
                    H("Injectivity"),
                    StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("n"), Comma, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc, Operatorname, Grp(F.Id("goldenPhase")), Open, F.Id("n"), Close, Eq, Operatorname, Grp(F.Id("goldenPhase")), Open, F.Id("m"), Close, Sp, Rightarrow, Sp, F.Id("n"), Eq, F.Id("m")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(
                            Text("Two phases could coincide only if a nonzero integer multiple of "),
                            Math(new Formula.Phi()),
                            Text(" were an integer. Irrationality excludes this. No three-distance theorem is asserted here."))),
                    DescribeRole.Theorem),
                Describe.Remark(
                DescribeId.Create("visible-phase-and-hidden-prime-fiber"),
                H("Visible phase and hidden prime fiber"),
                Equal(DefinitionDsl.Id("visiblePhase"), DefinitionDsl.Id("T")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                        "The source treats the all-prime hidden fiber K_infinity = product_p Z_p as derived rather than postulated: accepting a compatible family of congruence readings incurs its dual completion. Its phase interpretation is the exact sequence 0 -> K_infinity -> Sigma_infinity -> T -> 0, where T is visible phase, K_infinity is the hidden all-prime fiber, and Sigma_infinity is the complete phase object.")))),
                Describe.Remark(
                DescribeId.Create("congruence-readings-close-under-dual-completion"),
                H("Congruence readings close under dual completion"),
                Equal(DefinitionDsl.Id("dualK"), DefinitionDsl.Id("QmodZ")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                        "In the source's forward direction, a compatible family of congruence readings determines the completion, so hidden structure is the debt incurred by those readings. In the reverse direction, all continuous readings of the completion recover exactly Q/Z = union_m (1/m)Z/Z. Reading, completion, and reading again therefore form a closed loop on the pure congruence layer; the source points separately to the mixed-layer closure.")))),
                Describe.Remark(
                DescribeId.Create("the-two-phase-duality-loops"),
                H("The two phase-duality loops"),
                Equal(DefinitionDsl.Id("dualSigma"), DefinitionDsl.Id("Q")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                        "The source records both dual loops as closed: the pure congruence layer has K_infinity dual to Q/Z, and the mixed layer has Sigma_infinity dual to Q. Conversely, the dual of Q is the constructional origin assigned to Sigma_infinity. On this interpretation the complete phase object's measurable content is precisely the rational numbers, with readings and completion serving as each other's character groups.")))),
                Describe.Remark(
                DescribeId.Create("dense-phase-leaves-and-discrete-switching"),
                H("Dense phase leaves and discrete switching"),
                NotEqual(
                        Call("timeline", DefinitionDsl.Id("a")),
                        Call("timeline", DefinitionDsl.Id("b"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                        "The source's strict replacement for switchable parallel timelines is an uncountable family K_infinity/Z of leaves with one generator and different hidden offsets. Distinct leaves never intersect, while every leaf is dense, so they remain disjoint yet arbitrarily close everywhere. Continuous switching is ruled out; a genuine switch must be a discrete jump obeying a cocycle composition law, and every finite observation is said to be unable to distinguish such a jump from ordinary motion. The continuous phase leaf and discrete address leaf are then read as wave and particle. Finally, every switch must pass through an address reading and enter the ledger, giving the slogan that observation is bookkeeping.")))))));
    }
}
