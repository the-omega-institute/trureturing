using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class RankOneFeedbackProtocolDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite rank-one feedback, independent control, and response effects.",
        H("Rank-One Feedback and the First Read"), Blocks(
            Describe.Lean(DescribeId.Create("rankone-projector-positive"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.projector_positive"),
                H("Positivity of each basis projection"), StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("Fintype", F.Id("n")), CloseBracket,
                    OpenBracket, C("DecidableEq", F.Id("n")), CloseBracket, Comma,
                    Forall, Sp, F.Id("s"), Colon, F.Id("n"), Comma,
                    Seq(Operatorname, Grp(F.Id("Matrix")), Dot, C("PosSemidef", C("projector", F.Id("s"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite index type with decidable equality and every index s, the basis projection projector s = Matrix.single s s 1 is positive semidefinite. The nonnegativity of terminal record masses follows by applying this projection to each read outcome; it also supplies positive basis inputs for the channel time-reversal contradiction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rankone-first-read"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.actual_protocol_tv_supremum"),
                H("The actual finite protocol supremum"), StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("Fintype", F.Id("n")), CloseBracket,
                    OpenBracket, C("DecidableEq", F.Id("n")), CloseBracket, Comma,
                    Forall, Sp, F.Id("U"), Colon, C("WaitFamily", F.Id("n")), Comma,
                    Forall, Sp, F.Id("X"), Comma, F.Id("Y"), Colon, C("ComplexMatrix", F.Id("n")), Comma,
                    C("UnitaryWaits", F.Id("U")), Land, Sp, C("PSD", F.Id("X")), Land, Sp,
                    C("PSD", F.Id("Y")), Land, Sp, C("Tr", F.Id("X")), Eq, C("Tr", F.Id("Y")),
                    Rightarrow, Sp, C("ProtocolTVSup", F.Id("U"), F.Id("X"), F.Id("Y")), Eq,
                    C("FirstReadTVSup", F.Id("U"), F.Id("X"), F.Id("Y"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A unitary waiting semigroup on actual complex matrices is indexed by nonnegative real times. A finite protocol consists of Stop, a wait, or a complete rank-one Lueders read with one continuation per observed outcome. Terminal records retain all read outcomes.")),
                    Paragraph(Text("Before the first read, waits merge by the semigroup law. No-read Stop has zero distinction for equal-trace inputs. At a first outcome s, the unnormalized branch is its probability times the basis projection. The suffix law starts at that projection and is defined even when the original first probability is zero. Its nonnegative mass sums to one, so the complete-record total variation is exactly that of the first read."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rankone-finite-random-control"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.randomized_protocol_tv_supremum"),
                H("Finite independent control and coarse output"), StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("Fintype", F.Id("n")), CloseBracket,
                    OpenBracket, C("DecidableEq", F.Id("n")), CloseBracket, Comma,
                    Forall, Sp, F.Id("U"), Colon, C("WaitFamily", F.Id("n")), Comma,
                    Forall, Sp, F.Id("X"), Comma, F.Id("Y"), Colon, C("ComplexMatrix", F.Id("n")), Comma,
                    C("UnitaryWaits", F.Id("U")), Land, Sp, C("PSD", F.Id("X")), Land, Sp,
                    C("PSD", F.Id("Y")), Land, Sp, C("Tr", F.Id("X")), Eq, C("Tr", F.Id("Y")),
                    Rightarrow, Sp, C("RandomProtocolTVSup", F.Id("U"), F.Id("X"), F.Id("Y")), Eq,
                    C("FirstReadTVSup", F.Id("U"), F.Id("X"), F.Id("Y")), Land, Sp, RowBreak,
                    Forall, Sp, F.Id("R"), Colon, C("RandomControl", F.Id("n")), Comma,
                    Forall, Sp, F.Id("m"), Colon, Seq(Mathbb, Grp(F.Id("N"))), Comma,
                    Forall, Sp, F.Id("W"), Colon,
                    C("OutputKernel", C("RandomRecord", F.Id("R")), C("Fin", F.Id("m"))), Comma,
                    C("Stochastic", F.Id("W")), Rightarrow, Sp,
                    C("TV", C("W", C("randomLaw", F.Id("U"), F.Id("R"), F.Id("X"))),
                        C("W", C("randomLaw", F.Id("U"), F.Id("R"), F.Id("Y")))), Leq, Sp,
                    C("TV", C("randomLaw", F.Id("U"), F.Id("R"), F.Id("X")),
                        C("randomLaw", F.Id("U"), F.Id("R"), F.Id("Y")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite control seed is sampled independently of the unknown input. It selects a finite feedback tree, whose later decisions use actual recorded outcomes. The complete record includes the seed. Its total variation is a convex combination of deterministic distinctions and is dominated by one deterministic tree. Arbitrary finite stochastic output kernels contract that law; their coefficients can depend on the recorded seed and history, but have no access to the unknown input."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rankone-arbitrary-random-control"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.arbitrary_random_control_event_bound"),
                H("Arbitrary independent probability seeds"), StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("Fintype", F.Id("n")), CloseBracket,
                    OpenBracket, C("DecidableEq", F.Id("n")), CloseBracket, Comma,
                    Forall, Sp, F.Id("U"), Colon, C("WaitFamily", F.Id("n")), Comma,
                    Forall, Sp, F.Id("X"), Comma, F.Id("Y"), Colon, C("ComplexMatrix", F.Id("n")), Comma,
                    Forall, Sp, F.Id("S"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("MeasurableSpace", F.Id("S")), CloseBracket, Comma,
                    Forall, Sp, F.Id("mu"), Colon, C("Measure", F.Id("S")), Comma,
                    Forall, Sp, F.Id("strategy"), Colon, C("ProtocolFamily", F.Id("S"), F.Id("n")), Comma,
                    Forall, Sp, F.Id("event"), Colon, C("FiniteEventFamily", F.Id("strategy")), Comma,
                    C("UnitaryWaits", F.Id("U")), Land, Sp, C("Density", F.Id("X")), Land, Sp,
                    C("Density", F.Id("Y")), Land, Sp, C("ProbabilityMeasure", F.Id("mu")), Land, Sp,
                    C("Integrable", C("eventWeight", F.Id("U"), F.Id("strategy"), F.Id("event"), F.Id("X")), F.Id("mu")), Land, Sp,
                    C("Integrable", C("eventWeight", F.Id("U"), F.Id("strategy"), F.Id("event"), F.Id("Y")), F.Id("mu")), Rightarrow, Sp,
                    Bar, C("Integral", C("eventWeight", F.Id("U"), F.Id("strategy"), F.Id("event"), F.Id("X")), F.Id("mu")), Minus,
                    C("Integral", C("eventWeight", F.Id("U"), F.Id("strategy"), F.Id("event"), F.Id("Y")), F.Id("mu")), Bar, Leq, Sp,
                    C("FirstReadTVSup", F.Id("U"), F.Id("X"), F.Id("Y"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary probability space of independent seeds, each seed selects a finite feedback tree with arbitrary nonnegative real waits. An event can depend on the seed and the whole observed record. Whenever its two actual probability functions are integrable, its integrated probability gap is at most the first-read supremum. Thus arbitrary measurable random control has the same event bound; deterministic one-read protocols supply the reverse supremum bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rankone-protocol-effect-span"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/RankOneFeedbackProtocol.actual_protocol_effect_correspondence"),
                H("Actual histories supply exactly the first-read effect span"), StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, F.Id("Type"), Comma,
                    OpenBracket, C("Fintype", F.Id("n")), CloseBracket,
                    OpenBracket, C("DecidableEq", F.Id("n")), CloseBracket, Comma,
                    Forall, Sp, F.Id("U"), Colon, C("WaitFamily", F.Id("n")), Comma, C("UnitaryWaits", F.Id("U")), Rightarrow, Sp,
                    C("RealSpan", C("AllHistoryEffects", F.Id("U"))), Eq,
                    C("firstEffectSpan", F.Id("U")), Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("P"), Colon, C("Protocol", F.Id("n")), Comma,
                    Forall, Sp, F.Id("X"), Colon, C("ComplexMatrix", F.Id("n")), Comma,
                    Forall, Sp, F.Id("h"), Colon, C("Record", F.Id("P")), Comma,
                    C("Re", C("Tr", Seq(C("recordEffect", F.Id("U"), F.Id("P"), F.Id("h")),
                        F.Id("X")))), Eq, C("ludersLaw", F.Id("U"), F.Id("P"), F.Id("X"), F.Id("h")), Close, Land, Sp,
                    Forall, Sp, F.Id("P"), Colon, C("Protocol", F.Id("n")), Comma,
                    Forall, Sp, F.Id("h"), Colon, C("Record", F.Id("P")), Comma,
                    C("PSD", C("recordEffect", F.Id("U"), F.Id("P"), F.Id("h"))), Land, Sp,
                    C("PSD", Seq(D(1), Minus, C("recordEffect", F.Id("U"), F.Id("P"), F.Id("h"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every complete history has an explicit complex Heisenberg effect obtained from the actual unitary waits and rank-one sandwiches. Its trace probability equals the operational Lueders law. Every actual history effect and its complement in the identity are positive semidefinite, by induction through unitary conjugations and rank-one sandwiches. The real span of all these effects equals the span of the identity and all first-read effects. Rank-one collapse and the semigroup identity prove the forward inclusion; Stop and one-read histories prove the reverse inclusion.")),
                    Paragraph(Text("This explicit correspondence is required before any finite-dimensional readout-fiber supplier can be applied. It does not identify a product-generated algebra with the actual effect span. Measurement-relative compression and broader no-disturbance structure are prior work of Bluhm, Rauber and Wolf (arXiv:1708.04898v4) and Koashi and Imoto (quant-ph/0101144), respectively."))), DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
