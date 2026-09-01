using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class VisibleHiddenMotionClassificationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/VisibleHiddenMotionClassification."
            + "universal_solenoid_visible_hidden_motion_classification";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The universal solenoid is connected but not path-connected, and every continuous "
            + "history has one visible lift and one constant hidden offset. Distinct hidden "
            + "addresses instead determine nonzero discrete jumps with no continuous real "
            + "extension.",
        H("Universal-Solenoid Visible-Hidden Motion Classification"),
        Blocks(Describe.Lean(
            DescribeId.Create("universal-solenoid-visible-hidden-motion-classification"),
            DeclarationHandle.Create(Declaration),
            H("Visible phase paths and hidden address jumps are exhaustive"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The universal solenoid is connected, but an explicit hidden-kernel point "
                        + "lies outside the real-flow orbit of zero. The frozen path-orbit "
                        + "classification therefore supplies both non-path-connectedness and "
                        + "the exact path-reachable set of every point.")),
                Paragraph(Text(
                    "Every continuous solenoid path has a unique real lift normalized at time "
                        + "zero and one constant element of the visible projection kernel. This "
                        + "is the whole-solenoid phase branch of the classification.")),
                Paragraph(Text(
                    "For any two distinct hidden addresses, no continuous unit-interval hidden "
                        + "motion joins them. Their difference canonically generates a nonzero "
                        + "integer-parameter additive action, and continuous hidden-flow rigidity "
                        + "prevents that action, or any nonzero integer action, from extending to "
                        + "a continuous additive real flow."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/GoldenCoding/VisibleHiddenMotionDichotomy")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/HiddenFlow/DiscreteRigidity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Solenoid/StreamlineDecomposition")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula solenoid = F.Id("UniversalSolenoid");
        Formula hidden = F.Id("HiddenAddress");
        Formula unitInterval = F.Id("unitInterval");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula t = F.Id("t");
        Formula path = GammaLower;
        Formula data = F.Id("data");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula motion = F.Id("motion");
        Formula jump = F.Id("jump");
        Formula flow = F.Id("flow");

        Formula connectedClause = Seq(
            Call("ConnectedSpace", solenoid), Sp, Land, Sp,
            Neg, Sp, Call("PathConnectedSpace", solenoid));

        Formula orbitClause = Seq(
            Forall, Sp, Typed(Seq(x, Comma, Sp, y), solenoid), Comma, Sp,
            Call("Joined", x, y), Sp, Iff, Sp,
            Exists, Sp, Typed(t, real), Comma, Sp,
            y, Sp, Eq, Sp, Call("realFlow", t), Sp, Plus, Sp, x);

        Formula continuousSolenoidPath = Call("C", real, solenoid);
        Formula continuousRealPath = Call("C", real, real);
        Formula hiddenKernel = Seq(Ker, Open, F.Id("projection"), Close);
        Formula dataType = Seq(
            continuousRealPath, Sp, Times, Sp, hiddenKernel);
        Formula visibleLift = Call("fst", data);
        Formula hiddenOffset = Call("snd", data);
        Formula decompositionClause = Seq(
            Forall, Sp, Typed(path, continuousSolenoidPath), Comma, Sp,
            Exists, Bang, Sp, Typed(data, dataType), Comma, Sp,
            Apply(visibleLift, D(0)), Sp, Eq, Sp,
            Call("baseRepresentative", path, D(0)), Sp, Land, Sp,
            Forall, Sp, Typed(t, real), Comma, Sp,
            Apply(path, t), Sp, Eq, Sp,
            Call("realFlow", Apply(visibleLift, t)), Sp, Plus, Sp, hiddenOffset);

        Formula hiddenMotionType = new Formula.TypeArrow(unitInterval, hidden);
        Formula continuousMotion = Seq(
            Call("Continuous", motion), Sp, Land, Sp,
            Apply(motion, D(0)), Sp, Eq, Sp, first, Sp, Land, Sp,
            Apply(motion, D(1)), Sp, Eq, Sp, second);
        Formula noHiddenSliding = Seq(
            Neg, Sp, Exists, Sp, Typed(motion, hiddenMotionType), Comma, Sp,
            continuousMotion);

        Formula jumpType = Call("AddHom", integer, hidden);
        Formula flowType = Call("CAddHom", real, hidden);
        Formula restriction = Call(
            "comp", Call("toAddMonoidHom", flow), Call("castAddHom", integer, real));
        Formula noContinuousExtension = Seq(
            Neg, Sp, Exists, Sp, Typed(flow, flowType), Comma, Sp,
            restriction, Sp, Eq, Sp, jump);
        Formula generatedJump = Seq(
            Exists, Sp, Typed(jump, jumpType), Comma, Sp,
            Apply(jump, D(1)), Sp, Eq, Sp,
            second, Sp, Minus, Sp, first, Sp, Land, Sp,
            jump, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            noContinuousExtension);
        Formula hiddenChangeClause = Seq(
            Forall, Sp, Typed(Seq(first, Comma, Sp, second), hidden), Comma, Sp,
            first, Sp, Neq, Sp, second, Sp, Rightarrow, Sp,
            Open, Open, noHiddenSliding, Close, Sp, Land, Sp,
            Open, generatedJump, Close, Close);

        Formula allJumpClause = Seq(
            Forall, Sp, Typed(jump, jumpType), Comma, Sp,
            jump, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            noContinuousExtension);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, connectedClause, Close, Sp, Land, RowBreak, Grp(),
            Open, orbitClause, Close, Sp, Land, RowBreak, Grp(),
            Open, decompositionClause, Close, Sp, Land, RowBreak, Grp(),
            Open, hiddenChangeClause, Close, Sp, Land, RowBreak, Grp(),
            Open, allJumpClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
