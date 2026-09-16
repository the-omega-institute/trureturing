using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class FinitePathCoherenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite sequential qubit channels multiply coherence; its phase, attenuation, and closed-path gauge laws follow.",
        H("Finite-Path Coherence"),
        Blocks(
            Paragraph(Text("Let M be the complex two-by-two matrices and Q the completely positive, "
                + "trace-preserving channels on them. Matrix action converts through CStarMatrix. "
                + "The imaginary unit is I. The following notation fixes the Hermitian sector and edge coefficient.")),
            Paragraph(Math(Disp(And(
                Equal(Call("sourceMatrix", A, B, Dd), Matrix(A, B, Conj(B), Dd)),
                Equal(Call("coefficient", Vv, Tt),
                    Multiply(Call("ofReal", Vv), Phase(Tt))))))),
            Paragraph(Text("A quiver has an arbitrary vertex type V and arbitrary arrow types Hom(x,y). "
                + "Family(T) below means an assignment in T to every arrow, with its endpoints implicit. "
                + "Path(i,j) contains every finite directed path, including the empty path. "
                + "Weight is the ordered product of edge values, with empty product one; addWeight is "
                + "the sum, with empty sum zero. The path channel applies each edge after the preceding path; "
                + "its empty case is edgeChannel(1,0).")),
            Paragraph(Text("Sequential application is licensed by independently prepared auxiliary "
                + "resources, or by a factorization already established in the physical model. "
                + "Correlated resource reuse does not by itself supply this factorization.")),
            Describe.Lean(
                DescribeId.Create("canonical-edge-action"),
                Handle("edgeChannel_action"),
                H("Canonical Edge Action"),
                StatementSource.FromAuthor(EdgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The channel is supplied by the finite Kraus construction. "
                    + "Its two Kraus matrices are diagonal, with diagonals (coefficient(v,theta),1) "
                    + "and (sqrt(1-v squared),0). Normalization and the displayed action hold for "
                    + "every admissible visibility and every real phase."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sequential-path-action"),
                Handle("path_channel_action"),
                H("Sequential Path Action"),
                StatementSource.FromAuthor(PathFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The edge premise specifies the whole Hermitian matrix action. "
                    + "Channel composition preserves both diagonal entries and multiplies the upper "
                    + "coherence by the path product; the lower entry is its conjugate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polar-and-gauge-path-law"),
                Handle("source_path_coherence"),
                H("Polar Coordinates and Vertex Gauge"),
                StatementSource.FromAuthor(SourceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The map angle is the quotient from real phases to Real.Angle, "
                    + "so phase equality is modulo two pi. The principal argument is used only for "
                    + "the polar reconstruction. The norm and its negative logarithm retain attenuation. "
                    + "For each real vertex reference alpha, the transformed channels are canonical "
                    + "edge channels with phase theta(e)+alpha(y)-alpha(x). On a closed path their "
                    + "complex multiplier, phase-norm pair, and actual Hermitian matrix action agree exactly."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        "D5/S3/Quantum/Decoherence/FinitePathCoherence." + name);

    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula Dd => F.Id("d");
    private static Formula Vv => F.Id("v");
    private static Formula Tt => F.Id("theta");
    private static Formula P => F.Id("p");
    private static Formula Zp => F.Id("zP");
    private static Formula Zgp => F.Id("zgP");
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Family(Formula codomain) => Call("Family", codomain);
    private static Formula Conj(Formula value) => Seq(Overline, Grp(value));
    private static Formula Phase(Formula value) =>
        Call("exp", Multiply(Call("ofReal", value), F.Id("I")));
    private static Formula Norm(Formula value) => new Formula.Norm(value);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Matrix(Formula aa, Formula bb, Formula cc, Formula dd) =>
        Seq(Begin, Grp(F.Id("pmatrix")), aa, Amp, bb, RowBreak,
            cc, Amp, dd, End, Grp(F.Id("pmatrix")));
    private static Formula Entry(long i, long j) =>
        new Formula.Subscript(F.Id("rho"), Seq(Num(i), Comma, Num(j)));
    private static Formula Sector(Formula coherence) => Call("sourceMatrix", A, coherence, Dd);
    private static Formula Action(Formula channel, Formula matrix) => Call("matrixAction", channel, matrix);
    private static Formula PathAction(string family) =>
        Action(Call("pathChannel", F.Id(family), P), Sector(B));
    private static Formula Weight(string family) => Call("weight", F.Id(family), P);
    private static Formula PolarPair(Formula value) =>
        Seq(Open, Call("angle", Call("arg", value)), Comma, Sp, Norm(value), Close);
    private static Formula EdgeValue(string name) => Call(name, F.Id("e"));
    private static Formula EdgeCoefficient => Call("coefficient", EdgeValue("v"), EdgeValue("theta"));
    private static Formula ReferenceDifference(string target, string source) =>
        Subtract(Call("alpha", F.Id(target)), Call("alpha", F.Id(source)));
    private static Formula GaugeFactor(string target, string source) => Phase(ReferenceDifference(target, source));

    private static Formula ForEdges(Formula body) =>
        All("x", F.Id("V"), All("y", F.Id("V"),
            All("e", Call("Hom", F.Id("x"), F.Id("y")), body)));

    private static Formula ForMatrices(Formula body) =>
        All("a", Real, All("d", Real, All("b", Complex, body)));

    private static Formula ForPaths(Formula body) =>
        All("i", F.Id("V"), All("j", F.Id("V"),
            All("p", Call("Path", F.Id("i"), F.Id("j")), ForMatrices(body))));

    private static Formula QuiverScope(Formula body) =>
        All("V", F.Id("Type"), All("H", Call("Quiver", F.Id("V")), body));

    private static Formula Bounds(Formula value) =>
        And(new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, value),
            new Formula.Relation(value, FormulaRelationOperator.LessThanOrEqual, Num(1)));

    private static Formula EdgeHypothesis(Formula multiplier) =>
        ForEdges(ForMatrices(Equal(Action(EdgeValue("C"), Sector(B)),
            Sector(Multiply(multiplier, B)))));

    private static Formula Let(Formula equations) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, equations, Semi, Sp);

    private static Formula EdgeFormula()
    {
        Formula result = Equal(Action(Call("edgeChannel", Vv, Tt), F.Id("rho")),
            Matrix(Entry(0, 0), Multiply(Call("coefficient", Vv, Tt), Entry(0, 1)),
                Multiply(Conj(Call("coefficient", Vv, Tt)), Entry(1, 0)), Entry(1, 1)));
        return Disp(All("v", Real, All("theta", Real,
            ImpliesFormula(Bounds(Vv), All("rho", F.Id("M"), result)))));
    }

    private static Formula PathFormula() => Disp(QuiverScope(
        All("C", Family(F.Id("Q")), All("z", Family(Complex),
            ImpliesFormula(EdgeHypothesis(EdgeValue("z")),
                ForPaths(Equal(PathAction("C"), Sector(Multiply(Weight("z"), B)))))))));

    private static Formula SourceFormula()
    {
        Formula definitions = Let(And(ForEdges(Equal(EdgeValue("z"), EdgeCoefficient)),
            Equal(Zp, Weight("z"))));
        Formula attenuation = Equal(new Formula.Negate(Call("log", Norm(Zp))),
            Call("addWeight", Seq(Open, F.Id("e"), Mapsto,
                new Formula.Negate(Call("log", EdgeValue("v"))), Close), P));
        Formula polar = Equal(Zp, Multiply(Call("ofReal", Norm(Zp)),
            Phase(Call("arg", Zp))));
        Formula body = And(Equal(PathAction("C"), Sector(Multiply(Zp, B))),
            And(NotEqual(Zp, Num(0)),
            And(Equal(Norm(Zp), Weight("v")),
            And(Bounds(Norm(Zp)),
            And(Equal(Call("angle", Call("arg", Zp)),
                Call("angle", Call("addWeight", Tt, P))),
            And(attenuation, And(polar, GaugeFormula())))))));
        return Disp(QuiverScope(All("C", Family(F.Id("Q")),
            All("v", Family(Real), All("theta", Family(Real),
                ImpliesFormula(And(ForEdges(Bounds(EdgeValue("v"))),
                    EdgeHypothesis(EdgeCoefficient)), ForPaths(Seq(definitions, body))))))));
    }

    private static Formula GaugeFormula()
    {
        Formula definitions = Let(And(ForEdges(Equal(EdgeValue("zg"),
                Multiply(GaugeFactor("y", "x"), EdgeValue("z")))),
            And(ForEdges(Equal(EdgeValue("Cg"), Call("edgeChannel", EdgeValue("v"),
                Add(EdgeValue("theta"), ReferenceDifference("y", "x"))))),
                Equal(Zgp, Weight("zg")))));
        Formula closed = Equal(F.Id("i"), F.Id("j"));
        Formula result = And(Equal(Zgp, Multiply(GaugeFactor("j", "i"), Zp)),
            And(ImpliesFormula(closed, Equal(Zgp, Zp)),
            And(ImpliesFormula(closed, Equal(PolarPair(Zgp), PolarPair(Zp))),
                ImpliesFormula(closed, Equal(PathAction("Cg"), PathAction("C"))))));
        return All("alpha", Seq(F.Id("V"), To, Real), Seq(definitions, result));
    }
}
