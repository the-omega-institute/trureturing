using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FaithfulConditionalGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/FaithfulConditionalGap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squared trace distance gives a strict complete versus conditional contraction gap.",
        H("A faithful divergence with different complete and conditional coefficients"),
        Blocks(
            Paragraph(Text(
                "DensityState(A) is a positive semidefinite complex CStarMatrix of trace one. "
                + "QuantumChannel(A,B) is the canonical completely positive, trace-preserving "
                + "map between these matrix spaces. All index types below lie in Type and "
                + "carry the displayed finite enumerations and decidable equalities. "
                + "The reference is the first coordinate. The map marginalRight traces out "
                + "the second coordinate; referenceState(N,rho) applies the channel to that "
                + "coordinate and preserves the reference marginal.")),
            Describe.Lean(
                DescribeId.Create("faithful-conditional-finite-divergence"),
                DeclarationHandle.Create(Prefix + "FiniteDivergence"),
                H("Finite faithful quantum divergences"),
                StatementSource.FromAuthor(Disp(DivergenceFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "FiniteDivergence stores a real-valued family D on density-state pairs "
                    + "over every finite index type, together with nonnegativity, zero exactly "
                    + "on equal states, and data processing for every canonical CPTP channel "
                    + "between arbitrary finite source and target dimensions. No additivity "
                    + "or direct-sum law is imposed. The family D in the display has precisely "
                    + "these density-state domains."))), DescribeRole.Definition),
            RatioDescribe(false), RatioDescribe(true),
            CoefficientDescribe(false), CoefficientDescribe(true),
            Describe.Lean(
                DescribeId.Create("faithful-conditional-gap-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A strict gap with unrestricted finite quantum references"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take D(rho,sigma)=T(rho,sigma)^2, where T is one half of the trace "
                        + "norm of rho minus sigma. The channel measures in the binary "
                        + "computational basis and applies W=((3/4,1/4),(1/4,3/4)). Its four "
                        + "Kraus matrices are sqrt(W(y,x)) times the matrix unit at (y,x); "
                        + "their adjoint products sum to the identity. Its action is the "
                        + "diagonal matrix with entries (3X(0,0)+X(1,1))/4 and "
                        + "(X(0,0)+3X(1,1))/4.")),
                    Paragraph(Text(
                        "For every finite quantum reference R, an equal-marginal difference "
                        + "X has X((r,0),(s,0))+X((r,1),(s,1))=0 for every r,s, including "
                        + "off-diagonal reference entries. Consequently the amplified channel "
                        + "sends X to one half of its binary pinching. That pinching is "
                        + "(X+UXU*)/2 for U=I_R tensor diag(1,-1), so its trace norm cannot "
                        + "increase. Squaring yields the uniform complete bound 1/4.")),
                    Paragraph(Text(
                        "In the ordered basis (0,0),(0,1),(1,0),(1,1),(2,0),(2,1), use the "
                        + "actual density states with diagonals (1/2,0,0,0,1/2,0) and "
                        + "(0,0,1/2,0,0,1/2). Their channel outputs have diagonals "
                        + "(3/8,1/8,0,0,3/8,1/8) and (0,0,3/8,1/8,1/8,3/8). Their "
                        + "reference marginals are (1/2,0,1/2) and (0,1/2,1/2), and are "
                        + "preserved by the channel. The input, output and reference trace "
                        + "distances are 1, 3/4 and 1/2. The conditional denominator is "
                        + "3/4, its numerator is 5/16, and the ratio is 5/12.")),
                    Paragraph(Text(
                        "For heterogeneous CPTP data processing, decompose a Hermitian "
                        + "matrix into positive and negative Jordan parts. Positivity, trace "
                        + "preservation and the trace-norm triangle inequality give contraction "
                        + "without identifying the source and target dimensions. Trace norm "
                        + "vanishes only at zero; nonnegative squaring preserves data "
                        + "processing and faithfulness. The conditional ratios are bounded "
                        + "above by one. The conclusion answers the faithful-divergence "
                        + "existential in Section 9, second bullet, without specializing to "
                        + "relative entropy or determining either exact optimal coefficient.")),
                    Paragraph(Text(
                        "The endpoint and its consumed proof helpers have proof_shape bind-only. "
                        + "The endpoint is admitted as an external open-problem resolution; "
                        + "no escape witness is claimed. The positive-result four-slot audit "
                        + "is unfinished under issue 30303, comment 6874572340: exact "
                        + "sourceSelection and whole-family observational dependence are missing. "
                        + "This is not a declared_validated registration."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hirche-george-nuradha-wilde-2026-faithful-conditional-gap"),
                    ResolutionKind.Proved)))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Id(name)));
    private static Formula At(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Par(Formula x) => Seq(F.Open, x, F.Close);
    private static Formula Typed(string name, Formula type) => Par(Seq(Id(name), Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Iff, Par(y));
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Type() => Op("Type");
    private static Formula Product(Formula x, Formula y) => Seq(x, Sp, Times, Sp, y);
    private static Formula State(Formula n) => At("DensityState", n);
    private static Formula Channel(Formula a, Formula b) => At("QuantumChannel", a, b);
    private static Formula Finite(string n, Formula body, bool exists = false)
    {
        var instances = Seq(OpenBracket, At("Fintype", Id(n)), CloseBracket, Sp,
            OpenBracket, At("DecidableEq", Id(n)), CloseBracket, Sp, body);
        return exists ? Some(n, Type(), instances) : All(n, Type(), instances);
    }
    private static Formula Value(Formula x, Formula y) => At("value", Id("D"), x, y);
    private static Formula Ref(Formula x) => At("marginalRight", x);
    private static Formula Out(Formula x) => At("referenceState", Id("N"), x);
    private static Formula Pair(Formula body) => All("rho", State(Id("A")), All("sigma", State(Id("A")), body));
    private static Formula DivergenceFormula()
    {
        var laws = Finite("A", Pair(And(Le(D(0), Value(Id("rho"), Id("sigma"))),
            Iff(Eqn(Value(Id("rho"), Id("sigma")), D(0)), Eqn(Id("rho"), Id("sigma"))))));
        var dpi = Finite("A", Finite("B", All("N", Channel(Id("A"), Id("B")), Pair(
            Le(Value(At("mapState", Id("N"), Id("rho")), At("mapState", Id("N"), Id("sigma"))),
                Value(Id("rho"), Id("sigma")))))));
        var family = Finite("A", new Formula.TypeArrow(State(Id("A")),
            new Formula.TypeArrow(State(Id("A")), Real())));
        return Eqn(Op("FiniteDivergence"), Seq(OpenBrace, Typed("D", family), Sp, Mid, Sp,
            And(laws, dpi), CloseBrace));
    }
    private static Formula Ratios(bool conditional)
    {
        var input = Value(Id("rho"), Id("sigma"));
        var output = Value(Out(Id("rho")), Out(Id("sigma")));
        var reference = Value(Ref(Id("rho")), Ref(Id("sigma")));
        var denominator = conditional ? Sub(input, reference) : input;
        var numerator = conditional ? Sub(output, reference) : output;
        var conditions = And(Lt(D(0), denominator), Eqn(Id("x"), new Formula.Fraction(numerator, denominator)));
        if (!conditional) conditions = And(Eqn(Ref(Id("rho")), Ref(Id("sigma"))), conditions);
        var states = Some("rho", State(Product(Id("R"), Id("A"))),
            Some("sigma", State(Product(Id("R"), Id("A"))), conditions));
        var set = Seq(OpenBrace, Typed("x", Real()), Sp, Mid, Sp, Finite("R", states, true), CloseBrace);
        return Finite("A", Finite("B", All("D", Op("FiniteDivergence"),
            All("N", Channel(Id("A"), Id("B")), Eqn(
                At(conditional ? "conditionalRatios" : "completeRatios", Id("D"), Id("N")), set)))));
    }
    private static DocumentBlock.Describe RatioDescribe(bool conditional) => Describe.Lean(
        DescribeId.Create(conditional ? "faithful-conditional-ratios" : "faithful-complete-ratios"),
        DeclarationHandle.Create(Prefix + (conditional ? "conditionalRatios" : "completeRatios")),
        H(conditional ? "Conditional ratios" : "Complete ratios"),
        StatementSource.FromAuthor(Disp(Ratios(conditional))), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text("The set includes every finite quantum reference R and every canonical "
            + "density-state pair satisfying the displayed conditions. Denominators are strictly "
            + "positive real numbers; all divergence values are finite."))), DescribeRole.Definition);
    private static DocumentBlock.Describe CoefficientDescribe(bool conditional)
    {
        var name = conditional ? "conditionalCoefficient" : "completeCoefficient";
        var ratios = conditional ? "conditionalRatios" : "completeRatios";
        var formula = Finite("A", Finite("B", All("D", Op("FiniteDivergence"),
            All("N", Channel(Id("A"), Id("B")), Eqn(At(name, Id("D"), Id("N")),
                At("sSup", At("insert", D(0), At(ratios, Id("D"), Id("N")))))))));
        return Describe.Lean(DescribeId.Create(conditional ? "faithful-conditional-coefficient" : "faithful-complete-coefficient"),
            DeclarationHandle.Create(Prefix + name), H(conditional ? "Conditional coefficient" : "Complete coefficient"),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text("Adjoining zero makes an empty admissible ratio set have coefficient zero. "
                + "The squared trace-distance instance has the boundedness needed for the real supremum."))), DescribeRole.Definition);
    }
    private static Formula ResultFormula()
    {
        var qubit = At("Fin", D(2));
        return Some("D", Op("FiniteDivergence"), Some("N", Channel(qubit, qubit),
            And(Le(At("completeCoefficient", Id("D"), Id("N")), new Formula.Fraction(D(1), D(4))),
                And(Lt(new Formula.Fraction(D(1), D(4)), new Formula.Fraction(D(5), D(1, 2))),
                    Le(new Formula.Fraction(D(5), D(1, 2)), At("conditionalCoefficient", Id("D"), Id("N")))))));
    }
}
