using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FixedHistoryCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/FixedHistoryComposition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive natural composition and a single actual Clifford history are jointly realizable "
            + "exactly when the rational quarter-counts are integral, all eight integer edge counts are "
            + "nonnegative, and their undirected positive support is connected to the initial state 00.",
        H("Fixed Composition in an Actual Clifford History Fiber"),
        Blocks(
            Paragraph(Text("Source is the native FreeMagma Bool: true denotes alpha, false beta. "
                + "The source remains a nonempty ordered binary tree, with its brackets retained. "
                + "Substitution sends alpha to beta and beta to the ordered pair (beta,alpha). "
                + "Composition counts the leaves of each label.")),
            Paragraph(Text("The carrier is the actual real CliffordAlgebra for Q(a,b)=a*a+a*b-b*b. "
                + "A and B are the canonical vector images. E multiplies their images in original leaf order; "
                + "W3(t)=(E(t),E(rho(t)),E(rho(rho(t)))). S=B*A, D=A+B, "
                + "g=(A,B,S), h=(B,S,D), and R00=1, R10=g, R01=h, R11=g*h. "
                + "L(u,v,w)=((-1)^v*S^(2u),(-1)^w*S^(2v),(-1)^u*S^(2w)).")),
            Paragraph(Text("Write phi for the real golden ratio and psi for its conjugate. "
                + "The notation mat(a,b,c,d) lists a two-by-two real matrix in row order.")),
            MatrixEntry("K", "Golden-ratio vector representation", DescribeRole.Definition,
                All("a", RealDomain, All("b", RealDomain,
                    Equal(Call("K", Tuple(V("a"), V("b"))), Call("mat", Num(0),
                        Add(V("a"), Multiply(V("b"), V("phi"))),
                        Add(V("a"), Multiply(V("b"), V("psi"))), Num(0))))),
                "K is real linear and sends the two coordinate vectors to off-diagonal matrices."),
            MatrixEntry("k_square", "Quadratic relation", DescribeRole.Theorem,
                All("x", Seq(RealDomain, Sp, Times, Sp, RealDomain),
                    Equal(Multiply(Call("K", V("x")), Call("K", V("x"))),
                        Call("algebraMap", Call("Q", V("x"))))),
                "The scalar algebra map has target the two-by-two real matrix algebra."),
            MatrixEntry("sep", "Clifford matrix representation", DescribeRole.Definition,
                Equal(V("sep"), Call("CliffordLift", V("Q"), V("K"))),
                "The quadratic relation extends K to a real algebra homomorphism from C."),
            MatrixEntry("sep_a", "Image of the alpha vector", DescribeRole.Theorem,
                Equal(Call("sep", V("A")), Call("mat", Num(0), Num(1), Num(1), Num(0))),
                "The alpha image exchanges the two matrix coordinates."),
            MatrixEntry("sep_b", "Image of the beta vector", DescribeRole.Theorem,
                Equal(Call("sep", V("B")), Call("mat", Num(0), V("phi"), V("psi"), Num(0))),
                "The beta image uses the two conjugate roots in its off-diagonal entries."),
            Describe.Lean(DescribeId.Create("fixed-history-composition-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Complete same-source criterion"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("All u,v,w are integers; p,q are Boolean bits interpreted as 0 or 1. "
                        + "All ac,bc are natural numbers with ac+bc>=1; either coordinate may be zero. "
                        + "Criterion means that the rational numbers X=(ac-p-2w+2u)/4 and "
                        + "Y=(bc-q-2u+2v)/4 have integer witnesses, all eight counts below are nonnegative, "
                        + "and every endpoint of every positive-count edge is connected to 00 in the "
                        + "undirected positive support. Unused ambient vertices impose no connectivity requirement.")),
                    Paragraph(Text("The alpha counts at departures 00,10,01,11 are "
                        + "X+w-u+p, X+w, X, X-u. The beta counts at departures 00,01,10,11 are "
                        + "Y+u+q*(1-p), Y, Y-v+p*q, Y+u-v. Alpha toggles the first bit; beta toggles the second.")),
                    Paragraph(Math(CountsFormula())),
                    Paragraph(Text("In the displayed criterion, Kind=State times the Boolean leaf label, "
                        + "src and label are its two projections, and Path is the finite quiver path type. "
                        + "The label 1 denotes alpha and 0 denotes beta. Symmetrify allows each positive "
                        + "edge in either direction; a zero-length path retains the initial vertex 00. "
                        + "The positive support and its step function are specified by:")),
                    Paragraph(Math(SupportFormula())),
                    Paragraph(Text("The integer witness equations are ac=4X+2w-2u+p and "
                        + "bc=4Y+2u-2v+q, proved equivalent to the rational quotients. "
                        + "A maximum path whose edge counts are bounded by the capacities reaches the "
                        + "prescribed terminal by its residual divergence. Any remaining capacity is balanced. "
                        + "A boundary crossing in the original weak support supplies a visited splice vertex; "
                        + "a nonempty residual closed path would increase the maximum length. "
                        + "Residual connectivity is not assumed.")),
                    Paragraph(Text("The same chronological path supplies the leaf word, all three actual "
                        + "Clifford coordinates and the composition. Necessity identifies parameters by actual "
                        + "Clifford reflection, and sufficiency brackets that same nonempty word into an actual Source. "
                        + "Parallel occurrences are retained by their exact chronological counts. "
                        + "Flow balance alone is insufficient: unit history at composition (4,0) gives two disconnected alpha cycles."))),
                DescribeRole.Theorem))));

    private static DocumentBlock MatrixEntry(string name, string title, DescribeRole role,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create("fixed-history-composition-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula RealDomain => Seq(Mathbb, Grp(V("R")));
    private static Formula V(string name) => F.Id(name);
    private static Formula Bits => new Formula.SetLiteral([Num(0), Num(1)]);
    private static Formula State => Seq(Bits, Sp, Times, Sp, Bits);
    private static Formula Kind => Seq(Paren(State), Sp, Times, Sp, Bits);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Tuple(params Formula[] values)
    {
        var items = new List<Formula> { Open };
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(values[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula LeOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula And(params Formula[] values)
    {
        var result = values[0];
        for (var i = 1; i < values.Length; i++)
            result = new Formula.Logic(result, FormulaLogicOperator.And, values[i]);
        return result;
    }
    private static Formula Counts() => Call("edgeCounts", V("u"), V("v"), V("w"),
        V("X"), V("Y"), V("p"), V("q"));
    private static Formula Edge(int p, int q, int label) =>
        Apply(Counts(), Tuple(Tuple(Num(p), Num(q)), Num(label)));
    private static Formula Reach(Formula vertex) => Call("Nonempty",
        Call("Path", Call("Symmetrify", Call("PositiveSupport", Counts())),
            Tuple(Num(0), Num(0)), vertex));

    private static Formula ResultFormula()
    {
        var t = V("t");
        var e = V("e");
        var lhs = Some("t", V("Source"), And(
            Equal(Apply(new Formula.Subscript(V("W"), Num(3)), t),
                Multiply(Call("L", V("u"), V("v"), V("w")),
                    new Formula.Subscript(V("R"), Tuple(V("p"), V("q"))))),
            Equal(Call("c", t), Tuple(V("ac"), V("bc")))));
        var rhs = Some("X", new Formula.Integers(), Some("Y", new Formula.Integers(), And(
            Equal(V("X"), new Formula.Fraction(
                Add(Subtract(Subtract(V("ac"), V("p")), Multiply(Num(2), V("w"))),
                    Multiply(Num(2), V("u"))), Num(4))),
            Equal(V("Y"), new Formula.Fraction(
                Add(Subtract(Subtract(V("bc"), V("q")), Multiply(Num(2), V("u"))),
                    Multiply(Num(2), V("v"))), Num(4))),
            All("e", Kind, LeOf(Num(0), Apply(Counts(), e))),
            All("e", Kind, Imp(LtOf(Num(0), Apply(Counts(), e)), And(
                Reach(Call("src", e)),
                Reach(Call("step", Call("src", e), Call("label", e)))))))));
        var result = Imp(LeOf(Num(1), Add(V("ac"), V("bc"))), IffOf(lhs, rhs));
        result = All("bc", Seq(Mathbb, Grp(V("N"))), result);
        result = All("ac", Seq(Mathbb, Grp(V("N"))), result);
        result = All("q", Bits, result);
        result = All("p", Bits, result);
        result = All("w", new Formula.Integers(), result);
        result = All("v", new Formula.Integers(), result);
        result = All("u", new Formula.Integers(), result);
        return Disp(result);
    }

    private static Formula Count(string letter, byte p, byte q, int label, Formula expression) =>
        new Formula.RelationChain(FormulaRelationOperator.Equal,
            [new Formula.Subscript(V(letter), D(p, q)), Edge(p, q, label), expression]);
    private static Formula CountsFormula() => Disp(new Formula.Aligned([
        Count("x", 0, 0, 1, Add(Subtract(Add(V("X"), V("w")), V("u")), V("p"))),
        Count("x", 1, 0, 1, Add(V("X"), V("w"))),
        Count("x", 0, 1, 1, V("X")),
        Count("x", 1, 1, 1, Subtract(V("X"), V("u"))),
        Count("y", 0, 0, 0, Add(Add(V("Y"), V("u")), Multiply(V("q"), Subtract(Num(1), V("p"))))),
        Count("y", 0, 1, 0, V("Y")),
        Count("y", 1, 0, 0, Add(Subtract(V("Y"), V("v")), Multiply(V("p"), V("q")))),
        Count("y", 1, 1, 0, Subtract(Add(V("Y"), V("u")), V("v")))]));

    private static Formula SupportFormula()
    {
        var z = V("z");
        var s = V("s");
        var r = V("r");
        var b = V("b");
        var m = V("m");
        return Disp(new Formula.Aligned([
            Equal(V("State"), State), Equal(V("Kind"), Kind),
            All("z", State, All("b", Bits, And(
                Equal(Call("src", Tuple(z, b)), z), Equal(Call("label", Tuple(z, b)), b)))),
            All("r", Bits, All("s", Bits, And(
                Equal(Call("step", Tuple(r, s), Num(1)), Tuple(Subtract(Num(1), r), s)),
                Equal(Call("step", Tuple(r, s), Num(0)), Tuple(r, Subtract(Num(1), s)))))),
            All("m", new Formula.TypeArrow(Kind, new Formula.Integers()),
                All("s", State, All("z", State,
                    IffOf(Call("Nonempty", Call("Hom", Call("PositiveSupport", m), s, z)),
                        Some("b", Bits, And(Equal(Call("step", s, b), z),
                            LtOf(Num(0), Apply(m, Tuple(s, b)))))))))]));
    }
}
