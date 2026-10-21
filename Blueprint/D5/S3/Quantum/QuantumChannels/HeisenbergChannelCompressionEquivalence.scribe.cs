using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class HeisenbergChannelCompressionEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/uola2021subspaces");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatibility of a finite POVM family under every isometric compression is equivalent to compatibility under every unital completely positive map.",
        H("Heisenberg Channel Compression Equivalence"),
        Blocks(
            Paragraph(Text(
                "All dimensions and index types are finite. A family M assigns to each setting x "
                    + "a finite outcome-indexed family of complex d by d matrices. Joint "
                    + "measurability means that one parent POVM indexed by all outcome choices "
                    + "has the given marginal at every setting.")),
            Node("family-jointly-measurable", "Joint measurability with a parent POVM",
                FamilyJointlyMeasurableFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "The parent G is indexed by dependent outcome choices a, one outcome for each "
                    + "setting. It is a POVM, and summing G over choices whose x-coordinate is b "
                    + "recovers M x b. This is the finite joint-measurability condition."),
            Node("claim", "Compression and channel compatibility",
                ClaimFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "For 1 at most n at most d, the family is required to be a POVM at every setting. "
                    + "The first side asks for joint measurability after every isometric "
                    + "compression V from dimension n into dimension d. The second asks for joint "
                    + "measurability after every completely positive unital matrix map from d by d "
                    + "matrices to n by n matrices. The two quantified conditions are asserted to "
                    + "be equivalent."),
            Node("result", "Compatibility is unchanged by replacing compressions with channels",
                Disp(F.Id("claim")), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "An isometry V gives the unital completely positive map X ↦ Vᴴ X V, so every "
                    + "channel-compatible family is compatible after every compression. Conversely, "
                    + "a unital completely positive map has a finite Kraus decomposition "
                    + "Φ(X) = sum_r K_rᴴ X K_r with sum_r K_rᴴ K_r = I. Because n is at most d, "
                    + "each Kraus operator factors as K_r = V_r C_r through an isometry V_r from "
                    + "dimension n into dimension d. A parent POVM for each compressed family is "
                    + "then combined as H_a = sum_r C_rᴴ G^(r)_a C_r. Positivity and the Kraus "
                    + "normalization make H a parent POVM, and its x-marginal is exactly "
                    + "Φ(M x b)."))));

    private static DocumentBlock Node(string id, string title, Formula formula,
        DescribeRole role, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("heisenberg-channel-" + id),
            DeclarationHandle.Create(Prefix + (id == "family-jointly-measurable"
                ? "FamilyJointlyMeasurable" : id)), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Matrix(Formula rows, Formula cols) =>
        Call("Matrix", Fin(rows), Fin(cols), Complex());
    private static Formula MatrixMap(Formula d, Formula n) =>
        Call("MatrixMap", Fin(d), Fin(n), Complex());
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula At(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula name, Formula type) =>
        Parenthesized(Seq(name, Sp, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula range) =>
        new Formula.TypeArrow(domain, range);
    private static Formula DepArrow(string name, Formula domain, Formula range) =>
        Parenthesized(Seq(Typed(V(name), domain), Sp, To, Sp, range));
    private static Formula Family(Formula d, Formula index, Formula outcomes) =>
        DepArrow("x", index, DepArrow("b", At(outcomes, V("x")), Matrix(d, d)));
    private static Formula ParentIndex(Formula index, Formula outcomes) =>
        DepArrow("x", index, At(outcomes, V("x")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(Formula value) =>
        Seq(OpenBracket, value, CloseBracket, Sp);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Adj(Formula value) => new Formula.Power(Parenthesized(value), V("H"));
    private static Formula One() => D(1);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V("fun"), Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula FamilyFintype(Formula index, Formula outcomes) =>
        DepArrow("x", index, Call("Fintype", At(outcomes, V("x"))));
    private static Formula SumWith(string name, Formula type, Formula condition, Formula body) =>
        Seq(new Formula.Subscript(Sum,
                Parenthesized(Seq(V(name), Sp, Colon, Sp, type, Sp,
                    F.Text, Grp(V("with")), Sp, condition))), Sp, body);

    private static Formula FamilyJointlyMeasurableFormula()
    {
        var d = V("d");
        var index = V("X");
        var outcomes = V("Omega");
        var x = V("x");
        var b = V("b");
        var a = V("a");
        var m = V("M");
        var g = V("G");
        var family = Family(d, index, outcomes);
        var parentType = Arrow(ParentIndex(index, outcomes), Matrix(d, d));
        var marginal = SumWith("a", ParentIndex(index, outcomes),
            Equal(At(a, x), b), At(g, a));
        var body = Ex("G", parentType,
            And(Call("IsPOVM", g),
                All("x", index, All("b", At(outcomes, x),
                    Equal(marginal, At(At(m, x), b))))));
        return Disp(All("d", Nat(),
            All("X", V("Type"),
                Seq(Instance(Call("Fintype", index)),
                    All("Omega", Arrow(index, V("Type")),
                        Seq(Instance(FamilyFintype(index, outcomes)),
                            All("M", family,
                                Iff(Call("FamilyJointlyMeasurable", m), body))))))));
    }

    private static Formula ClaimFormula()
    {
        var d = V("d");
        var n = V("n");
        var index = V("X");
        var outcomes = V("Omega");
        var x = V("x");
        var b = V("b");
        var m = V("M");
        var v = V("V");
        var phi = V("Phi");
        var family = Family(d, index, outcomes);
        var compressed = Lambda("x", index,
            Lambda("b", At(outcomes, x), Mul(Mul(Adj(v), At(At(m, x), b)), v)));
        var channelImage = Lambda("x", index,
            Lambda("b", At(outcomes, x), At(phi, At(At(m, x), b))));
        var compressionSide = All("V", Matrix(d, n),
            Implies(Equal(Mul(Adj(v), v), One()),
                Call("FamilyJointlyMeasurable", compressed)));
        var channelSide = All("Phi", MatrixMap(d, n),
            Implies(Call("IsCompletelyPositive", phi),
                Implies(Equal(At(phi, One()), One()),
                    Call("FamilyJointlyMeasurable", channelImage))));
        var body = All("d", Nat(), All("n", Nat(),
            Implies(And(LessOrEqual(One(), n), LessOrEqual(n, d)),
                All("X", V("Type"),
                    Seq(Instance(Call("Fintype", index)),
                        All("Omega", Arrow(index, V("Type")),
                            Seq(Instance(FamilyFintype(index, outcomes)),
                                All("M", family,
                                    Implies(All("x", index, Call("IsPOVM", At(m, x))),
                                        Iff(compressionSide, channelSide))))))))));
        return Disp(Iff(V("claim"), body));
    }
}
