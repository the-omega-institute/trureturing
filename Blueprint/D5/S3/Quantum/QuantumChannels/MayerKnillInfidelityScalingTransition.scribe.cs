using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class MayerKnillInfidelityScalingTransitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingTransition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/mayerknill2018unitary");
    private static AssessedProvenance Literature => AssessedProvenance.FromLiterature(Source);
    private static AssessedProvenance Derived => AssessedProvenance.FromRepo(Source);
    private static DocumentBlock Node(string id, string name, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    private static DocumentBlock InputNode(string id, string name, Formula formula, string encoding) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), Literature, Blocks(InputQuotation(encoding)), DescribeRole.Definition);
    private static DocumentBlock OwnerNode(string id, string owner, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(owner), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);
    private static DocumentBlock InputQuotation(string encoding)
    {
        Formula process = Seq(Mathcal, Grp(V("E")));
        Formula feasible = App(Seq(Mathcal, Grp(V("C"))), Varepsilon);
        Formula minimum = App(new Formula.Subscript(Min, Membership(process, feasible)), App(V("F"), process));
        return Paragraph(
            Text("Mayer and Knill, arXiv:1805.04491v1, p. 2, §III: “Let {|ψₖ⟩}ₖ₌₁ᴺ be an indexed family of pure states in ℋ, fix ε=(ε₁,…,"),
            Math(new Formula.Subscript(Varepsilon, V("N"))),
            Text(") with εₖ≥0, and let 𝒞(ε) be the convex set of CPTP maps ℰ such that for all k, ⟨ψₖ|ℰ(ψ̂ₖ)|ψₖ⟩ ≥ 1−εₖ. We refer to {|ψₖ⟩} as the set of input states. We wish to find "),
            Math(App(new Formula.Subscript(V("F"), Seq(Mathrm, Grp(V("min")))), Varepsilon)),
            Text("="), Math(minimum),
            Text(". Note that the minimum is achieved by compactness of the feasible set.” " + encoding));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar line-preserving matrices distinguish linear from square-root process infidelity for fixed connected spanning pure-input families.",
        H("Mayer–Knill infidelity transition"), Blocks(
            InputNode("unit-inputs", "unitInputFamily", FamilyDefinition("unitInputFamily", UnitBody()),
                "The coordinate vectors use Fin N and Fin d; the pure states are normalized."),
            Node("spanning-inputs", "spanInputFamily", FamilyDefinition("spanInputFamily", SpanBody()),
                "The complex span of the input vectors is the entire coordinate space. This is the spanning hypothesis in the source's unitary-identification criterion.", Literature),
            Node("connected-inputs", "nonorthogonalityConnected", FamilyDefinition("nonorthogonalityConnected", ConnectedBody()),
                "Nonzero complex overlaps generate a single equivalence class. Paths may have any finite length, and indexed repeated inputs are allowed.", Literature),
            Node("survival-fidelity", "survivalFidelity", SurvivalDefinition(),
                "The source's survival event is ⟨ψ∣E(ψ̂)∣ψ⟩. Here ψ̂ is the existing rankOneDensity, and the real part extracts the real-valued event probability for a CPTP map.", Literature),
            OwnerNode("choi", "D5/S3/Quantum/Foundation/FiniteKrausRepresentation.choi_matrix", "Choi matrix",
                ChoiDefinition(),
                "MatrixMap.choi_matrix is the matrix whose coordinates are obtained by applying Φ to Matrix.single j.2 k.2 1 and reading the j.1, k.1 entry.",
                DescribeRole.Definition, Literature),
            Node("worst-infidelity", "f", FDefinition(),
                "The worst process infidelity is one minus the infimum of the normalized Choi overlap over admissible channels.", Literature),
            InputNode("admissible-channels", "admissibleAt", AdmissibleDefinition(),
                "The error vector is constant, with every coordinate equal to epsilon."),
            Node("obstruction-space", "obstructionSpace", ObstructionDefinition(),
                "For unit input families, a matrix belongs to the obstruction space exactly when it preserves each tested line. The orthogonal residual after applying that matrix vanishes at every input.", Derived),
            Node("scalar-obstruction", "scalarObstruction", FamilyDefinition("scalarObstruction", ScalarBody()),
                "Every line-preserving matrix is a scalar identity. Unit inputs ensure that every scalar identity does preserve all the tested lines.", Derived),
            Node("linear-scaling", "LinearScaling", FamilyDefinition("LinearScaling", ScalingBody(false)),
                "There are positive lower and upper constants and a positive radius on which the infidelity lies between the corresponding multiples of epsilon. Constants are chosen separately for each fixed input family.", Derived),
            Node("sqrt-scaling", "SqrtScaling", FamilyDefinition("SqrtScaling", ScalingBody(true)),
                "The same two-sided local estimate holds with Real.sqrt epsilon. The quantified errors are strictly positive and smaller than the radius.", Derived),
            Node("transition-claim", "claim", Eq(V("claim"), ClaimBody()),
                "Mayer and Knill, arXiv:1805.04491v1, p. 4: “First, note that the lowest order term in the lower bound is of order √ε. This scaling behavior matches our empirical observations from numerically solving the SDP given by Eq. (5). However, we find that for many sets of input states containing more than d states, the O(√ε) term vanishes and the process infidelity becomes linear in ε for small error. Examples include the basis states plus the totally rotated state, as well as the symmetric POVM states defined in the next section. The transition from sub-linear to linear scaling is not explained by the proof of Thm. 2 and thus remains an open question.” The proposition quantifies over all finite unit spanning input families in dimensions at least two whose nonorthogonality graph is connected. It characterizes the two possible rates by the line-preserving obstruction space.", Derived),
            Node("transition-result", "result", ClaimBody(),
                "The traceless Kraus squared norms sum to d times process infidelity, and the tested orthogonal residual squared norms sum to each input error. Scalar obstruction makes the finite-dimensional detection map injective, giving the linear upper estimate; an identity/reset mixture supplies a positive linear lower estimate. A traceless nonscalar obstruction admits a positive square-root Kraus completion and produces a square-root lower estimate. Stinespring overlap defects propagate along the finite connected graph, and spanning evaluation controls the whole matrix, giving the matching square-root upper estimate. The two local rates cannot both hold. Constants may depend on the spanning condition and the nonzero overlaps; no uniform estimate for degenerating families is asserted.", Derived, DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] binders, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders], body);
    private static Formula Ex(Formula.BoundVariable[] binders, Formula body) => new Formula.BindMany(FormulaQuantifier.Exists, [.. binders], body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => Parenthesized(Seq(Parenthesized(a), Sp, Leftrightarrow, Sp, Parenthesized(b)));
    private static Formula NotOf(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Component(string value, byte field) => Seq(V(value), Dot, Num(field));
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(V("fun")), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Vec => Arrow(Fin(V("d")), C);
    private static Formula Mat => Call("Matrix", Fin(V("d")), Fin(V("d")), C);
    private static Formula Map => Call("MatrixMap", Fin(V("d")), Fin(V("d")), C);
    private static Formula Psi(Formula k) => App(V("psi"), k);
    private static Formula StarOf(Formula x) => Call("star", x);
    private static Formula DotOf(Formula x, Formula y) => Call("dotProduct", x, y);
    private static Formula MulVec(Formula a, Formula v) => App(Q("Matrix", "mulVec"), a, v);
    private static Formula Density(Formula v) => App(Q("PureStateHandshake", "rankOneDensity"), v);
    private static Formula Membership(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Smul(Formula a, Formula b) => App(Q("HSMul", "hSMul"), a, b);
    private static Formula FamilyDefinition(string name, Formula body) =>
        All([B("d", N), B("N", N), B("psi", Arrow(Fin(V("N")), Vec))], Eq(Call(name, V("psi")), body));
    private static Formula UnitBody() => All([B("k", Fin(V("N")))], Eq(DotOf(StarOf(Psi(V("k"))), Psi(V("k"))), Num(1)));
    private static Formula SpanBody() => Eq(App(Q("Submodule", "span"), C, App(Q("Set", "range"), V("psi"))), Q("Top", "top"));
    private static Formula ConnectedBody()
    {
        Formula relation = Seq(Operatorname, Grp(V("fun")), Sp, V("a"), Sp, V("b"), Sp, Mapsto, Sp,
            NotOf(Eq(DotOf(StarOf(Psi(V("a"))), Psi(V("b"))), Num(0))));
        return All([B("i", Fin(V("N"))), B("j", Fin(V("N")))],
            App(Q("Relation", "EqvGen"), relation, V("i"), V("j")));
    }
    private static Formula SurvivalDefinition() => All([B("d", N), B("Phi", Map), B("psi", Vec)],
        Eq(Call("survivalFidelity", V("Phi"), V("psi")), App(Q("Complex", "re"),
            DotOf(StarOf(V("psi")), MulVec(App(V("Phi"), Density(V("psi"))), V("psi"))))));
    private static Formula ChoiDefinition() =>
        All([B("d", N), B("Phi", Map)], ChoiBody(V("Phi")));
    private static Formula ChoiBody(Formula phi)
    {
        Formula indices = Seq(Fin(V("d")), Sp, Times, Sp, Fin(V("d")));
        Formula unit = App(Q("Matrix", "single"), Component("j", 2), Component("k", 2), Num(1));
        return Fun("j", indices, Fun("k", indices,
            App(App(phi, unit), Component("j", 1), Component("k", 1))));
    }
    private static Formula ProcessValue()
    {
        Formula indices = Seq(Fin(V("d")), Sp, Times, Sp, Fin(V("d")));
        Formula diagonal = Fun("ij", indices,
            Call("ite", Eq(Component("ij", 1), Component("ij", 2)),
                App(Q("Complex", "ofReal"), new Formula.Power(App(Q("Real", "sqrt"), V("d")),
                    new Formula.Negate(Num(1)))), Num(0)));
        Formula overlap = DotOf(StarOf(diagonal), MulVec(ChoiBody(V("Phi")), diagonal));
        return new Formula.Fraction(App(Q("Complex", "re"), overlap), V("d"));
    }
    private static Formula FDefinition()
    {
        Formula set = Seq(OpenBrace, Sp, V("x"), Sp, Colon, Sp, R, Sp, Mid, Sp,
            Ex([B("Phi", Map)], And(Call("admissibleAt", V("psi"), V("epsilon"), V("Phi")),
                Eq(V("x"), ProcessValue()))), Sp, CloseBrace);
        return All([B("d", N), B("N", N), B("psi", Arrow(Fin(V("N")), Vec)), B("epsilon", R)],
            Eq(Call("f", V("psi"), V("epsilon")), Sub(Num(1), Call("sInf", set))));
    }
    private static Formula AdmissibleDefinition() => All([B("d", N), B("N", N),
        B("psi", Arrow(Fin(V("N")), Vec)), B("epsilon", R), B("Phi", Map)],
        Eq(Call("admissibleAt", V("psi"), V("epsilon"), V("Phi")),
            And(App(Q("ElementaryChannelDivisibility", "CPTP"), V("Phi")),
                All([B("k", Fin(V("N")))], Le(Sub(Num(1), V("epsilon")), Call("survivalFidelity", V("Phi"), Psi(V("k"))))))));
    private static Formula ObstructionDefinition()
    {
        Formula residual = MulVec(Sub(Num(1), Density(Psi(V("k")))), MulVec(V("A"), Psi(V("k"))));
        Formula set = Seq(OpenBrace, Sp, V("A"), Sp, Colon, Sp, Mat, Sp, Mid, Sp, All([B("k", Fin(V("N")))], Eq(residual, Num(0))), Sp, CloseBrace);
        return FamilyDefinition("obstructionSpace", set);
    }
    private static Formula ScalarBody() => All([B("A", Mat)], Imp(Membership(V("A"), Call("obstructionSpace", V("psi"))),
        Ex([B("z", C)], Eq(V("A"), Smul(V("z"), Seq(Num(1), Sp, Colon, Sp, Mat))))));
    private static Formula ScalingBody(bool squareRoot)
    {
        Formula error = squareRoot ? App(Q("Real", "sqrt"), V("epsilon")) : V("epsilon");
        return Ex([B("c", R), B("C", R), B("delta", R)],
            And(Lt(Num(0), V("c")), And(Lt(Num(0), V("C")), And(Lt(Num(0), V("delta")),
                All([B("epsilon", R)], Imp(Lt(Num(0), V("epsilon")), Imp(Lt(V("epsilon"), V("delta")),
                    And(Le(Mul(V("c"), error), Call("f", V("psi"), V("epsilon"))),
                        Le(Call("f", V("psi"), V("epsilon")), Mul(V("C"), error))))))))));
    }
    private static Formula ClaimBody() => All([B("d", N), B("N", N), B("psi", Arrow(Fin(V("N")), Vec))],
        Imp(Le(Num(2), V("d")), Imp(Call("unitInputFamily", V("psi")), Imp(Call("spanInputFamily", V("psi")),
            Imp(Call("nonorthogonalityConnected", V("psi")),
                And(IffOf(Call("scalarObstruction", V("psi")), Call("LinearScaling", V("psi"))),
                    IffOf(NotOf(Call("scalarObstruction", V("psi"))), Call("SqrtScaling", V("psi")))))))));
}
