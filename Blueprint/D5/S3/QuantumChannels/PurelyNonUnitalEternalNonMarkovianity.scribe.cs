using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class PurelyNonUnitalEternalNonMarkovianityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/utagi2024eternal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rotating replacement state gives a completely positive trace-preserving qubit dynamics whose unital part is divisible, while its generator fails conditional complete positivity at every positive time.",
        H("Purely non-unital eternal non-Markovianity"), Blocks(
            Entry("unital-part", "unitalPart", "The translation-free part", UnitalFormula(),
                "Eqs. (9)–(11), pages 3–4, decompose the Bloch action into M(t)r + τ(t). On arbitrary complex qubit matrices, subtracting half the trace times Phi(t)(1) − 1 removes the translation. Matrix.trace is the complex trace, 1 is the identity matrix, and the dot is complex scalar multiplication.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("purely-nonunital", "PurelyNonUnital", "Non-unitality with a divisible unital part", PurelyFormula(),
                "Definition 1, page 4: \"When non-Markovianity originates solely from the non-unital part, i.e., from τ(t), then we call it non-unital non-Markovianity and such a channel will be called purely non-unital non-Markovian channel.\" Phi(t) fails to preserve 1 for every t > 0. For every 0 ≤ s ≤ t, a completely positive trace-preserving map V carries unitalPart(Phi,s,X) to unitalPart(Phi,t,X) for every matrix X. MatrixMap denotes PhyslibLeaf.MatrixMap, and IsCPTP is the existing completely positive trace-preserving predicate.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("generator", "IsGeneratorAt", "The entrywise time-local generator", GeneratorFormula(),
                "The time parameter is real. For each complex matrix X and both Fin 2 indices, HasDerivAt states that the derivative of the entry Phi(u)(X)(i,j) at t equals L(Phi(t)(X))(i,j). No derivative of the input matrix is taken.",
                AssessedProvenance.FromRepo(Source)),
            Entry("conditional-cp", "CondCP", "Conditional complete positivity", CondFormula(),
                "The sum of the diagonal coordinates of v vanishes, so v is orthogonal to the identity vector. The quadratic form uses star v, dotProduct and Matrix.mulVec, followed by Complex.re. The displayed lambda is the output-first coordinate definition of MatrixMap.choi_matrix L: its row p and column q entry is L(Matrix.single p.2 q.2 1)(p.1,q.1). CondCP requires nonnegativity for every such vector.",
                AssessedProvenance.FromRepo(Source)),
            Entry("eternal", "EternallyNonMarkovian", "A negative generator direction at every positive time", EternalFormula(),
                "At every t > 0 there is a time-local generator L with a negative direction in its conditional Choi form. This is the weak eternal non-Markovianity criterion of a negative canonical rate at every positive time; it imposes no lower bound on the magnitude as t tends to infinity.",
                AssessedProvenance.FromRepo(Source)),
            Entry("depolarizing-cptp", "dep_cptp", "Completely positive trace-preserving qubit depolarization", DepCptpFormula(),
                "For every real eta in [0,1], depolarized LinearMap.id (1 − eta) is completely positive and trace preserving. It sends X to eta X + (1 − eta) Matrix.trace(X) I/2. Its Pauli weights are eta + (1 − eta)/4 and three copies of (1 − eta)/4, which are nonnegative and sum to one.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem),
            Entry("conjecture", "claim", "The qubit specialization of the conjecture", ClaimFormula(),
                "Section IV, page 11: \"These diverse examples examined in the Section suggest that a purely non-unital channel (i.e., one lacking any unital component) is impossible. Although we have only studied the qubit case, we conjecture that it is true for non-unital channels in arbitrary finite dimensions.\" Section V, page 11: \"However, we conjecture that for a non-unital channel with no such unital component (in the above sense) to be ENM, is impossible.\" The universal claim here concerns qubits, starts at the identity map, and requires IsCPTP at every nonnegative time. A qubit counterexample refutes the assertion for arbitrary finite dimensions.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A rotating replacement counterexample", Disp(Seq(Neg, Sp, V("claim"))),
                "For real t put D = 1 + t² and P = [[1,t],[t,t²]]/D. The family Phi(t)(X) = (X + t² Matrix.trace(X) P)/D has four Kraus matrices I/D, tI/D, (t/D)[[1,0],[t,0]] and (t/D)[[0,1],[0,t]]. It starts at the identity and is non-unital at every positive time. Its unital part is the isotropic depolarization (X + t² Matrix.trace(X) I/2)/D. For 0 ≤ s ≤ t the intermediate depolarizing parameter is (1+s²)/(1+t²), in [0,1]. Its four Pauli weights are η + (1 − η)/4 and three copies of (1 − η)/4, so it is completely positive and trace preserving. The inverse of Phi(t) sends Y to DY − t² Matrix.trace(Y) P. Composing the derivative with this inverse gives L(Y) = −(2t/D)Y + Matrix.trace(Y) B, where B = [[2t,t²(t²+3)],[t²(t²+3),2t³(t²+2)]]/D³. In the order (0,0),(0,1),(1,0),(1,1), the vector [−2t(t²+3),−t²(t²+3)²,4,2t(t²+3)] has diagonal-coordinate sum zero and conditional Choi quadratic form −2t³(1+t²)(t²+4), strictly negative for t > 0. The replacement direction rotates while the contraction remains a divisible isotropic depolarization.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("utagi-banerjee-srikanth-2024-purely-nonunital-eternal-nonmarkovianity"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula UnitalFormula()
    {
        Formula phi = V("Phi"), t = V("t"), x = V("X");
        return Disp(All("Phi", Dynamics(), All("t", Real(), All("X", Mat(),
            Equal(Call("unitalPart", phi, t, x), Sub(App(phi, t, x),
                Scalar(new Formula.Fraction(App(Qualified("Matrix", "trace"), x), D(2)),
                    Sub(App(phi, t, D(1)), D(1)))))))));
    }

    private static Formula PurelyFormula()
    {
        Formula phi = V("Phi"), s = V("s"), t = V("t"), x = V("X"), map = V("V");
        Formula nonunital = All("t", Real(), Imp(Less(D(0), t),
            new Formula.Relation(App(phi, t, D(1)), FormulaRelationOperator.NotEqual, D(1))));
        Formula divisible = All("s", Real(), All("t", Real(), Imp(Le(D(0), s), Imp(Le(s, t),
            ExistsIn("V", Map(), And(Call("IsCPTP", map), All("X", Mat(),
                Equal(App(map, Call("unitalPart", phi, s, x)), Call("unitalPart", phi, t, x)))))))));
        return Disp(All("Phi", Dynamics(), Equal(Call("PurelyNonUnital", phi), And(nonunital, divisible))));
    }

    private static Formula GeneratorFormula()
    {
        Formula phi = V("Phi"), t = V("t"), l = V("L"), x = V("X"), i = V("i"), j = V("j");
        Formula derivative = Call("HasDerivAt", Lambda("u", Real(), App(phi, V("u"), x, i, j)),
            App(l, App(phi, t, x), i, j), t);
        return Disp(All("Phi", Dynamics(), All("t", Real(), All("L", Map(),
            Equal(Call("IsGeneratorAt", phi, t, l), All("X", Mat(),
                All("i", Fin(), All("j", Fin(), derivative))))))));
    }

    private static Formula CondFormula()
    {
        Formula l = V("L"), v = V("v"), p = V("p"), q = V("q");
        Formula choi = Lambda("p", Pair(), Lambda("q", Pair(),
            App(l, App(Qualified("Matrix", "single"), Projection(p, 2), Projection(q, 2), D(1)),
                Projection(p, 1), Projection(q, 1))));
        Formula trace = Seq(Sum, Underscore, Grp(V("i"), Colon, Sp, Fin()), Sp,
            App(v, Tuple(V("i"), V("i"))));
        Formula form = App(Qualified("Complex", "re"), Call("dotProduct", Call("star", v),
            App(Qualified("Matrix", "mulVec"), choi, v)));
        return Disp(All("L", Map(), Equal(Call("CondCP", l),
            All("v", Arrow(Pair(), Complex()), Imp(Equal(trace, D(0)), Le(D(0), form))))));
    }

    private static Formula EternalFormula() => Disp(All("Phi", Dynamics(),
        Equal(Call("EternallyNonMarkovian", V("Phi")), All("t", Real(), Imp(Less(D(0), V("t")),
            ExistsIn("L", Map(), And(Call("IsGeneratorAt", V("Phi"), V("t"), V("L")),
                Seq(Neg, Sp, Call("CondCP", V("L"))))))))));

    private static Formula ClaimFormula() => Disp(Equal(V("claim"), All("Phi", Dynamics(),
        Imp(All("t", Real(), Imp(Le(D(0), V("t")), Call("IsCPTP", App(V("Phi"), V("t"))))),
            Imp(All("X", Mat(), Equal(App(V("Phi"), D(0), V("X")), V("X"))),
                Imp(Call("PurelyNonUnital", V("Phi")), Seq(Neg, Sp, Call("EternallyNonMarkovian", V("Phi")))))))));

    private static Formula DepCptpFormula() => Disp(All("eta", Real(),
        Imp(Le(D(0), V("eta")), Imp(Le(V("eta"), D(1)),
            Call("IsCPTP", Call("depolarized",
                Parenthesized(Seq(Qualified("LinearMap", "id"), Colon, Sp, Map())), Sub(D(1), V("eta"))))))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin() => Call("Fin", D(2));
    private static Formula Mat() => Call("Matrix", Fin(), Fin(), Complex());
    private static Formula Map() => Call("MatrixMap", Fin(), Fin(), Complex());
    private static Formula Dynamics() => Arrow(Real(), Map());
    private static Formula Pair() => Seq(Fin(), Sp, Times, Sp, Fin());
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Projection(Formula value, byte digit) => Seq(value, Dot, D(digit));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Tuple(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Sub(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Minus, Sp, Parenthesized(b));
    private static Formula Scalar(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(V("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
