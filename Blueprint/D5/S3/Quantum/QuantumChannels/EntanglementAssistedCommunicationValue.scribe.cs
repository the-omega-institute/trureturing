using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class EntanglementAssistedCommunicationValueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/EntanglementAssistedCommunicationValue.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/chitambargeorgedoolittlejunge2023communication");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared entanglement increases communication value by at most the output dimension.",
        H("Entanglement-assisted communication value and the output dimension"),
        Blocks(
            Paragraph(Text(
                "All matrix spaces are over ℂ, with Fin(d) the standard coordinate set of size d. "
                    + "MatrixMap(U,V,ℂ) denotes complex linear maps from square U matrices to square V matrices. "
                    + "The identity in a matrix equation is the identity matrix. The real part of a trace "
                    + "makes the protocol expressions real even for linear maps that are not channels. "
                    + "For channels the traces in these expressions are already real.")),
            Node("is-channel", "Completely positive trace-preserving maps", "IsChannel", ChannelFormula(),
                "A channel is completely positive and preserves the trace of every complex input matrix. "
                    + "No restriction to density matrices is imposed on the trace-preservation identity."),
            Node("classical-cv", "Classical communication value", "classicalCV", ClassicalFormula(),
                "For n ≥ 1 and any real array P with m outputs and n inputs, the value is the sum "
                    + "over outputs of the largest entry over inputs. The proof h supplies n ≥ 1, "
                    + "so each maximum is over a nonempty finite set. The definition also permits m = 0 "
                    + "and does not require P to be stochastic. For a classical channel it is Eq. (Cv) "
                    + "of the source, the unnormalized optimal guessing probability."),
            Node("comm-values", "Values of unassisted protocols", "commValues", UnassistedValuesFormula(),
                "A value belongs to commValues(N) precisely when some positive input and output alphabet "
                    + "sizes n and m, density matrices ρ(x), and a POVM M(y) induce the real array "
                    + "P(y|x) = Re tr(M(y) N(ρ(x))) with that classical communication value. "
                    + "The density matrices are positive semidefinite with trace one; the POVM elements "
                    + "are positive semidefinite and sum to the identity. This is the protocol "
                    + "optimization in Definition 1, with both finite alphabet sizes allowed to vary."),
            Node("comm-value", "Unassisted communication value", "commValue", SupremumFormula(false),
                "The real supremum sSup of the set of unassisted protocol values is commValue(N), "
                    + "written cv(N). For a channel this is the communication value of Definition 1, "
                    + "including the supremum over both finite alphabet sizes. The definition itself "
                    + "is given for every complex linear map and every natural input and output dimension."),
            Node("ea-comm-values", "Values of entanglement-assisted protocols", "eaCommValues", AssistedValuesFormula(),
                "The shared density matrix φ acts on dimensions c and r. For each input x, "
                    + "a channel E(x) maps the c-dimensional sender system into the a-dimensional "
                    + "channel input. The receiver measures a POVM on the channel output together "
                    + "with the r-dimensional shared system. The symbol kron denotes the tensor "
                    + "product of linear maps, and id is the identity map on matrices of the indicated "
                    + "coordinate type. The induced array is P(y|x) = Re tr(M(y) ((N∘E(x))⊗id)(φ)). "
                    + "Its classical communication value is the protocol value. The natural dimensions "
                    + "c and r are unrestricted, and n and m are positive. These are the protocols "
                    + "of Eq. (Ea-cv); no fixed bound on shared entanglement is imposed."),
            Node("ea-comm-value", "Entanglement-assisted communication value", "eaCommValue", SupremumFormula(true),
                "The real supremum sSup of all assisted protocol values is eaCommValue(N), "
                    + "written cv*(N). The set includes all finite shared dimensions, all shared "
                    + "density matrices, all finite positive alphabet sizes, local encoding channels "
                    + "and joint decoding POVMs. This restates the assisted communication value "
                    + "defined after Eq. (Ea-cv). As with commValue, the definition is also available "
                    + "for arbitrary complex linear maps and natural dimensions."),
            Node("claim", "The output-dimension comparison", "claim", ClaimFormula(),
                "For every pair of positive finite dimensions a and b and every channel from "
                    + "a by a matrices to b by b matrices, cv*(N) ≤ b cv(N). This is the conjecture "
                    + "stated in the source, with b the output dimension."),
            Describe.Lean(
                DescribeId.Create("cgdj-communication-value-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Shared entanglement gives at most an output-dimension advantage"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix a channel N and write b for its positive output dimension and J for "
                            + "its Choi matrix. Use tensor order A⊗B in this explanation; exchanging "
                            + "the factors gives the B⊗A coordinate convention of the matrix formulas. "
                            + "For every assisted protocol value v there is a positive semidefinite "
                            + "operator Ω with tr_A Ω = I_B and v = Re tr(JΩ). Choose an input "
                            + "maximizing each output probability and contract the corresponding "
                            + "encoded shared state with the receiver's POVM element. Complete "
                            + "positivity gives positivity of the resulting sum. Trace preservation "
                            + "of each encoding gives the same receiver marginal for every input; "
                            + "the POVM identity then gives tr_A Ω = I_B.")),
                    Paragraph(Text(
                        "Depolarizing the B factor gives Ω' = (Ω + tr_B Ω ⊗ I_B)/(b+1). "
                            + "This operator has a finite product decomposition Ω' = ∑ₖ Pₖ⊗Qₖ "
                            + "with Pₖ and Qₖ positive semidefinite. To see finiteness directly, "
                            + "write Ω as a finite sum of rank-one positive operators |ψ⟩⟨ψ|. "
                            + "Choose independent coordinates zⱼ equal to zero with probability 1/2 "
                            + "and to each of √2, −√2, i√2, −i√2 with probability 1/8. "
                            + "For u_z = (I_A⊗⟨z|)ψ, the finite average of "
                            + "|u_z⟩⟨u_z|⊗|z⟩⟨z| is |ψ⟩⟨ψ| + tr_B(|ψ⟩⟨ψ|)⊗I_B. "
                            + "Summing and dividing by b+1 gives the asserted decomposition. Moreover "
                            + "tr_A Ω' = I_B. Since tr_B J = I_A and tr Ω = b, its objective is "
                            + "Re tr(JΩ') = (v+b)/(b+1).")),
                    Paragraph(Text(
                        "For each product term with tₖ = tr Pₖ > 0, use the state "
                            + "ρₖ = Pₖᵀ/tₖ and the POVM element Mₖ = tₖQₖ; terms with zero "
                            + "trace contribute zero and may use any density matrix. The marginal "
                            + "identity makes these POVM elements sum to I_B. The resulting "
                            + "unassisted protocol has diagonal guessing score (v+b)/(b+1). "
                            + "Maximizing over inputs for each output gives a classical communication "
                            + "value at least this score, hence (v+b)/(b+1) ≤ cv(N).")),
                    Paragraph(Text(
                        "Every output state is a density matrix, so each output's largest "
                            + "probability is at most tr M(y). Summing the POVM elements gives "
                            + "cv(N) ≤ b. Therefore v ≤ (b+1)cv(N)−b ≤ b cv(N). "
                            + "Taking the supremum over all assisted protocols proves claim."))),
                DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose) => Describe.Lean(
            DescribeId.Create("cgdj-communication-value-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula dimension) => Call("Fin", dimension);
    private static Formula MatrixOn(Formula coordinates) => Call("Matrix", coordinates, coordinates, Complexes());
    private static Formula Matrices(Formula dimension) => MatrixOn(FinOf(dimension));
    private static Formula Maps(Formula input, Formula output) =>
        Call("MatrixMap", FinOf(input), FinOf(output), Complexes());
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Times, right));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Lam(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body)));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Logic(Formula left, FormulaLogicOperator operation, Formula right) =>
        new Formula.Logic(Parenthesized(left), operation, Parenthesized(right));
    private static Formula Conjunction(params Formula[] terms)
    {
        var body = terms[^1];
        for (var i = terms.Length - 2; i >= 0; i--)
            body = Logic(terms[i], FormulaLogicOperator.And, body);
        return body;
    }
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(variable, type)), Sp, Parenthesized(body));
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Trace(Formula matrix) => Call("tr", matrix);
    private static Formula RealTrace(Formula matrix) => At(Re, Trace(matrix));
    private static Formula Positive(Formula matrix) => Call("PosSemidef", matrix);
    private static Formula Density(Formula matrix) => Conjunction(Positive(matrix), Equal(Trace(matrix), D(1)));
    private static Formula OverMaps(Formula body)
    {
        var a = F.Id("a"); var b = F.Id("b"); var channel = F.Id("N");
        return All(a, Naturals(), All(b, Naturals(), All(channel, Maps(a, b), body)));
    }

    private static Formula ChannelFormula()
    {
        var a = F.Id("a"); var channel = F.Id("N"); var matrix = F.Id("X");
        return OverMaps(Logic(Call("IsChannel", channel), FormulaLogicOperator.Iff,
            Conjunction(Call("IsCompletelyPositive", channel),
                All(matrix, Matrices(a), Equal(Trace(At(channel, matrix)), Trace(matrix))))));
    }

    private static Formula ClassicalFormula()
    {
        var n = F.Id("n"); var m = F.Id("m"); var h = F.Id("h"); var p = F.Id("P");
        var x = F.Id("x"); var y = F.Id("y");
        var maximum = Seq(new Formula.Subscript(Max, Typed(x, FinOf(n))), Sp, Parenthesized(At(p, y, x)));
        return All(n, Naturals(), All(m, Naturals(), All(h, LE(D(1), n),
            All(p, Arrow(FinOf(m), Arrow(FinOf(n), Reals())),
                Equal(Call("classicalCV", h, p), SumOver(y, FinOf(m), maximum))))));
    }

    private static Formula UnassistedValuesFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var channel = F.Id("N"); var v = F.Id("v");
        var n = F.Id("n"); var m = F.Id("m"); var h = F.Id("h"); var measurement = F.Id("M");
        var x = F.Id("x"); var y = F.Id("y");
        var probabilities = Lam(y, FinOf(m), Lam(x, FinOf(n),
            RealTrace(Mul(At(measurement, y), At(channel, At(Rho, x))))));
        var conditions = Conjunction(All(x, FinOf(n), Density(At(Rho, x))),
            All(y, FinOf(m), Positive(At(measurement, y))),
            Equal(SumOver(y, FinOf(m), At(measurement, y)), D(1)),
            Equal(v, Call("classicalCV", h, probabilities)));
        var protocol = Ex(Rho, Arrow(FinOf(n), Matrices(a)),
            Ex(measurement, Arrow(FinOf(m), Matrices(b)), conditions));
        protocol = Ex(h, LE(D(1), n), Conjunction(LE(D(1), m), protocol));
        protocol = Ex(n, Naturals(), Ex(m, Naturals(), protocol));
        return OverMaps(All(v, Reals(), Logic(Member(v, Call("commValues", channel)),
            FormulaLogicOperator.Iff, protocol)));
    }

    private static Formula AssistedValuesFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var channel = F.Id("N"); var v = F.Id("v");
        var c = F.Id("c"); var r = F.Id("r"); var n = F.Id("n"); var m = F.Id("m");
        var h = F.Id("h"); var encoding = F.Id("E"); var measurement = F.Id("M");
        var x = F.Id("x"); var y = F.Id("y");
        var composed = Parenthesized(Seq(channel, Sp, Circ, Sp, At(encoding, x)));
        var output = At(Call("kron", composed, Call("id", FinOf(r), Complexes())), Phi);
        var probabilities = Lam(y, FinOf(m), Lam(x, FinOf(n), RealTrace(Mul(At(measurement, y), output))));
        var conditions = Conjunction(Density(Phi),
            All(x, FinOf(n), Call("IsChannel", At(encoding, x))),
            All(y, FinOf(m), Positive(At(measurement, y))),
            Equal(SumOver(y, FinOf(m), At(measurement, y)), D(1)),
            Equal(v, Call("classicalCV", h, probabilities)));
        var protocol = Ex(Phi, MatrixOn(Product(FinOf(c), FinOf(r))),
            Ex(encoding, Arrow(FinOf(n), Maps(c, a)),
                Ex(measurement, Arrow(FinOf(m), MatrixOn(Product(FinOf(b), FinOf(r)))), conditions)));
        protocol = Ex(h, LE(D(1), n), Conjunction(LE(D(1), m), protocol));
        protocol = Ex(c, Naturals(), Ex(r, Naturals(), Ex(n, Naturals(), Ex(m, Naturals(), protocol))));
        return OverMaps(All(v, Reals(), Logic(Member(v, Call("eaCommValues", channel)),
            FormulaLogicOperator.Iff, protocol)));
    }

    private static Formula SupremumFormula(bool assisted)
    {
        var channel = F.Id("N");
        return OverMaps(Equal(Call(assisted ? "eaCommValue" : "commValue", channel),
            Call("sSup", Call(assisted ? "eaCommValues" : "commValues", channel))));
    }

    private static Formula ClaimFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var channel = F.Id("N");
        var bound = LE(Call("eaCommValue", channel), Mul(Typed(b, Reals()), Call("commValue", channel)));
        return Logic(Named("claim"), FormulaLogicOperator.Iff,
            All(a, Naturals(), All(b, Naturals(),
                Logic(LE(D(1), a), FormulaLogicOperator.Implies,
                    Logic(LE(D(1), b), FormulaLogicOperator.Implies,
                        All(channel, Maps(a, b), Logic(Call("IsChannel", channel),
                            FormulaLogicOperator.Implies, bound)))))));
    }
}
