using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class HedgingMajorityThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/HedgingMajorityThreshold.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/arunachalam2017quantumhedging");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Certain success in a strict majority of repetitions of the qubit game is equivalent to certain single-game success.",
        H("The strict-majority threshold for quantum hedging"), Blocks(
            Paragraph(Text(
                "A qubit has computational indices Fin(2) = {0, 1}. A word is a function "
                    + "from Fin(n) to Fin(2). Joint indices are ordered pairs of words, with "
                    + "Bob's register first and Alice's retained register second. Real scalars "
                    + "are viewed in C. The real square root is nonnegative and is defined "
                    + "to be zero on negative arguments. A star denotes the conjugate "
                    + "transpose. The symbol I denotes the "
                    + "identity on the indicated register, and kronecker(A, B) denotes A ⊗ B.")),
            Node("shared-amp", "sharedAmp", "The shared one-game amplitudes", SharedAmplitudeFormula(),
                "The function sharedAmp gives the computational amplitudes of u_alpha. "
                    + "Thus u_alpha = alpha |00> + sqrt(1 - alpha²) |11>. "
                    + "The formula defines these amplitudes for every real alpha; the shared "
                    + "vector is normalized when 0 < alpha <= 1, as in the source's game."),
            Node("shared-vec", "sharedVec", "The shared vector in parallel", SharedVectorFormula(),
                "The vector psi is the tensor product of n copies of u_alpha, with the "
                    + "registers regrouped into Bob's word and Alice's retained word. "
                    + "The product is over all i in Fin(n), including the empty product when n = 0."),
            Node("win-vec", "winVec", "The successful one-game amplitudes", WinningVectorFormula(),
                "The function winVec gives the amplitudes of v_theta = cos(theta) |00> "
                    + "+ sin(theta) |11>. This vector is normalized for every real theta. "
                    + "The source takes theta in [0, 2 pi); the same formulas are periodic "
                    + "and are defined here for all real theta."),
            Node("outcome-proj", "outcomeProj", "The two outcome projections", OutcomeFormula(),
                "Write v_theta for the column whose (y, z) entry is winVec(theta, y, z). "
                    + "Outcome 1 is the rank-one projection P(1,theta) = v_theta v_theta*, "
                    + "and outcome 0 is its full orthogonal complement P(0,theta) = I - P(1,theta). "
                    + "These are respectively the winning and losing outcomes."),
            Node("game-tensor", "gameTensor", "The game-by-game tensor product", TensorFormula(),
                "Each M(i) acts on one pair of qubits. The entry formula is the tensor "
                    + "product of these operators, expressed in the order (Bob's word, "
                    + "Alice's word). It applies to arbitrary complex matrices M(i)."),
            Node("win-at-least", "winAtLeast", "At least k successful outcomes", ThresholdFormula(),
                "The projector Pi_k(n,theta) sums the mutually orthogonal outcome-word "
                    + "projections for words a having at least k entries equal to 1. "
                    + "The cardinality counts coordinates, and each summand acts game by game. "
                    + "The definition allows every natural n and k."),
            Node("output", "output", "The output of a joint channel", OutputFormula(),
                "Bob's matrices K(l) act jointly on his entire word, while I acts on "
                    + "Alice's retained word. The sum defines output for every finite family "
                    + "K, without assuming trace preservation. In the channel assertion below, "
                    + "the inline equation sum K(l)* K(l) = I supplies that condition. "
                    + "The vector psi is sharedVec(n,alpha)."),
            Node("claim", "claim", "The strict-majority assertion", ClaimFormula(),
                "The source's strict-majority question is expressed as an equivalence: "
                    + "a joint channel can win at least k games with certainty exactly when "
                    + "alpha² = cos²(theta), the case in which a single game can be won "
                    + "with certainty. The bounds n < 2k and k <= n imply n >= 1. "
                    + "All finite Kraus families are allowed, and theta ranges over all real "
                    + "numbers. The assertion concerns strict majorities; it makes no "
                    + "characterization for k <= n/2."),
            Describe.Lean(
                DescribeId.Create("hedging-majority-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Certain majority success requires certain single-game success"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Put c = cos(theta), s = sin(theta), D = diag(s², -c²), and "
                            + "T = I ⊗ D on one game. Since v_theta* T v_theta = 0, "
                            + "the winning projection satisfies P(1,theta) T P(1,theta) = 0. "
                            + "Two outcome words with more than n/2 ones share a coordinate "
                            + "where both entries are 1. At that coordinate the compressed "
                            + "tensor factor vanishes. Summing over the two outcome words "
                            + "therefore gives Pi_k T^{⊗n} Pi_k = 0 whenever n < 2k.")),
                    Paragraph(Text(
                        "For 0 < alpha <= 1 the retained one-game marginal is "
                            + "R = diag(alpha², 1 - alpha²). A trace-preserving channel on "
                            + "Bob's word leaves Alice's marginal R^{⊗n} unchanged. Hence "
                            + "the output state rho obeys tr(T^{⊗n} rho) = tr(D R)^n "
                            + "= (alpha² s² - (1 - alpha²)c²)^n = (alpha² - c²)^n.")),
                    Paragraph(Text(
                        "The output rho is positive semidefinite with trace one, and "
                            + "Pi_k is an orthogonal projection. Full weight "
                            + "tr(Pi_k rho) = 1 forces rho = Pi_k rho Pi_k. Its support "
                            + "therefore lies in the range of Pi_k. The zero compression "
                            + "and cyclicity of trace give tr(T^{⊗n} rho) = 0. Thus "
                            + "(alpha² - c²)^n = 0, and n >= 1 yields alpha² = c².")),
                    Paragraph(Text(
                        "Conversely, if alpha² = c² and alpha > 0, then alpha = |c| "
                            + "and sqrt(1 - alpha²) = |s|. Let epsilon(t) be 1 for t >= 0 "
                            + "and -1 otherwise. The diagonal unitary with entries "
                            + "epsilon(c), epsilon(s) maps u_alpha to v_theta on Bob's "
                            + "qubit. Its n-fold tensor product is a single Kraus operator "
                            + "and produces v_theta in every game. All n outcomes are "
                            + "therefore 1 with certainty, giving at least k wins for k <= n."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("arunachalam-molina-russo-2013-hedging-majority-threshold"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string declaration, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create("hedging-majority-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Chain(Formula left, Formula middle, Formula right) =>
        Seq(left, Eq, Sp, middle, Eq, Sp, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Adjoint(Formula value) => new Formula.Power(Parenthesized(value), Star);
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Finite(Formula size) => Call("Fin", size);
    private static Formula Qubit() => Finite(D(2));
    private static Formula Word(Formula n) => Parenthesized(new Formula.TypeArrow(Finite(n), Qubit()));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula ProductType(Formula left, Formula right) => Parenthesized(Seq(left, Times, Sp, right));
    private static Formula MatrixType(Formula index) => Call("Matrix", index, index, Complexes());
    private static Formula Family(Formula index, Formula value) => Parenthesized(new Formula.TypeArrow(index, value));
    private static Formula Over(Formula symbol, Formula index, Formula body) =>
        Seq(new Formula.Subscript(symbol, index), Sp, Parenthesized(body));
    private static Formula Lambda(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(variable, type), Sp, Mapsto, Sp, body));
    private static Formula Shared(Formula n) => new Formula.Subscript(Psi, Seq(n, Comma, Alpha));
    private static Formula Winning() => new Formula.Subscript(X("v"), Theta);
    private static Formula Projection(Formula b) => new Formula.Subscript(X("P"), Seq(b, Comma, Theta));

    private static Formula SharedAmplitudeFormula()
    {
        Formula x = X("x"), z = X("z");
        Formula cases = Seq(Begin, Grp(X("cases")),
            Alpha, Amp, Seq(x, Eq, z, Eq, D(0)), RowBreak,
            Seq(Sqrt, Grp(Subtract(D(1), Square(Alpha)))), Amp, Seq(x, Eq, z, Eq, D(1)), RowBreak,
            D(0), Amp, new Formula.Relation(x, FormulaRelationOperator.NotEqual, z),
            End, Grp(X("cases")));
        return All(Alpha, Reals(), All(x, Qubit(), All(z, Qubit(),
            Chain(Call("sharedAmp", Alpha, x, z), At(new Formula.Subscript(X("u"), Alpha), x, z), cases))));
    }

    private static Formula SharedVectorFormula()
    {
        Formula n = X("n"), x = X("x"), z = X("z"), i = X("i");
        return All(n, Naturals(), All(Alpha, Reals(), All(x, Word(n), All(z, Word(n),
            Chain(Call("sharedVec", n, Alpha, Pair(x, z)), At(Shared(n), Pair(x, z)),
                Over(Prod, Typed(i, Finite(n)), Call("sharedAmp", Alpha, At(x, i), At(z, i))))))));
    }

    private static Formula WinningVectorFormula()
    {
        Formula y = X("y"), z = X("z");
        Formula cases = Seq(Begin, Grp(X("cases")),
            Call("cos", Theta), Amp, Seq(y, Eq, z, Eq, D(0)), RowBreak,
            Call("sin", Theta), Amp, Seq(y, Eq, z, Eq, D(1)), RowBreak,
            D(0), Amp, new Formula.Relation(y, FormulaRelationOperator.NotEqual, z),
            End, Grp(X("cases")));
        return All(Theta, Reals(), All(y, Qubit(), All(z, Qubit(),
            Chain(Call("winVec", Theta, y, z), At(Winning(), y, z), cases))));
    }

    private static Formula OutcomeFormula()
    {
        Formula b = X("b");
        Formula cases = Seq(Begin, Grp(X("cases")),
            Mul(Winning(), Adjoint(Winning())), Amp, Equal(b, D(1)), RowBreak,
            Subtract(X("I"), Projection(D(1))), Amp, Equal(b, D(0)),
            End, Grp(X("cases")));
        return All(Theta, Reals(), All(b, Qubit(),
            Chain(Call("outcomeProj", Theta, b), Projection(b), cases)));
    }

    private static Formula TensorFormula()
    {
        Formula n = X("n"), m = X("M"), x = X("x"), z = X("z"), xp = X("xp"), zp = X("zp"), i = X("i");
        Formula entry = At(At(m, i), Pair(At(x, i), At(z, i)), Pair(At(xp, i), At(zp, i)));
        return All(n, Naturals(), All(m, Family(Finite(n), MatrixType(ProductType(Qubit(), Qubit()))),
            All(x, Word(n), All(z, Word(n), All(xp, Word(n), All(zp, Word(n),
                Equal(Call("gameTensor", n, m, Pair(x, z), Pair(xp, zp)),
                    Over(Prod, Typed(i, Finite(n)), entry))))))));
    }

    private static Formula ThresholdFormula()
    {
        Formula n = X("n"), k = X("k"), a = X("a"), i = X("i");
        Formula count = Call("card", Seq(OpenBrace, Typed(i, Finite(n)), Sp, Mid, Sp,
            Equal(At(a, i), D(1)), CloseBrace));
        Formula index = Seq(Typed(a, Word(n)), Comma, Sp, LE(k, count));
        Formula factors = Lambda(i, Finite(n), Call("outcomeProj", Theta, At(a, i)));
        return All(n, Naturals(), All(k, Naturals(), All(Theta, Reals(),
            Chain(Call("winAtLeast", n, k, Theta), At(new Formula.Subscript(Pi, k), n, Theta),
                Over(Sum, index, Call("gameTensor", n, factors))))));
    }

    private static Formula OutputFormula()
    {
        Formula m = X("m"), n = X("n"), k = X("K"), l = X("l");
        Formula identity = Typed(X("I"), MatrixType(Word(n)));
        Formula lifted = Call("kronecker", At(k, l), identity);
        Formula term = Mul(Mul(Mul(lifted, Shared(n)), Adjoint(Shared(n))), Adjoint(lifted));
        return All(m, Naturals(), All(n, Naturals(),
            All(k, Family(Finite(m), MatrixType(Word(n))), All(Alpha, Reals(),
                Equal(Call("output", k, Alpha), Over(Sum, Typed(l, Finite(m)), term))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = X("n"), k = X("k"), m = X("m"), kraus = X("K"), l = X("l");
        Formula completeness = Equal(Over(Sum, Typed(l, Finite(m)), Mul(Adjoint(At(kraus, l)), At(kraus, l))),
            Typed(X("I"), MatrixType(Word(n))));
        Formula certainty = Equal(Call("tr", Mul(Call("winAtLeast", n, k, Theta), Call("output", kraus, Alpha))), D(1));
        Formula channel = Some(m, Naturals(), Some(kraus, Family(Finite(m), MatrixType(Word(n))),
            Logic(completeness, FormulaLogicOperator.And, certainty)));
        Formula equivalence = Logic(channel, FormulaLogicOperator.Iff, Equal(Square(Alpha), Square(Call("cos", Theta))));
        Formula parameters = All(Alpha, Reals(), All(Theta, Reals(),
            Logic(LT(D(0), Alpha), FormulaLogicOperator.Implies,
                Logic(LE(Alpha, D(1)), FormulaLogicOperator.Implies, equivalence))));
        Formula statement = All(n, Naturals(), All(k, Naturals(),
            Logic(LT(n, Mul(D(2), k)), FormulaLogicOperator.Implies,
                Logic(LE(k, n), FormulaLogicOperator.Implies, parameters))));
        return Logic(Named("claim"), FormulaLogicOperator.Iff, statement);
    }
}
