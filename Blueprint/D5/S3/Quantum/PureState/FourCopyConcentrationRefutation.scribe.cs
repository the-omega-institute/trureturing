using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class FourCopyConcentrationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PureState/FourCopyConcentrationRefutation.";
    private const string Singlets = "D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.rationalSinglets";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/ortheyphilipkondrastreltsov2026optimality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed local singlet-sector measurement on four copies exceeds the conjectured pointwise concentration bound.",
        H("Direct four-copy concentration exceeds the proposed bound"), Blocks(
            Paragraph(Text(
                "All computational-basis indices are zero-based. The coefficient matrix of a two-qubit pure state and the unnormalized Bell coefficient array have the following meanings:")),
            new DocumentBlock.DisplayFormula(Disp(Equal(Qubit(), Matrix(Fin(2), Fin(2))))),
            new DocumentBlock.DisplayFormula(Disp(Equal(
                Call("D5.S3.Quantum.QubitWitnesses.bellCoefficients"), MatrixArray(D(1), D(0), D(0), D(1))))),
            Paragraph(Text(
                "The four coefficients c1, c2, c3, c4 in Eq. (1) are C(0,0), C(0,1), C(1,0), C(1,1), respectively. "
                    + "The superscript H denotes Matrix.conjTranspose, and a star between matrices denotes matrix multiplication. "
                    + "The double bars denote the complex norm; all sums below are finite.")),
            Node("Q", "The four-qubit local index", QFormula(),
                "The two product factors group positions (1,2) and (3,4) of one party's four qubits.",
                AssessedProvenance.FromRepo(Source)),
            Node("normalized", "Normalized pure-state coefficients", NormalizedFormula(),
                "Equation (1) requires the sum of the squared complex amplitudes to be one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("amp4", "The four-copy input amplitudes", AmpFormula(),
                "For the four copies of the state in Eq. (1), a contains Alice's four bits and b contains Bob's. Each copy contributes one coefficient of C.",
                AssessedProvenance.FromLiterature(Source)),
            Node("output", "The product success operator on four copies", OutputFormula(),
                "The success branch acts by the single Kraus operator K_A tensor K_B. Its pure output has these coefficients. Bob's factor is transposed in the coefficient-matrix action, with no complex conjugation.",
                AssessedProvenance.FromLiterature(Source)),
            Node("universal", "Universal conclusive pure-state concentration", UniversalFormula(),
                "Definition 1 for pure states says that the unnormalized output lies in the span of the Bell vector for every normalized input, including a zero output. This is exactly the vanishing of its two off-diagonal coefficients and equality of its two diagonal coefficients.",
                AssessedProvenance.FromLiterature(Source)),
            Node("success", "The success probability", SuccessFormula(),
                "For the normalized pure inputs of Eq. (1), the squared norm of the success output is the trace of the success branch, as in Theorem 3.",
                AssessedProvenance.FromLiterature(Source)),
            Node("B", "The proposed four-copy bound", BoundFormula(),
                "This is literally the right-hand side of Eq. (8): the first two terms are norms of products of fourth powers, and the last term is four times the real part of the product with the two conjugated coefficients.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The direct four-copy concentration conjecture", ClaimFormula(),
                "Section VIII conjectures that direct four-copy protocols cannot surpass B, the right-hand side of Eq. (8). "
                    + "Here the success branch has the single Kraus operator K_A tensor K_B, with each local operator a contraction. "
                    + "For either party, the positive square root R of the identity minus K_A^H K_A (or K_B^H K_B) gives failure operators |0><q|R, one for each local basis index q. "
                    + "Their adjoint products sum to R squared, so each party's instrument completes locally. "
                    + "The parties measure locally, communicate their success flags, and keep the output when both succeed. This is one-round LOCC processing the four copies directly. "
                    + "The predicate universal is Definition 1 for pure states. Thus every pair of operators quantified here gives a protocol in the conjectured class.",
                AssessedProvenance.FromLiterature(Source)),
            Node("u", "Singlets on consecutive pairs", UFormula(),
                "The coordinate permutation turns the two-singlet coefficient function into the product of singlets on positions (1,2) and (3,4): (|0101> - |0110> - |1001> + |1010>)/2.",
                AssessedProvenance.FromRepo(Source)),
            Node("v", "The orthogonal singlet-sector vector", VFormula(),
                "The second pairing is the product of singlets on positions (1,3) and (2,4). Twice that vector minus u, divided by the complex cast of the real square root of three, is a unit vector orthogonal to u.",
                AssessedProvenance.FromRepo(Source)),
            Node("K", "The local singlet-sector success operator", KFormula(),
                "The rows are u and v. Both vectors have real entries, so these rows are also their bras. Their orthonormality makes K a coisometry and hence a local contraction.",
                AssessedProvenance.FromRepo(Source)),
            Node("C0", "A maximally entangled input with zero proposed bound", CFormula(),
                "These rational coefficients form a normalized state with determinant one half.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("four-copy-concentration-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The direct four-copy bound is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Name("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The two singlet-pairing vectors are (|0101> - |0110> - |1001> + |1010>)/2 and "
                        + "(|0011> - |0110> - |1001> + |1100>)/2. The first is u; twice the second minus the first, divided by sqrt 3, is v. "
                        + "For every coefficient matrix C, output K K C is (det C) squared times the Bell array D5.S3.Quantum.QubitWitnesses.bellCoefficients, "
                        + "whose entries are one on the diagonal and zero off the diagonal. The fixed local contractions therefore give a universal conclusive protocol with success probability 2|det C| to the fourth power. "
                        + "At C0 this probability is 1/8, whereas B C0 is zero, contradicting the asserted inequality."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("orthey-philip-kondra-streltsov-2026-four-copy-concentration-bound"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("four-copy-concentration-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula QFormula() => Equal(Name("Q"),
        Product(Product(Fin(2), Fin(2)), Product(Fin(2), Fin(2))));

    private static Formula NormalizedFormula() => All("C", Qubit(),
        Iff(Call("normalized", V("C")), Equal(
            SumOver("i", Fin(2), SumOver("j", Fin(2), Pow(new Formula.Norm(At(V("C"), V("i"), V("j"))), 2))), D(1))));

    private static Formula AmpFormula()
    {
        Formula a = V("a"), b = V("b");
        Formula Entry(byte pair, byte bit) => At(V("C"), Field(Field(a, pair), bit), Field(Field(b, pair), bit));
        return All("C", Qubit(), All("a", Name("Q"), All("b", Name("Q"),
            Equal(Typed(Call("amp4", V("C"), a, b), Complexes()),
                Mul(Mul(Mul(Entry(1, 1), Entry(1, 2)), Entry(2, 1)), Entry(2, 2))))));
    }

    private static Formula OutputFormula() => Operators(All("C", Qubit(),
        All("i", Fin(2), All("j", Fin(2), Equal(
            Typed(Call("output", V("KA"), V("KB"), V("C"), V("i"), V("j")), Complexes()),
            SumOver("a", Name("Q"), SumOver("b", Name("Q"),
                Mul(Mul(At(V("KA"), V("i"), V("a")), At(V("KB"), V("j"), V("b"))),
                    Call("amp4", V("C"), V("a"), V("b"))))))))));

    private static Formula UniversalFormula() => Operators(Iff(Call("universal", V("KA"), V("KB")),
        All("C", Qubit(), Imp(Call("normalized", V("C")),
            And(Equal(Output(0, 1), D(0)), And(Equal(Output(1, 0), D(0)), Equal(Output(0, 0), Output(1, 1))))))));

    private static Formula SuccessFormula() => Operators(All("C", Qubit(),
        Equal(Typed(Call("success", V("KA"), V("KB"), V("C")), Reals()),
            SumOver("i", Fin(2), SumOver("j", Fin(2),
                Pow(new Formula.Norm(Call("output", V("KA"), V("KB"), V("C"), V("i"), V("j"))), 2))))));

    private static Formula BoundFormula()
    {
        Formula Entry(byte i, byte j) => At(V("C"), D(i), D(j));
        Formula cross = Mul(Mul(Mul(Pow(Entry(0, 0), 2), Pow(Entry(1, 1), 2)),
            Pow(Call("conj", Entry(0, 1)), 2)), Pow(Call("conj", Entry(1, 0)), 2));
        return All("C", Qubit(), Equal(Typed(Call("B", V("C")), Reals()),
            Sub(Add(Mul(D(2), new Formula.Norm(Mul(Pow(Entry(0, 1), 4), Pow(Entry(1, 0), 4)))),
                Mul(D(2), new Formula.Norm(Mul(Pow(Entry(0, 0), 4), Pow(Entry(1, 1), 4))))),
                Mul(D(4), Seq(Parenthesized(cross), Dot, Name("re"))))));
    }

    private static Formula ClaimFormula() => Iff(Name("claim"), Operators(
        Imp(Contractive(V("KA")), Imp(Contractive(V("KB")), Imp(Call("universal", V("KA"), V("KB")),
            All("C", Qubit(), Imp(Call("normalized", V("C")),
                LE(Call("success", V("KA"), V("KB"), V("C")), Call("B", V("C"))))))))));

    private static Formula UFormula()
    {
        Formula q = V("q");
        Formula permuted = Pair(Pair(Field(Field(q, 1), 1), Field(Field(q, 2), 1)),
            Pair(Field(Field(q, 1), 2), Field(Field(q, 2), 2)));
        return All("q", Name("Q"), Equal(Typed(Call("u", q), Complexes()), Call(Singlets, permuted)));
    }

    private static Formula VFormula() => All("q", Name("Q"),
        Equal(Typed(Call("v", V("q")), Complexes()),
            Mul(new Formula.Power(Typed(Call("Real.sqrt", D(3)), Complexes()), new Formula.Negate(D(1))),
                Sub(Mul(D(2), Call(Singlets, V("q"))), Call("u", V("q"))))));

    private static Formula KFormula() => All("i", Fin(2), All("q", Name("Q"),
        Equal(Typed(At(Name("K"), V("i"), V("q")), Complexes()),
            Call("ite", Equal(V("i"), D(0)), Call("u", V("q")), Call("v", V("q"))))));

    private static Formula CFormula() => Equal(Typed(Name("C0"), Qubit()),
        MatrixArray(Typed(Half(), Complexes()), Half(), new Formula.Negate(Half()), Half()));

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name)
    {
        var parts = name.Split('.');
        return Seq(Operatorname, Grp(Seq([.. parts.SelectMany((part, index) => index == 0
            ? new[] { V(part) } : new[] { Dot, V(part) })])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(byte size) => Call("Fin", D(size));
    private static Formula Qubit() => Name("D5.S3.Quantum.FiniteDimensional.QubitMatrix");
    private static Formula Matrix(Formula rows, Formula columns) => Call("Matrix", rows, columns, Complexes());
    private static Formula Product(Formula left, Formula right) => Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Field(Formula value, byte index) => Seq(value, Dot, D(index));
    private static Formula Half() => new Formula.Fraction(D(1), D(2));
    private static Formula Pow(Formula value, byte exponent) => new Formula.Power(Parenthesized(value), D(exponent));
    private static Formula Adj(Formula value) => new Formula.Power(Parenthesized(value), V("H"));
    private static Formula Contractive(Formula value) => Call("Matrix.PosSemidef", Sub(D(1), Mul(Adj(value), value)));
    private static Formula Output(byte i, byte j) => Call("output", V("KA"), V("KB"), V("C"), D(i), D(j));
    private static Formula Operators(Formula body) => All("KA", Matrix(Fin(2), Name("Q")),
        All("KB", Matrix(Fin(2), Name("Q")), body));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula MatrixArray(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(V("bmatrix")), a, Amp, b, RowBreak, c, Amp, d, End, Grp(V("bmatrix")));
    private static Formula Mul(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Star, Sp, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
