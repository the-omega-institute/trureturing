using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CorrelatedCoherenceMonogamyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/basso2020correlatedcoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A pure state of three qubits has a negative l1 correlated-coherence monogamy difference.",
        H("Correlated coherence need not be monogamous for pure three-qubit states"), Blocks(
            Paragraph(Text(
                "Work in the computational product basis. Fin(n) consists of the indices 0 through n − 1, "
                    + "and a basis index of three qubits is a function from Fin(3) to Fin(2). "
                    + "Qubits 0, 1 and 2 are A, B and C, respectively. Complex absolute values are moduli. "
                    + "The anonymous brackets Fintype n and DecidableEq n supply a finite enumeration "
                    + "and decidable equality for the matrix indices.")),
            Node("l1Coherence", "Coherence in a fixed basis", CoherenceFormula(),
                "The l1 coherence is the sum of the moduli of all off-diagonal matrix entries. "
                    + "Each ordered pair of distinct indices is counted once. "
                    + "The expression is defined for every complex square matrix, without positivity "
                    + "or trace assumptions, and is the l1-norm coherence used in Section II."),
            Node("monogamyGap", "The seven-term monogamy difference", GapFormula(),
                "For a vector ψ and a set S of qubits, the partial trace over Fin(3) outside S "
                    + "of ψ ψ* is its reduced matrix on S. The star on the column vector denotes "
                    + "conjugate transpose; equivalently, the pure matrix has entry ψ(x) times "
                    + "the complex conjugate of ψ(y). The retained basis is the set of functions "
                    + "from S to Fin(2). A trace over the empty set retains the full pure matrix. "
                    + "Write M for monogamyGap. Its four positive terms are the full coherence "
                    + "and the three single-qubit coherences; its three subtracted terms are the "
                    + "two-qubit coherences. This is Eq. (33), the difference between the correlated "
                    + "coherence across A versus BC and the sum of those across AB and AC. "
                    + "The formula itself does not require ψ to have norm one."),
            Node("claim", "The conjecture for three qubits", ClaimFormula(),
                "Section III.A conjectures monogamy for every tripartite pure state. "
                    + "Here it is restricted to three qubits: every complex vector whose squared "
                    + "moduli sum to one has a nonnegative monogamy difference. "
                    + "All reduced matrices use the same computational product basis. "
                    + "The sufficient conditions (22)–(24) are not assumed in this conjecture."),
            Describe.Lean(
                DescribeId.Create("correlated-coherence-monogamy-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A pure three-qubit state with a negative difference"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Named("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take ψ = (−16, 1, 128, −16, −128, −16, 1, −128)/√49922, "
                            + "in the order |000⟩, |001⟩, |010⟩, |011⟩, |100⟩, |101⟩, |110⟩, |111⟩. "
                            + "The first bit is qubit 0. The sum of the squares of the eight integer "
                            + "amplitudes is 49922, so ψ is a unit vector.")),
                    Paragraph(Text(
                        "For the full state and the marginals A, B, C, AB, AC and BC, respectively, "
                            + "the l1 coherences are 138434/49922, 8416/49922, 288/49922, "
                            + "288/49922, 48928/49922, 48928/49922 and 50336/49922. "
                            + "Each reduced entry is the sum, over a common configuration of the "
                            + "discarded qubits, of the two corresponding integer amplitudes multiplied "
                            + "together and divided by 49922. Summing the moduli of its off-diagonal "
                            + "entries gives these seven values.")),
                    Paragraph(Text(
                        "The alternating sum is M(ψ) = −766/49922 = −383/24961, which is negative. "
                            + "Thus a pure three-qubit state contradicts claim and hence the conjecture "
                            + "for all tripartite pure states. This does not contradict Theorem 4: "
                            + "its trade-off hypothesis is not assumed by the conjecture."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("basso-maziero-2020-correlated-coherence-monogamy-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("correlated-coherence-monogamy-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Arrow(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(byte size) => Call("Fin", D(size));
    private static Formula Basis() => Parenthesized(Arrow(Fin(3), Fin(2)));
    private static Formula Vectors() => Parenthesized(Arrow(Basis(), Complexes()));
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, Parenthesized(body));

    private static Formula CoherenceFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), j = F.Id("j");
        Formula offDiagonal = Seq(Typed(j, n), Comma, Sp, NotEqual(i, j));
        Formula sum = SumOver(Typed(i, n), SumOver(offDiagonal,
            new Formula.Absolute(At(Rho, i, j))));
        return All(n, Named("Type"), Instance(Call("Fintype", n), Instance(Call("DecidableEq", n),
            All(Rho, Call("Matrix", n, n, Complexes()), Equal(Call("l1Coherence", Rho), sum)))));
    }

    private static Formula CoherenceOn(params byte[] qubits)
    {
        var indices = new System.Collections.Generic.List<Formula>();
        foreach (var qubit in qubits) indices.Add(D(qubit));
        Formula outside = Seq(Fin(3), Sp, Setminus, Sp, new Formula.SetLiteral([.. indices]));
        Formula pureMatrix = Seq(Psi, Sp, new Formula.Power(Psi, Star));
        Formula trace = At(new Formula.Subscript(Named("Tr"), outside), Parenthesized(pureMatrix));
        return Call("l1Coherence", trace);
    }

    private static Formula GapFormula()
    {
        Formula positive = Add(Add(Add(CoherenceOn(0, 1, 2), CoherenceOn(0)),
            CoherenceOn(1)), CoherenceOn(2));
        Formula negative = Add(Add(CoherenceOn(0, 1), CoherenceOn(0, 2)), CoherenceOn(1, 2));
        return All(Psi, Vectors(), Equal(Call("monogamyGap", Psi), Subtract(positive, negative)));
    }

    private static Formula ClaimFormula()
    {
        Formula total = SumOver(Typed(F.Id("x"), Basis()),
            new Formula.Power(new Formula.Absolute(At(Psi, F.Id("x"))), D(2)));
        return IffOf(Named("claim"), All(Psi, Vectors(),
            Imp(Equal(total, D(1)), LE(D(0), Call("monogamyGap", Psi)))));
    }
}
