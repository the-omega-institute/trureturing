using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class UnitalBlockOverlapRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/girlingcirstoiujennings2022unitarity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two completely positive trace-preserving qutrit maps have unital-block overlap minus four thirds, contradicting the proposed lower bound of minus one.",
        H("Unital-block overlap can be less than minus one"),
        Blocks(
            Node("basis", "Liouville operator bases", BasisFormula(),
                "We choose an orthonormal basis of operators X₀, X₁, …, X_{d²−1} for B(H_A) with X₀ = 1/√d and with respect to the Hilbert Schmidt inner product ⟨X_μ, X_ν⟩ := tr X_μ†X_ν = δ_{μ,ν}. In particular, this means that X₁, …, X_{d²−1} are all traceless operators. (Section II.C, arXiv v3 PDF p. 5.) The dimension d is natural, the operator indices are Fin(d^2), and h0 proves that index zero exists. The first condition is complex Hilbert-Schmidt orthonormality; the second fixes the normalized identity. The square root takes the real cast of d and is then cast to the complex numbers.",
                "IsLiouvilleBasis", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("block", "Liouville entries", BlockFormula(),
                "Section II.C, arXiv v3 PDF p. 5, gives the Liouville entries as the trace of X_i conjugate-transposed times the channel image of X_j. The function is defined on all indices; its restriction to positive i and j is the unital block. MatrixMap is the complex-linear matrix-map type. Matrix.conjTranspose and Matrix.trace are the matrix adjoint and trace.",
                "unitalBlock", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("overlap", "Overlap of the unital blocks", OverlapFormula(),
                "The overlap in Appendix C.5 is the Hilbert-Schmidt inner product of the two unital blocks. The double sum includes only indices with nonzero Fin.val. Each summand is the complex conjugate of the first Liouville entry multiplied by the second entry; star denotes complex conjugation. No division of natural numbers occurs.",
                "overlap", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed universal lower bound", ClaimFormula(),
                "However, we conjecture a stronger result that for any two quantum channels E₁, E₂ that ⟨T₁, T₂⟩ ≥ −1. (Appendix C.5, after Lemma C.3, arXiv v3 PDF p. 21.) The paper also states: Since it is not essential to our work we leave it as an open problem. Here Phi and Psi range over all complex-linear maps on d by d matrices, and CoPRelativeQuantumnessRefutation.IsCPTP requires complete positivity and trace preservation on all matrices. The basis satisfies IsLiouvilleBasis. The comparison uses the real part of the complex overlap, agreeing with the source inner product for Hermitian operator bases.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Two qutrit coarse-graining channels", Disp(new Formula.Not(F.Id("claim"))),
                "Use the Kraus families (E00, E01, E12) and (E10, E11, E02), with Eij = Matrix.single i j 1. The first channel sends a matrix A to diagonal(A00+A11, A22, 0); the second sends it to diagonal(A22, A00+A11, 0). Each Kraus representation proves complete positivity, and FiniteKrausChannel.finite_kraus_quantum_channel supplies trace preservation because each sum of adjoint Kraus products is the identity. Choose the nine Hermitian operators I/sqrt(3), diagonal(1,-1,0)/sqrt(2), diagonal(1,1,-2)/sqrt(6), and the symmetric and imaginary antisymmetric matrix units for the three off-diagonal pairs, each divided by sqrt(2). Their eighty-one inner products give an orthonormal basis. On the eight traceless operators both channels have just one nonzero Liouville entry, at row one and column two, with values 4/(sqrt(2) sqrt(6)) and its negative. Their overlap is therefore minus four thirds, strictly below minus one. Neither channel is unital, and dimension three lies outside the qubit case of Lemma C.4.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("girling-cirstoiu-jennings-2022-unital-block-overlap"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("gcj-unital-overlap-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Square(Formula d) => new Formula.Power(d, D(2));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula MatrixType(Formula d) => Call("Matrix", Call("Fin", d), Call("Fin", d), Complexes());
    private static Formula MapType(Formula d) => Call("MatrixMap", Call("Fin", d), Call("Fin", d), Complexes());
    private static Formula BasisType(Formula d) => Seq(Call("Fin", Square(d)), To, MatrixType(d));
    private static Formula Trace(Formula a) => App(Qualified("Matrix", "trace"), a);
    private static Formula Adjoint(Formula a) => App(Qualified("Matrix", "conjTranspose"), a);
    private static Formula Entry(Formula phi, Formula x, Formula i, Formula j) => Call("unitalBlock", phi, x, i, j);
    private static Formula CPTP(Formula phi) => App(Qualified("CoPRelativeQuantumnessRefutation", "IsCPTP"), phi);

    private static Formula BasisFormula()
    {
        Formula d = F.Id("d"), x = F.Id("X"), h = F.Id("h0"), mu = F.Id("mu"), nu = F.Id("nu");
        Formula ortho = All("mu", Call("Fin", Square(d)), All("nu", Call("Fin", Square(d)),
            Equal(Trace(Multiply(Adjoint(App(x, mu)), App(x, nu))),
                Call("ite", Equal(mu, nu), D(1), D(0)))));
        Formula cast = Parenthesized(Seq(d, Colon, Reals()));
        Formula root = Parenthesized(Seq(App(Qualified("Real", "sqrt"), cast), Colon, Complexes()));
        Formula identity = Equal(App(x, App(Qualified("Fin", "mk"), D(0), h)),
            Seq(new Formula.Power(root, new Formula.Negate(D(1))), Sp, Cdot, Sp, D(1)));
        return Disp(All("d", Naturals(), All("X", BasisType(d), All("h0", Less(D(0), Square(d)),
            Iff(Call("IsLiouvilleBasis", x, h), And(ortho, identity))))));
    }

    private static Formula BlockFormula()
    {
        Formula d = F.Id("d"), phi = F.Id("Phi"), x = F.Id("X"), i = F.Id("i"), j = F.Id("j");
        Formula entry = Equal(Entry(phi, x, i, j), Trace(Multiply(Adjoint(App(x, i)), App(phi, App(x, j)))));
        return Disp(All("d", Naturals(), All("Phi", MapType(d), All("X", BasisType(d),
            All("i", Call("Fin", Square(d)), All("j", Call("Fin", Square(d)), entry))))));
    }

    private static Formula OverlapFormula()
    {
        Formula d = F.Id("d"), phi = F.Id("Phi"), psi = F.Id("Psi"), x = F.Id("X"), i = F.Id("i"), j = F.Id("j");
        Formula condition = And(NotEqual(Call("val", i), D(0)), NotEqual(Call("val", j), D(0)));
        Formula term = Call("ite", condition,
            Multiply(Call("star", Entry(phi, x, i, j)), Entry(psi, x, i, j)), D(0));
        Formula sum = SumOver("i", Call("Fin", Square(d)), SumOver("j", Call("Fin", Square(d)), term));
        return Disp(All("d", Naturals(), All("Phi", MapType(d), All("Psi", MapType(d), All("X", BasisType(d),
            Equal(Call("overlap", phi, psi, x), sum))))));
    }

    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, Sp, type)), Sp, Parenthesized(body));

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), h = F.Id("h0"), phi = F.Id("Phi"), psi = F.Id("Psi"), x = F.Id("X");
        Formula lower = new Formula.Relation(new Formula.Negate(D(1)), FormulaRelationOperator.LessThanOrEqual,
            Seq(Parenthesized(Call("overlap", phi, psi, x)), Dot, Named("re")));
        Formula body = Implies(CPTP(phi), Implies(CPTP(psi), Implies(Call("IsLiouvilleBasis", x, h), lower)));
        return Disp(Iff(F.Id("claim"), All("d", Naturals(), All("h0", Less(D(0), Square(d)),
            All("Phi", MapType(d), All("Psi", MapType(d), All("X", BasisType(d), body)))))));
    }
}
