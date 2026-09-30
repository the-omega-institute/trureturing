using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OrthocrossGramHalfIntegerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/debrota2020varieties");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every dimension d and every orthonormal basis of C^d, the Gram matrix G of the orthocross MIC is invertible and every entry of G^(-1) is an integer or a half-integer. This proves the conjecture of J. B. DeBrota, C. A. Fuchs and B. C. Stacey (arXiv:1812.08762), who observed it numerically.",
        H("The inverse Gram matrix of an orthocross MIC is half-integral"),
        Blocks(
            Node("vec", "Basis and cross vectors", VecFormula(),
                "The index set consists of the d basis indices X_j and, for every pair j < k, a real cross index T_jk and an imaginary cross index V_jk, d^2 indices in all. The vectors are e_j, e_j + e_k and e_j + i e_k.",
                "vec", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weight", "Normalising weights", WeightFormula(),
                "The weight is 1 for a basis vector and 1/2 for a cross vector, whose squared norm is 2, so that w(alpha) v_alpha v_alpha^* is a rank-one projector.",
                "weight", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("proj", "The projectors Pi_alpha", ProjFormula(),
                "For a unitary U, the columns U e_j form the chosen orthonormal basis, and Pi_alpha(U) is the projector onto U v_alpha: the paper's Gamma_jj, (1/2)(|j> + |k>)(<j| + <k|) and (1/2)(|j> + i|k>)(<j| - i<k|) for j < k.",
                "proj", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("frame", "The frame operator Omega", FrameFormula(),
                "Omega is the sum of the d^2 projectors.",
                "frame", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mic", "The orthocross MIC elements", MicFormula(),
                "E_alpha = Omega^(-1/2) Pi_alpha Omega^(-1/2), where Omega^(-1/2) is the positive square root of the inverse of the positive definite matrix Omega.",
                "mic", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gram", "The Gram matrix", GramFormula(),
                "The Gram matrix of the MIC, G_alpha beta = tr(E_alpha E_beta).",
                "gram", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "The conjecture of the paper, for every dimension d and every orthonormal basis (every unitary U): G is invertible and 2 (G^(-1))_ab is an integer for all indices a and b of Idx(d), the d^2 indices X_j, T_jk and V_jk.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Half-integrality of the inverse Gram matrix", Disp(F.Id("claim")),
                "Since the square of Omega^(-1/2) is Omega^(-1), G_alpha beta = tr(Pi_alpha Omega^(-1) Pi_beta Omega^(-1)), and a unitary change of basis does not change it, so U = 1 suffices. In the standard basis Omega has d on the diagonal, (1 - i)/2 above it and (1 + i)/2 below it. The matrices D_T = E_jk + E_kj, D_V = i(E_kj - E_jk) and D_X = E_jj - E_jj C - C E_jj, where C is the off-diagonal part of Omega, satisfy tr(D_alpha Pi_beta) = delta_alpha beta; there are d^2 of them and they are linearly independent, so every matrix Y equals the sum over beta of tr(Y Pi_beta) D_beta. It follows that G M = 1 for M_beta gamma = tr(D_beta Omega D_gamma Omega), so G is invertible and G^(-1) = M. The matrices (1 - i) Omega and (1 - i) D_alpha have Gaussian-integer entries, and 4 = (1 + i) i (1 - i)^3, so every entry of 4 Z with Z = Omega D_gamma Omega is (1 + i) times a Gaussian integer a + b i. Z is Hermitian, so M_T gamma = Z_kj + Z_jk, M_V gamma = i Z_jk - i Z_kj and M_X gamma = Z_jj minus the sum over q of C_jq Z_qj + C_qj Z_jq are read off from these entries, and in each case 2M is an integer: a - b, -(a + b), and a sum of the integers a or -b with 2 Z_jj.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("debrota-2020-orthocross-gram-inverse-half-integer"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("orthocross-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Half() => Seq(Frac, Grp(D(1)), Grp(D(2)));
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, body);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Basis(Formula j) => new Formula.Subscript(F.Id("e"), j);
    private static Formula X(Formula j) => new Formula.Subscript(F.Id("X"), j);
    private static Formula T(Formula j, Formula k) => new Formula.Subscript(F.Id("T"), Seq(j, k));
    private static Formula V(Formula j, Formula k) => new Formula.Subscript(F.Id("V"), Seq(j, k));

    private static Formula VecFormula()
    {
        Formula j = F.Id("j"), k = F.Id("k");
        Formula vec = F.Id("vec");
        return Disp(Seq(
            Equal(Call(vec, X(j)), Basis(j)), Comma, Qquad,
            Equal(Call(vec, T(j, k)), Add(Basis(j), Basis(k))), Comma, Qquad,
            Equal(Call(vec, V(j, k)), Add(Basis(j), Mul(F.Id("i"), Basis(k))))));
    }

    private static Formula WeightFormula()
    {
        Formula j = F.Id("j"), k = F.Id("k");
        Formula w = F.Id("weight");
        return Disp(Seq(
            Equal(Call(w, X(j)), D(1)), Comma, Qquad,
            Call(w, T(j, k)), Sp, Eq, Sp, Call(w, V(j, k)), Sp, Eq, Sp, Half()));
    }

    private static Formula ProjFormula()
    {
        Formula u = F.Id("U"), alpha = Alpha;
        Formula image = Parenthesized(Seq(u, Sp, Call(F.Id("vec"), alpha)));
        return Disp(Equal(Call(F.Id("proj"), u, alpha),
            Mul(Call(F.Id("weight"), alpha), Seq(image, Sp, image, Caret, Grp(Star)))));
    }

    private static Formula FrameFormula()
    {
        Formula u = F.Id("U"), alpha = Alpha;
        return Disp(Equal(Call(F.Id("frame"), u), SumOver(alpha, Call(F.Id("proj"), u, alpha))));
    }

    private static Formula MicFormula()
    {
        Formula u = F.Id("U"), alpha = Alpha;
        Formula root = Seq(Call(F.Id("frame"), u), Caret, Grp(Minus, Half()));
        return Disp(Equal(Call(F.Id("mic"), u, alpha),
            Seq(root, Sp, Call(F.Id("proj"), u, alpha), Sp, root)));
    }

    private static Formula GramFormula()
    {
        Formula u = F.Id("U"), alpha = Alpha, beta = Beta;
        return Disp(Equal(Call(F.Id("gram"), u, alpha, beta),
            Call(F.Id("tr"), Seq(Call(F.Id("mic"), u, alpha), Sp, Call(F.Id("mic"), u, beta)))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), u = F.Id("U"), z = F.Id("z");
        Formula gram = Call(F.Id("gram"), u);
        Formula unit = Call(F.Id("IsUnit"), Call(F.Id("det"), gram));
        Formula entry = Seq(Parenthesized(Seq(gram, Caret, Grp(Minus, D(1)))),
            Parenthesized(Seq(F.Id("a"), Comma, Sp, F.Id("b"))));
        Formula half = Some("z", Ints(), Equal(Mul(D(2), entry), z));
        Formula entries = All("a", Call(F.Id("Idx"), d), All("b", Call(F.Id("Idx"), d), half));
        Formula body = All("d", Nats(),
            All("U", Call(F.Id("UnitaryGroup"), d), And(unit, entries)));
        return Disp(Iff(F.Id("claim"), body));
    }
}
