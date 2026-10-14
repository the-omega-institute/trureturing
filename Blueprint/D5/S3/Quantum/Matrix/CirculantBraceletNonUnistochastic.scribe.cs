using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CirculantBraceletNonUnistochasticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/rajchelkorzekwapuchalazyczkowski2021birkhoff");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A circulant bracelet matrix of order twelve is not unistochastic.",
        H("Circulant bracelet sufficiency fails at order twelve"), Blocks(
            Paragraph(Text("Matrices have zero-based indices in Fin d. Subtraction in Fin d is modulo d. "
                + "A sum indexed by Fin d includes every index exactly once. The real indexed supremum iSup "
                + "is the maximum for the nonempty finite index sets in the question.")),
            Entry("circulant", "IsCirculant", "Circulant matrices", CirculantFormula(),
                "Definition 5, page 4: \"The set of d × d circulant matrices C_d consists of all matrices B whose entries satisfy [30] B_{j+l,k} = B_{j,k−l}, (7) where the addition and subtraction is modulo d.\" Matrix.circulant uses v(i−j); replacing the first row by its reversal gives the same set of matrices.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("unistochastic", "IsUnistochastic", "Unistochastic matrices", UnistochasticFormula(),
                "Definition 4, page 3: \"The set of d × d unistochastic matrices U_d consists of all bistochastic matrices B whose entries satisfy B_jk = |U_jk|² for some unitary matrix U.\" RHLinalg.normSqMatrix U has entry ‖U i j‖². Membership of U in Matrix.unitaryGroup implies bistochasticity of this squared-norm matrix.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("bracelet", "IsBracelet", "Column and row bracelet conditions", BraceletFormula(),
                "Definition 7, page 4: \"The set of d × d bracelet matrices L_d consists of these bistochastic matrices B whose entries satisfy:\" equations (9a) and (9b), \"which are called column and row bracelet conditions.\" The displayed inequalities are those two equations. The source counts d(d−1) conditions: distinct column pairs and distinct row pairs. Both orders of each pair give the same inequality.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("sufficiency-question", "claim", "The higher-dimensional sufficiency question", ClaimFormula(),
                "Section V, page 13: \"Another observation that holds for d ≤ 4, and should be further investigated for d > 4, is whether the bracelet condition is sufficient for unistochasticity if we restrict the analysis to the set of circulant matrices.\" The formula quantifies over every natural d > 4 and every real d × d matrix. IsBracelet includes bistochasticity; IsUnistochastic allows an arbitrary complex unitary matrix, without requiring it to be circulant.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A twelve-dimensional refutation", Disp(Seq(Neg, Sp, V("claim"))),
                "Let S={0,1,3,4,6,9} modulo twelve, and put B(i,j)=1/6 when j−i belongs to S and zero otherwise. Every row and column contains six nonzero entries. Every distinct row or column pair overlaps in at least two positions, so all bracelet inequalities hold. "
                + "If B were the squared-norm matrix of a unitary U, its zero entries would be exactly those of U. Put T={0,3,6,9}. Row 11 overlaps every row in T exactly in columns 0 and 3; row 2 overlaps them exactly in columns 3 and 6. Row orthogonality therefore gives common nonzero complex ratios λ and μ, with U(r,3)=λ U(r,0) and U(r,6)=μ U(r,3) for every r in T. Columns 0 and 6 overlap exactly on T, so their inner product is μλ·4/6, which is nonzero. This contradicts column orthogonality. "
                + "Theorem 17, page 9, establishes the equality of circulant bracelet and circulant unistochastic matrices at dimension four. The counterexample concerns higher dimensions and does not decide the sufficiency question at dimensions five through eleven.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("rajchel-korzekwa-puchala-zyczkowski-2021-circulant-bracelet-sufficiency"),
                ResolutionKind.Refuted) : null);

    private static Formula CirculantFormula()
    {
        Formula d = V("d"), b = V("B"), v = V("v");
        return Disp(All("d", Nat(), All("B", Matrix(d, Real()),
            Equal(Call("IsCirculant", b), ExistsIn("v", Arrow(Fin(d), Real()),
                Equal(b, App(Qualified("Matrix", "circulant"), v)))))));
    }

    private static Formula UnistochasticFormula()
    {
        Formula d = V("d"), b = V("B"), u = V("U");
        return Disp(All("d", Nat(), All("B", Matrix(d, Real()),
            Equal(Call("IsUnistochastic", b), ExistsIn("U", Matrix(d, Complex()),
                And(Member(u, App(Qualified("Matrix", "unitaryGroup"), Fin(d), Complex())),
                    Equal(b, App(Qualified("RHLinalg", "normSqMatrix"), u))))))));
    }

    private static Formula BraceletFormula()
    {
        Formula d = V("d"), b = V("B"), j = V("j"), k = V("k"), l = V("l");
        Formula columns = All("k", Fin(d), All("l", Fin(d), Imp(NotEqual(k, l),
            BraceletInequality("j", d, Length(b, j, k, j, l)))));
        Formula rows = All("j", Fin(d), All("k", Fin(d), Imp(NotEqual(j, k),
            BraceletInequality("l", d, Length(b, j, l, k, l)))));
        return Disp(All("d", Nat(), All("B", Matrix(d, Real()),
            Equal(Call("IsBracelet", b), And(Member(b, App(V("doublyStochastic"), Real(), Fin(d))),
                And(columns, rows))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = V("d"), b = V("B");
        return Disp(Equal(V("claim"), All("d", Nat(),
            Imp(new Formula.Relation(D(4), FormulaRelationOperator.LessThan, d),
                All("B", Matrix(d, Real()), Imp(Call("IsCirculant", b),
                    Imp(Call("IsBracelet", b), Call("IsUnistochastic", b))))))));
    }

    private static Formula BraceletInequality(string name, Formula d, Formula length) =>
        new Formula.Relation(Multiply(D(2), App(V("iSup"), Lambda(name, Fin(d), length))),
            FormulaRelationOperator.LessThanOrEqual,
            Seq(new Formula.Subscript(F.Sum, Seq(V(name), Colon, Sp, Fin(d))), Sp, length));
    private static Formula Length(Formula b, Formula i, Formula j, Formula k, Formula l) =>
        App(Qualified("Real", "sqrt"), Multiply(App(b, i, j), App(b, k, l)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Matrix(Formula d, Formula scalar) => Call("Matrix", Fin(d), Fin(d), scalar);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(V("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
