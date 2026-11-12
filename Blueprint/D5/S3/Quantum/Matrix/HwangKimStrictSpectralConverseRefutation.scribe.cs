using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HwangKimStrictSpectralConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HwangKimStrictSpectralConverseRefutation";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict comparison of every ordered eigenvalue of the actual means does not imply near order.",
        H("Strict spectral domination and near order"),
        Blocks(
            Entry("strict-spectral-order", "StrictSpectralOrder", "Strict ordered eigenvalue comparison",
                StrictStatement(),
                "lambda(X,i) is the i-th decreasingly ordered Hermitian eigenvalue, "
                + "Matrix.IsHermitian.eigenvalues₀. The definition requires Hermitian X and Y. "
                + "Proof witnesses for Hermiticity do not affect the eigenvalue functions.", DescribeRole.Definition),
            Entry("claim", "claim", "The strict-spectral converse for actual means",
                Disp(Iff(V("claim"), ClaimBody())),
                "For every complex matrix size m≥1, input count n≥2, strictly positive normalized "
                + "weight vector and positive definite input family, ask whether strict comparison "
                + "of every sorted eigenvalue of LE and the actual epsilon-selected Wasserstein "
                + "barycenter would imply NearOrder. This is the reverse implication separated by "
                + "the first Ma–Zhang witness; it is not the original forward near-order question.",
                DescribeRole.Definition),
            Entry("result", "result", "The original witness refutes the converse",
                Disp(Seq(Neg, Sp, P(ClaimBody()))),
                "Use the original A=diag(4,1), B=[[19,−3√15],[−3√15,61]]/64 at weights (1/2,1/2). "
                + "The original positive-input, actual CFC log-Euclidean and global-argmin "
                + "Wasserstein proofs are reused. With u=√√2 and z=√265, LE has sorted eigenvalues "
                + "u and 1/u. For W, tr W=25/16+265/(16z) and det W=(5/8+10/z)². "
                + "Rational interval bounds prove tr W>2u, tr W>2/u and "
                + "(1/u)²−tr(W)/u+det W>0. Sortedness and the quadratic root identity therefore "
                + "give lambda(W,0)>u and lambda(W,1)>1/u. The original trace obstruction supplies "
                + "failure of near order. Thus the new strict-spectrum premise is proved for "
                + "actual means; neither an assumed premise nor a surrogate mean is used. "
                + "The original universal near-order refutation is reused, not a new discovery. "
                + "Source: Ma–Zhang revision2 Theorem 1 and Corollary (reverse), issue #29594, "
                + "CC BY 4.0. Haobo Ma: ChronoAI, Singapore. Wenlin Zhang: NUS and ChronoAI, "
                + "Singapore. This does not prove the second weighted witness, the arbitrary-size "
                + "families, or the full classification of reverse implications. BJL's actual "
                + "norm/weak-majorization Conjecture 1 and weak log-majorization remain intact.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula statement,
        string prose, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.FromAuthor(statement),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/hwangkim2024nearorder")),
        Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, b);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.And, P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Iff, P(y));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Mat => C("Matrix", C("Fin", V("m")), C("Fin", V("m")), Seq(Mathbb, Grp(V("C"))));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula L => C("logEuclidean", V("w"), V("A"));
    private static Formula W => C("wassersteinBarycenter", V("w"), V("A"));
    private static Formula StrictStatement()
    {
        Formula comparison = All("i", C("Fin", V("m")),
            Lt(C("lambda", V("X"), V("i")), C("lambda", V("Y"), V("i"))));
        Formula right = And(C("IsHermitian", V("X")), And(C("IsHermitian", V("Y")), comparison));
        return Disp(All("m", Nat, All("X", Mat, All("Y", Mat,
            Iff(C("StrictSpectralOrder", V("X"), V("Y")), right)))));
    }
    private static Formula ClaimBody()
    {
        Formula body = Imp(C("StrictSpectralOrder", L, W), C("NearOrder", L, W));
        body = Imp(All("j", C("Fin", V("n")), C("PosDef", C("A", V("j")))), body);
        body = All("A", Arrow(C("Fin", V("n")), Mat), body);
        body = Imp(Eq(Seq(new Formula.Subscript(F.Sum, V("j")), Sp, C("w", V("j"))), D(1)), body);
        body = Imp(All("j", C("Fin", V("n")), Lt(D(0), C("w", V("j")))), body);
        body = All("w", Arrow(C("Fin", V("n")), Real), body);
        body = All("n", Nat, Imp(Le(D(2), V("n")), body));
        return All("m", Nat, Imp(Le(D(1), V("m")), body));
    }
}
