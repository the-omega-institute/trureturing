using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HwangKimWeightedSpectralRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HwangKimWeightedSpectralRefutation";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual matrix means need not have entrywise ordered eigenvalues.",
        H("The unequal-weight entrywise counterexample"),
        Blocks(
            Entry("spectral-order", "SpectralOrder", "Ordered eigenvalue comparison",
                StrictStatement(),
                "lambda(X,i) is the i-th decreasingly ordered Hermitian eigenvalue, "
                + "Matrix.IsHermitian.eigenvalues₀. This is non-strict entrywise spectral comparison, "
                + "with Hermitian X,Y; it is neither weak majorization nor weak log-majorization.", DescribeRole.Definition),
            Entry("claim", "claim", "The entrywise strengthening for actual means",
                Disp(Iff(V("claim"), ClaimBody())),
                "For every complex dimension m≥1, input count n≥2, strictly positive normalized "
                + "weights and positive definite inputs, ask whether LE≤λΩ holds for the actual CFC "
                + "logarithmic mean and epsilon-selected positive definite global argmin. The complete "
                + "quantifiers are retained; the proof supplies the specified 2×2 weighted counterexample.",
                DescribeRole.Definition),
            Entry("result", "result", "The specified unequal-weight witness refutes the comparison",
                Disp(Seq(Neg, Sp, P(ClaimBody()))),
                "Use weights (3/4,1/4), A=diag(256,1), B=[[13,3√3],[3√3,7]]/4. "
                + "Both inputs are positive definite. Put h=√399, K=[[9,2√3],[2√3,90]]/(4h), "
                + "M=(3I+K)/4 and W=MAM. Exact multiplication proves KAK=B. The positive transports "
                + "T=M⁻¹ and V=KM⁻¹ obey (3/4)T+(1/4)V=I and transport W to A,B. "
                + "BuresWassersteinTransport.finite_barycenter_of_dual identifies this W with the actual "
                + "unique global argmin. Thus the finite theorem has a concrete live mathematical consumer. "
                + "The logarithmic sum is log(2)H, H=[[51,√3],[√3,1]]/8. Orthogonal diagonalization of "
                + "B identifies its actual logarithm. Positive definiteness of H−I/10 and "
                + "(107/100)^10<2 imply that L−(107/100)I is positive definite by continuous functional "
                + "calculus. This proves λmin(L)>107/100 without assuming the desired spectral bound. "
                + "The source's exact expression λmin(L)=2^((13−√157)/4) is preserved as written "
                + "scientific context; that expression is not a separately asserted Lean endpoint. "
                + "Exact trace and determinant calculations give tr W=1159/8+3591/(16h), "
                + "det W=(73/8+297/(4h))². The rational brackets 1997/100<h<999/50 prove "
                + "q²−tr(W)q+det W<0 at q=107/100, hence λmin(W)<q. Combining these strict bounds "
                + "refutes the universal entrywise comparison for the actual means. The same actual pair fails near order: if C=L⁻¹#W≥I, then C²≥I and W−qI=C(L−qI)C+q(C²−I) is positive semidefinite. Its negative determinant at q=107/100 contradicts this. This exact application was kernel-checked; it is an application of the retained bounds and Riccati suppliers. "
                + "Source: Ma–Zhang revision2 Theorem (entrywise), CC BY 4.0. "
                + "Haobo Ma: ChronoAI Pte Ltd, Singapore only. Wenlin Zhang: NUS and ChronoAI Pte Ltd, "
                + "Singapore. This is a formal return of their written witness, not a new discovery. "
                + "The established transport criterion is credited to Bhatia–Jain–Lim. Their Theorem 1 "
                + "weak log-majorization and (54) LE≤λQ₁/₂ remain valid; the witness therefore separates "
                + "weak log-majorization from entrywise order and obstructs the unposed stronger entrywise "
                + "Q₁/₂≤λΩ reading, as attributed mathematical consequences. Q₁/₂≠Ω, and their actual "
                + "Conjecture 1 on unitarily invariant norms / weak majorization is not refuted. "
                + "The theorem itself refutes the entrywise claim; the full all-dimension/input-count "
                + "families, commuting equality case, near-to-entrywise bridge and literature comparison "
                + "consumers remain separate proof obligations and are not assumed as axioms.",
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
            Le(C("lambda", V("X"), V("i")), C("lambda", V("Y"), V("i"))));
        Formula right = And(C("IsHermitian", V("X")), And(C("IsHermitian", V("Y")), comparison));
        return Disp(All("m", Nat, All("X", Mat, All("Y", Mat,
            Iff(C("SpectralOrder", V("X"), V("Y")), right)))));
    }
    private static Formula ClaimBody()
    {
        Formula body = C("SpectralOrder", L, W);
        body = Imp(All("j", C("Fin", V("n")), C("PosDef", C("A", V("j")))), body);
        body = All("A", Arrow(C("Fin", V("n")), Mat), body);
        body = Imp(Eq(Seq(new Formula.Subscript(F.Sum, V("j")), Sp, C("w", V("j"))), D(1)), body);
        body = Imp(All("j", C("Fin", V("n")), Lt(D(0), C("w", V("j")))), body);
        body = All("w", Arrow(C("Fin", V("n")), Real), body);
        body = All("n", Nat, Imp(Le(D(2), V("n")), body));
        return All("m", Nat, Imp(Le(D(1), V("m")), body));
    }
}
