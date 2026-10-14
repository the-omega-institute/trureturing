using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CirculantUnitaryLiftRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/rajchelkorzekwapuchalazyczkowski2021birkhoff");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A circulant unistochastic matrix of order ten has no circulant unitary lift.",
        H("Circulant unitary lifting fails at order ten"), Blocks(
            Paragraph(Text("Matrices use zero-based indices in Fin d. Subtraction in Fin d is modulo d. "
                + "Matrix.circulant z has entry z(i−j). The predicates IsCirculant and IsUnistochastic "
                + "are those of CirculantBraceletNonUnistochastic: a real matrix is circulant when it equals "
                + "Matrix.circulant v for some real vector v, and it is unistochastic when it equals "
                + "RHLinalg.normSqMatrix U for some U in Matrix.unitaryGroup. The latter matrix has entries ‖U i j‖².")),
            Entry("circulant-lift", "HasCirculantLift", "Circulant unitary lifts", LiftFormula(),
                "Definition 6, page 4: \"The set of d × d doubly circulant unistochastic matrices Cd² consists of these circulant unistochastic matrices for which there exists the corresponding unitary matrix that is circulant.\" The vector z describes this complex circulant unitary matrix. Its squared norms must agree with every entry of B.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("lifting-conjecture", "claim", "The circulant lifting conjecture", ClaimFormula(),
                "Section IV, Conjecture 19, page 11: \"The sets Cd ∩ Ud and Cd² coincide for all d, i.e., for every circulant unistochastic matrix it is possible to find a corresponding circulant unitary matrix.\" The formula quantifies over every natural d and every real d × d matrix B. A circulant unitary lift gives both circulantness and unistochasticity, so the displayed implication expresses the remaining inclusion in the asserted equality.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("refutation", "result", "A ten-dimensional refutation", Disp(Seq(Neg, Sp, V("claim"))),
                "The real matrix B has first row (9,4,0,0,4,0,4,0,0,4)/25 and is circulant. "
                + "Write i=5a+r and j=5b+s with a,b in {0,1} and r,s in {0,1,2,3,4}. "
                + "Set Q(i,j)=(−1)^a 1[s=r+1 modulo 5]−(−1)^b 1[r=s+1 modulo 5], W=3I+2Q and U=W/5. "
                + "The integer identity WWᵀ=25I makes U unitary, and RHLinalg.normSqMatrix U=B. "
                + "A circulant unitary with these squared norms would have coefficients z nonzero exactly at {0,1,9,4,6}. "
                + "Its row equations at shifts 1,4,3 are z(0)conj(z(9))+z(1)conj(z(0))=0, "
                + "z(0)conj(z(6))+z(4)conj(z(0))=0, and z(4)conj(z(1))+z(9)conj(z(6))=0. "
                + "Conjugating the first and combining it with the second gives z(9)conj(z(6))=z(4)conj(z(1)). "
                + "The third therefore forces 2z(9)conj(z(6))=0, contradicting the nonzero coefficients. "
                + "The obstruction concerns dimension ten. Lemma 18's result for d≤4 and the source's spectral characterization of doubly circulant matrices retain their stated scopes.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("rajchel-korzekwa-puchala-zyczkowski-2021-conjecture19-circulant-lift"),
                ResolutionKind.Refuted) : null);

    private static Formula LiftFormula()
    {
        Formula d = V("d"), b = V("B"), z = V("z");
        Formula circulant = App(Qualified("Matrix", "circulant"), z);
        return Disp(All("d", Nat(), All("B", Matrix(d, Real()),
            Equal(Call("HasCirculantLift", b), ExistsIn("z", Arrow(Fin(d), Complex()),
                And(Member(circulant, App(Qualified("Matrix", "unitaryGroup"), Fin(d), Complex())),
                    Equal(b, App(Qualified("RHLinalg", "normSqMatrix"), circulant))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = V("d"), b = V("B");
        return Disp(Equal(V("claim"), All("d", Nat(), All("B", Matrix(d, Real()),
            Imp(App(Qualified("CirculantBraceletNonUnistochastic", "IsCirculant"), b),
                Imp(App(Qualified("CirculantBraceletNonUnistochastic", "IsUnistochastic"), b),
                    Call("HasCirculantLift", b)))))));
    }

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
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
