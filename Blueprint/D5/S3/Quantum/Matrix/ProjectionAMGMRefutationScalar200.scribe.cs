using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class ProjectionAMGMRefutationScalar200Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.";
    private static readonly LibraryNoteRef Sly =
        LibraryNoteRef.Create("D5/L/QuadraticForms/sunluoye2020projectionamgm");
    private static readonly LibraryNoteRef Kly =
        LibraryNoteRef.Create("D5/L/QuadraticForms/kimleeyun2025randompermutations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual real unit-column basis at n=200 refutes the all-order scalar first-moment projection comparison.",
        H("Scalar coordinate-descent projection AM-GM counterexample"),
        Blocks(
            Entry("mean-proj", "meanProj", "Reuse the existing arithmetic mean", Alias("meanProj"),
                "This abbreviation directly consumes ProjectionAMGMRefutation.meanProj; it introduces no different normalization or assertion.", true),
            Entry("sym-prod", "symProd", "Reuse the complete reversed-word average", Alias("symProd"),
                "This abbreviation directly consumes ProjectionAMGMRefutation.symProd: inverse n factorial times the sum over all labelled permutations, with the first entry rightmost.", true),
            Entry("cd-family", "IsCDFamily", "Real unit independent coordinate columns", Family(),
                "The columns are unit vectors and linearly independent in the full real n-dimensional space. At positive n this is an actual square basis; neither a dependent family nor mutual orthogonality is substituted.", true),
            Entry("cd-projection", "cdProj", "Complement projection of a coordinate column", Projection(),
                "The scalar block specialization d_i=1 of SLY Claim 4.1 uses I-a_i a_i^T. Unit length makes each complement a self-adjoint idempotent contraction. Claim 4.1 itself states identities and is not refuted.", true),
            Entry("scalar-claim", "claimScalar", "The complete all-order scalar assertion", Claim(),
                "For every positive n and every real unit independent family in R^n, the arithmetic mean raised to n minus the complete n! reversed-word average is positive semidefinite. This is the scalar specialization of SLY arXiv:1503.06387v3 Conjecture 3.1/(37) in its coordinate-descent application, and the structured first-moment comparison named original matrix AM-GM in KLY arXiv:2505.23152v1 Appendix E.2 under Assumption 2.2. No dimension cap, permutation sample, conditioning restriction or second-moment target is added.", true),
            Entry("scalar-refutation", "result", "A finite basis gives a strict negative quadratic form", Disp(Seq(Neg, Sp, V("claimScalar"))),
                "The supplied proof uses n=N=200, K=10^9, s=sqrt(K^2+1), a0=e1, ai=(K e1+e(i+1))/s for 1<=i<=198, a199=(e0-e1)/sqrt(2), and z=e0+200e1. It proves unit length and linear independence at this finite K, bounds the full difference against an auxiliary 199P+Q family, and proves z^T(M^200-G)z < -3/32+15840396/1000000000 < -1/16 < 0. The dependent family is only a comparison. This closed theorem has the literal type Not claimScalar.", false),
            Paragraph(Text("Existing-owner integration: the sole OpenProblemResolutionClaim remains on ProjectionAMGMRefutation.result for sun-luo-ye-2020-projection-matrix-amgm, with this result as an additional member. This document creates no second claim. Admission basis is open-problem-resolution under the original all-n Tier 1 registration #17674 (2026-10-16T05:39:52Z). Its scoped status evidence is contextual namedness plus the preserved exact-claim literature screen, not the already-refuted unrestricted conjecture's former status.")),
            Paragraph(Text("The ended source review was quality approve, tests approve, architecture comment. The architecture concern about exact named-assertion status remains disclosed: no inspected passage independently labels this precise restriction a still-open conjecture. This author's existing-owner interpretation uses the named KLY first-moment display, SLY's explicit application and the original registration together; later independent complete admission review remains required. The historical proof-shape disagreement is not adjudicated here; declaration-level author accounting and actual consumers are recorded in the existing Problems dossier.")),
            Paragraph(Text("Only the scalar projection endpoint is formalized. Taking d_i=1 directly supplies ordinary SLY source specialization. The conventional symmetric positive square root gives an ordinary orthogonal-conjugacy correspondence with SPD unit-diagonal Hessians; no formal Hessian, full-block or update-transport endpoint is claimed. KLY does not separately specify its square-root choice in the inspected passages. Its later Appendix E.2 future work concerns second moments.")),
            Paragraph(Text("Evidence and literature limits: the proof source is reused verbatim, SHA-256 1067ac81d5cb1acca53faf795d906c6d832b55ab7c16c3890f44a6c143ca15ec. Historical private native evidence is not current acceptance. SLY journal text, numbering and arXiv equivalence and KLY conference equality remain unverified; Luenberger-Ye Chapter 14 full text remains unread. The inherited 37-retrieval and 41/33-row citation screens are incomplete, some records were metadata-only, and failed web access supplies no negative evidence. No global absence, priority, novelty, smallest dimension, optimal RP-CD rate, expected-inverse or second-moment settlement is claimed. Full current source-bound normal acceptance, independent review and final-head CI remain separate obligations.")))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, bool definition) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Sly, Kly), Blocks(Paragraph(Text(prose))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Vector(Formula n) => Arrow(Fin(n), Real());
    private static Formula Family()
    {
        Formula n = V("n"), a = V("a"), i = V("i");
        return Disp(All("n", Nat(), All("a", Arrow(Fin(n), Vector(n)),
            Iff(Call("IsCDFamily", a), And(All("i", Fin(n),
                Eq(Call("dotProduct", App(a, i), App(a, i)), Num(1))),
                Call("LinearIndependent", Real(), a))))));
    }
    private static Formula Projection()
    {
        Formula n = V("n"), a = V("a"), i = V("i");
        return Disp(All("n", Nat(), All("a", Arrow(Fin(n), Vector(n)), All("i", Fin(n),
            Eq(Call("cdProj", a, i), Sub(Num(1), Call("Matrix.vecMulVec", App(a, i), App(a, i))))))));
    }
    private static Formula Alias(string name) => Disp(Eq(V(name),
        Qualified("ProjectionAMGMRefutation", name)));
    private static Formula Claim()
    {
        Formula n = V("n"), a = V("a"), i = V("i");
        Formula p = Lambda("i", Fin(n), Call("cdProj", a, i));
        return Disp(Iff(V("claimScalar"), All("n", Nat(), All("a", Arrow(Fin(n), Vector(n)),
            Imp(Leq(Num(1), n), Imp(Call("IsCDFamily", a),
                Pos(Sub(Pow(Call("meanProj", p), n), Call("symProd", p)))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, type)), Comma, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : V(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula f, Formula x) => Seq(f, Parenthesized(x));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(V(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Pos(Formula a) => Call("Matrix.PosSemidef", a);
}
