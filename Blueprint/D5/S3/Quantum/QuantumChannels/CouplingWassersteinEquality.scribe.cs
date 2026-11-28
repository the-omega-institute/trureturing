using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class CouplingWassersteinEqualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/CouplingWassersteinEquality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/beatty2025couplingwasserstein");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For order one with the pure-state trace ground, equality with half the trace norm is equivalent to a common positive semidefinite remainder and a finite family of moving pairs. In each pair the two projectors use the same positive and negative spectral vectors with swapped amplitudes.",
        H("Equality in trace-ground coupling transport"),
        Blocks(
            Describe.Lean(DescribeId.Create("bsfwone-hasspectralcertificate"),
                DeclarationHandle.Create(Prefix + "HasSpectralCertificate"),
                H("The shared remainder and moving pairs"), StatementSource.FromAuthor(Disp(CertificateFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof h establishes that Δ = ρ − σ is Hermitian and determines the strict spectral subspaces of Δ. The predicate takes both marginals. The map val takes a unit vector to its underlying complex vector. The rankOneDensity map sends z to zz*. The square roots are real. The map ofReal sends each amplitude and each weight to ℂ before it acts on the corresponding vector or matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bsfwone-wasserstein-eq-tracenorm-iff"),
                DeclarationHandle.Create(Prefix + "wasserstein_eq_traceNorm_iff"),
                H("Equality with half the trace norm"),
                StatementSource.FromAuthor(Disp(EqualityFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The question following Eq. (62) asks when the dual-norm lower bound is attained. At order one with the pure trace ground of Eq. (81), Proposition 26 and Eq. (82) identify that dual norm with half the trace norm. The distance is the infimum over the original countable plans of Definitions 8–9. Dropping zero weights or enumerating and padding with zeros preserves the two marginals and cost. The term hermitianSub(p,q) proves that ρ − σ is Hermitian from the positive semidefinite hypotheses p and q.")),
                    Paragraph(Text("Proposition 16 establishes finite attainment in the paper. Here the two marginal matrices and the cost form a joint moment. Finite partial sums with leftover mass on a fixed pure pair put every countable plan moment in the closed convex hull of the pure-pair moment set. The moment set and its finite-dimensional convex hull are compact. The spectral product plan makes the fixed-marginal slice nonempty. Minimizing its cost coordinate and enumerating the resulting finite convex combination gives an optimizer for the original infimum.")),
                    Paragraph(Text("For necessity, use the Hermitian sign of the difference in a finite optimizer. Group the stationary entries into the same positive semidefinite sum R in both marginals. Reindex the remaining positive-weight entries by Fin m. Each moving pair has parameter equal to its ground distance and has the stated swapped amplitudes in the strict spectral subspaces.")),
                    Paragraph(Text("For sufficiency, assign the nonnegative eigenvalues of R as weights of stationary pairs, then add the specified moving pairs. The extremal eigenspaces of the sign are orthogonal. This gives unit vectors in the two displayed projectors and gives ground distance t for each moving pair. Taking the trace of a marginal gives total weight one. Every positive-weight entry attains the sign test, so the countable-plan infimum equals half the trace norm. For equal marginals one can take m equal to zero and R equal to the common matrix."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("beatty-stilck-franca-2024-eq62-trace-ground"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));

    private static Formula CertificateFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), i = F.Id("i"), r = F.Id("R"), h = F.Id("h");
        Formula w = F.Id("w"), t = F.Id("t"), u = F.Id("u"), v = F.Id("v");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula mat = Call("Matrix", Call("Fin", n), Call("Fin", n), Seq(Mathbb, Grp(F.Id("C"))));
        Formula indices = Call("Fin", m);
        Formula delta = new Formula.Binary(Rho, FormulaBinaryOperator.Subtract, SigmaLower);
        Formula wi = new Formula.Apply(w, [i]), ti = new Formula.Apply(t, [i]);
        Formula ui = Call("val", new Formula.Apply(u, [i]));
        Formula vi = Call("val", new Formula.Apply(v, [i]));
        Formula a = Call("sqrt", Seq(Frac, Grp(Seq(D(1), Plus, ti)), Grp(D(2))));
        Formula b = Call("sqrt", Seq(Frac, Grp(Seq(D(1), F.Minus, ti)), Grp(D(2))));
        Formula Member(Formula x, string space) =>
            new Formula.Relation(x, FormulaRelationOperator.MemberOf, Call(space, delta, h));
        Formula Lt(Formula x) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, x);
        Formula atMostOne = new Formula.Relation(ti, FormulaRelationOperator.LessThanOrEqual, D(1));
        Formula moving = All(i, indices, And(Lt(wi), And(Lt(ti), And(atMostOne,
            And(Member(ui, "positiveSubspace"), Member(vi, "negativeSubspace"))))));
        Formula Marginal(Formula first, Formula second)
        {
            Formula vector = Seq(Call("ofReal", first), Cdot, Sp, ui,
                Plus, Call("ofReal", second), Cdot, Sp, vi);
            Formula sum = Seq(new Formula.Subscript(Sum, Seq(i, InMacro, Sp, indices)), Sp,
                Call("ofReal", wi), Cdot, Sp, Call("rankOneDensity", vector));
            return Seq(r, Plus, sum);
        }
        Formula claims = And(Call("PosSemidef", r), And(moving,
            And(Eq(Rho, Marginal(a, b)), Eq(SigmaLower, Marginal(b, a)))));
        Formula realArray = new Formula.TypeArrow(indices, reals);
        Formula unitArray = new Formula.TypeArrow(indices, Call("UnitVector", n));
        Formula Some(Formula x, Formula type, Formula body) =>
            Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
        Formula data = Some(r, mat, Some(m, naturals, Some(w, realArray, Some(t, realArray,
            Some(u, unitArray, Some(v, unitArray, claims))))));
        Formula iff = new Formula.Logic(Par(Call("HasSpectralCertificate", Rho, SigmaLower, h)),
            FormulaLogicOperator.Iff, Par(data));
        return All(n, naturals, All(Rho, mat, All(SigmaLower, mat,
            All(h, Call("IsHermitian", delta), iff))));
    }

    private static Formula EqualityFormula()
    {
        Formula n = F.Id("n");
        Formula fin = Call("Fin", n);
        Formula mat = Call("Matrix", fin, fin, Seq(Mathbb, Grp(F.Id("C"))));
        Formula delta = new Formula.Binary(Rho, FormulaBinaryOperator.Subtract, SigmaLower);
        Formula halfNorm = Seq(Frac, Grp(Call("traceNorm", delta)), Grp(D(2)));
        Formula p = F.Id("p"), q = F.Id("q");
        Formula lhs = Eq(Call("wasserstein", Rho, SigmaLower), halfNorm);
        Formula rhs = Call("HasSpectralCertificate", Rho, SigmaLower, Call("hermitianSub", p, q));
        Formula iff = new Formula.Logic(Par(lhs), FormulaLogicOperator.Iff, Par(rhs));
        Formula withTarget = All(q, Call("PosSemidef", SigmaLower),
            Imp(Eq(Call("trace", SigmaLower), D(1)), iff));
        Formula withSource = All(p, Call("PosSemidef", Rho),
            Imp(Eq(Call("trace", Rho), D(1)), withTarget));
        Formula positiveDimension = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n);
        return All(n, Seq(Mathbb, Grp(F.Id("N"))),
            All(Rho, mat, All(SigmaLower, mat, Imp(positiveDimension, withSource))));
    }
}
