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
            Thm("fixed_pair_equality", "Equality for a distinct pair of pure states",
                "Fix a matrix H with I−H and I+H positive semidefinite. For distinct projectors P and Q, let t be their ground distance. Phase alignment and orthogonalization give a common pair of orthonormal vectors. In their basis, the difference is t times the difference of the coordinate projectors. The same two unit vectors, one in each extremal eigenspace of H, give both projectors at equality."),
            Thm("countable_plan_slack", "Summing nonnegative testing slack",
                "The weighted difference between each ground cost and the half real trace pairing is nonnegative. Its sum equals the total cost minus the half real trace pairing against the difference of the two marginals."),
            Thm("countable_plan_equality", "Equality at each positive-weight entry",
                "A countable plan attains the fixed trace test exactly when every entry with strictly positive weight attains that test."),
            Thm("traceNorm_le_countable_cost", "Trace-norm lower bound for each plan",
                "An attaining Hermitian contraction supplies the bound by half the trace norm of the difference for every countable plan with Hermitian marginals."),
            Thm("traceNorm_le_wasserstein", "Trace-norm lower bound for the infimum",
                "Taking the infimum over the inhabited countable plan space preserves the bound by half the trace norm."),
            Thm("countable_plan_mem_closure", "Countable moments lie in the closed convex hull",
                "The two marginal matrices and the cost form a single moment. Finite partial sums with leftover mass placed at a fixed pure pair approximate this moment by finite convex combinations."),
            Thm("convexHull_realized_as_plan", "Finite convex combinations give countable plans",
                "Enumerate the vectors and weights of a finite convex combination and extend the weights by zero to obtain a plan with exactly the given moment."),
            Thm("finite_attainment_of_compact_hull", "A compact moment hull gives attainment",
                "Minimize the cost coordinate on the nonempty compact slice of the hull with the given marginals. The resulting moment is realized by a finitely supported plan."),
            Thm("finite_attainment", "Finite attainment of the countable infimum",
                "The two unit spheres give a compact pure-pair moment set, since the projector and ground maps are continuous. Its finite-dimensional convex hull is compact. Thus whenever a countable plan exists, a finitely supported plan attains the same infimum."),
            Thm("plan_nonempty_of_density", "Density matrices have a product plan",
                "Use the spectral decompositions of the marginals. Each pair of eigenvectors receives the product of their nonnegative eigenvalues, and the two finite sums reproduce the marginals."),
            Thm("finite_attainment_of_density", "Finite attainment for density matrices",
                "Every pair of positive semidefinite, trace-one marginals in finite dimension at least one has a finitely supported optimizer for the countable infimum."),
            Thm("wasserstein_eq_pairing_iff", "Sharpness of a fixed test",
                "The infimum equals the fixed trace test exactly when some finitely supported plan has only stationary or swapped-amplitude entries at strictly positive weights. Finite attainment supplies such a plan at equality, and summing nonnegative slack proves the converse."),
            Describe.Lean(DescribeId.Create("bsfwone-hasspectralcertificate"),
                DeclarationHandle.Create(Prefix + "HasSpectralCertificate"),
                H("The shared remainder and moving pairs"), StatementSource.FromAuthor(Disp(CertificateFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write Δ for the Hermitian difference of the marginals and P for the rank-one projector of a unit vector. The scalar factors a and b are the square roots of (1+t)/2 and (1−t)/2. The same u and v appear in both projectors of a pair, with the two amplitudes swapped."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bsfwone-wasserstein-eq-tracenorm-iff"),
                DeclarationHandle.Create(Prefix + "wasserstein_eq_traceNorm_iff"),
                H("Equality with half the trace norm"),
                StatementSource.FromAuthor(Disp(EqualityFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Equation (62) asks when the lower bound is attained. Here the order is one and the ground is given by Eq. (81). The distance is the infimum over the original countable plans. Natural-number indices and nonnegative weights encode the strictly positive weights of Definitions 8–9 by dropping zeros or enumerating and padding with zeros.")),
                    Paragraph(Text("For necessity, use the Hermitian sign of the difference in a finite optimizer. Group the stationary entries into the same positive semidefinite sum R in both marginals. Reindex the remaining positive-weight entries by Fin m. Each moving pair has parameter equal to its ground distance and has the stated swapped amplitudes in the strict spectral subspaces.")),
                    Paragraph(Text("For sufficiency, assign the nonnegative eigenvalues of R as weights of stationary pairs, then add the specified moving pairs. The extremal eigenspaces of the sign are orthogonal. This gives unit vectors in the two displayed projectors and gives ground distance t for each moving pair. Taking the trace of a marginal gives total weight one. Every positive-weight entry attains the sign test, so the countable-plan infimum equals half the trace norm. For equal marginals one can take m equal to zero and R equal to the common matrix."))),
                DescribeRole.Theorem),
            Thm("phase_diagnostic", "Changing one phase changes the slack",
                "For H diagonal with entries 1 and −1, use source (4/5, 3i/5) and target (3/5, 4i/5). The ground and pairing both equal 7/25. Changing the target to (3/5, −4i/5) makes the ground equal to 1 and leaves the pairing equal to 7/25, giving slack 18/25."))));

    private static DocumentBlock Thm(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Theorem);

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bsfwone-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

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
        Formula n = F.Id("n"), m = F.Id("m"), i = F.Id("i"), r = F.Id("R");
        Formula w = F.Id("w"), t = F.Id("t"), u = F.Id("u"), v = F.Id("v");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula mat = Call("Matrix", Call("Fin", n), Call("Fin", n), Seq(Mathbb, Grp(F.Id("C"))));
        Formula indices = Call("Fin", m);
        Formula delta = new Formula.Binary(Rho, FormulaBinaryOperator.Subtract, SigmaLower);
        Formula wi = new Formula.Apply(w, [i]), ti = new Formula.Apply(t, [i]);
        Formula ui = new Formula.Apply(u, [i]), vi = new Formula.Apply(v, [i]);
        Formula a = Call("sqrt", Seq(Frac, Grp(Seq(D(1), Plus, ti)), Grp(D(2))));
        Formula b = Call("sqrt", Seq(Frac, Grp(Seq(D(1), F.Minus, ti)), Grp(D(2))));
        Formula Member(Formula x, string space) =>
            new Formula.Relation(x, FormulaRelationOperator.MemberOf, Call(space, delta));
        Formula Lt(Formula x) => new Formula.Relation(D(0), FormulaRelationOperator.LessThan, x);
        Formula atMostOne = new Formula.Relation(ti, FormulaRelationOperator.LessThanOrEqual, D(1));
        Formula moving = All(i, indices, And(Lt(wi), And(Lt(ti), And(atMostOne,
            And(Member(ui, "positiveSubspace"), Member(vi, "negativeSubspace"))))));
        Formula Marginal(Formula first, Formula second)
        {
            Formula vector = Seq(first, Cdot, Sp, ui, Plus, second, Cdot, Sp, vi);
            Formula sum = Seq(new Formula.Subscript(Sum, Seq(i, InMacro, Sp, indices)), Sp,
                wi, Cdot, Sp, Call("rankOneDensity", vector));
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
        Formula iff = new Formula.Logic(Par(Call("HasSpectralCertificate", delta)),
            FormulaLogicOperator.Iff, Par(data));
        return All(n, naturals, All(Rho, mat, All(SigmaLower, mat,
            Imp(Call("IsHermitian", delta), iff))));
    }

    private static Formula EqualityFormula()
    {
        Formula n = F.Id("n");
        Formula fin = Call("Fin", n);
        Formula mat = Call("Matrix", fin, fin, Seq(Mathbb, Grp(F.Id("C"))));
        Formula delta = new Formula.Binary(Rho, FormulaBinaryOperator.Subtract, SigmaLower);
        Formula halfNorm = Seq(Frac, Grp(Call("traceNorm", delta)), Grp(D(2)));
        Formula density = And(Call("PosSemidef", Rho), And(Eq(Call("trace", Rho), D(1)),
            And(Call("PosSemidef", SigmaLower), Eq(Call("trace", SigmaLower), D(1)))));
        Formula lhs = Eq(Call("wasserstein", Rho, SigmaLower), halfNorm);
        Formula rhs = Call("HasSpectralCertificate", delta);
        Formula iff = new Formula.Logic(Par(lhs), FormulaLogicOperator.Iff, Par(rhs));
        return All(n, Seq(Mathbb, Grp(F.Id("N"))), All(Rho, mat, All(SigmaLower, mat,
            Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n), Imp(density, iff)))));
    }
}
