using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class SeparableConeResidualWitnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Resource/SeparableConeResidualWitness.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { F.Operatorname, F.Grp(V(name)), F.Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([F.Comma, F.Sp]);
            parts.Add(args[i]);
        }
        parts.Add(F.Close);
        return F.Seq([.. parts]);
    }
    private static Formula Eq(Formula x, Formula y) => F.Seq(x, F.Sp, F.Eq, F.Sp, y);
    private static Formula Sub(Formula x, Formula y) => F.Seq(x, F.Sp, F.Minus, F.Sp, y);
    private static Formula Minus(Formula x) => F.Seq(F.Minus, x);
    private static Formula Le(Formula x, Formula y) => F.Seq(x, F.Sp, F.Leq, F.Sp, y);
    private static Formula Pair(Formula x, Formula y) => Call("pairing", x, y);
    private static Formula E(Formula x) => Call("e", x);
    private static Formula Sep(Formula x) => Call("separableCone", x);
    private static Formula Bp(Formula x) => Call("blockPositive", x);
    private static Formula SqNorm(Formula x) =>
        F.Seq(F.Vert, F.Sp, x, F.Vert, F.Caret, F.Grp(F.D(2)));
    private static Formula And(params Formula[] terms)
    {
        var result = terms[^1];
        for (var i = terms.Length - 2; i >= 0; i--)
            result = new Formula.Logic(terms[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => F.Seq(x, F.Sp, F.Leftrightarrow, F.Sp, y);
    private static Formula All(Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), V("Mat")))], body);

    public DocumentDefinition Create()
    {
        var rInput = V("R");
        var p = V("P");
        var q = V("Q");
        var r = V("r");
        var s = V("S");
        var w = V("W");
        var zero = F.D(0);
        var nearest = Call("nearestSeparable", rInput);
        var distance = Call("distanceSq", rInput, p);
        var argmin = Call("Argmin", rInput, p);
        var decomposition = And(Sep(p), Bp(Minus(r)), Eq(Pair(p, r), zero),
            Eq(rInput, F.Seq(p, F.Plus, r)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The separable matrix argmin identifies the canonical negative Moreau residual.",
            H("Canonical Separable Cone Residual"),
            Blocks(
                Paragraph(Text("Throughout, m and n are arbitrary natural numbers, including zero. "
                    + "Write I = Fin m x Fin n and Mat = Matrix I I Complex. All optimization, pairing "
                    + "and duality statements range over all complex matrices in Mat. The scalar field "
                    + "for linearity, cones and inner products is Real. No trace-one, rank or positive-dimension "
                    + "assumption is made.")),
                Describe.Lean(DescribeId.Create("entry-space"), DeclarationHandle.Create(Prefix + "EntrySpace"),
                    H("Standard entry Hilbert space"),
                    StatementSource.FromAuthor(F.Disp(Eq(V("H"), Call("EuclideanSpace",
                        F.Seq(F.Mathbb, F.Grp(V("C"))), F.Seq(V("I"), F.Times, F.Sp, V("I")))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("H uses the standard complex Euclidean norm and its existing real "
                        + "inner product. It is not the Hermitian subspace and its norm is not the default matrix norm."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("entry-equivalence"), DeclarationHandle.Create(Prefix + "entryEquiv"),
                    H("Continuous real linear entry equivalence"),
                    StatementSource.FromAuthor(F.Disp(F.Seq(V("e"), F.Colon, V("Mat"), F.Sp,
                        F.Equiv, F.Underscore, F.Grp(F.Mathbb, F.Grp(V("R"))), F.Sp, V("H")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The map e = entryEquiv and its inverse are continuous and real linear. "
                        + "The theorem entryEquiv_apply states e(A)(i,j) = A(i,j) for every A and every i,j in I."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("entry-pairing"), DeclarationHandle.Create(Prefix + "entry_inner"),
                    H("Metric and trace pairing agree"),
                    StatementSource.FromAuthor(F.Disp(All(Eq(Call("innerReal", E(s), E(w)), Pair(s, w)), "S", "W"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The existing pairing is Re(trace(S.conjTranspose * W)). "
                        + "The theorem pairing_symm gives pairing(S,W) = pairing(W,S) for all matrices. "
                        + "Thus this is a metric identification, beyond continuity or a trace expansion alone."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("matrix-distance"), DeclarationHandle.Create(Prefix + "distanceSq"),
                    H("Independent matrix objective"),
                    StatementSource.FromAuthor(F.Disp(All(Eq(distance, Pair(Sub(rInput, p), Sub(rInput, p))), "R", "P"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The objective is defined solely from the existing pairing and matrix subtraction."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("distance-is-hilbert-square"), DeclarationHandle.Create(Prefix + "distanceSq_eq"),
                    H("Squared distance in entry coordinates"),
                    StatementSource.FromAuthor(F.Disp(All(Eq(distance, SqNorm(E(Sub(rInput, p)))), "R", "P"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The norm in this equality is the Euclidean norm on H."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("independent-generators"), DeclarationHandle.Create(Prefix + "sourceGenerators"),
                    H("PSD product generators"),
                    StatementSource.FromAuthor(F.Disp(F.Seq(V("G"), F.Eq, F.OpenBrace, s, F.Sp, F.Mid, F.Sp,
                        F.Exists, F.Sp, V("A"), F.Comma, V("B"), F.Comma, F.Sp,
                        And(Call("PosSemidef", V("A")), Call("PosSemidef", V("B")),
                            Eq(s, Call("kronecker", V("A"), V("B")))), F.CloseBrace))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("A ranges over Matrix (Fin m) (Fin m) Complex and B over "
                        + "Matrix (Fin n) (Fin n) Complex, independently. G denotes sourceGenerators m n."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("closed-conic-hull"), DeclarationHandle.Create(Prefix + "closed_conic_hull_eq_separable"),
                    H("Closed nonnegative conic hull is SEP"),
                    StatementSource.FromAuthor(F.Disp(Eq(Call("closure", Call("nonnegativeConicHull", V("G"))),
                        F.Seq(F.OpenBrace, s, F.Sp, F.Mid, F.Sp, Sep(s), F.CloseBrace)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The hull is PointedCone.hull Real G, so zero and all finite nonnegative "
                        + "real combinations are included. The proof identifies the finite-sum representation and "
                        + "reuses isClosed_separableCone, including empty dimensions."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("transported-cone"), DeclarationHandle.Create(Prefix + "separableProperCone"),
                    H("The transported proper cone"),
                    StatementSource.FromAuthor(F.Disp(F.Seq(V("K"), F.Eq, F.OpenBrace, V("v"), F.Sp, F.InMacro,
                        F.Sp, V("H"), F.Sp, F.Mid, F.Sp, Sep(Call("inverseEntry", V("v"))), F.CloseBrace))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("K = separableProperCone m n is a ProperCone Real H. "
                        + "mem_separableProperCone gives the displayed membership equivalence, with inverseEntry = e.symm. "
                        + "entry_mem_separableProperCone specializes it to e(S) in K iff separableCone(S). "
                        + "Its closedness is transported through the continuous inverse of e."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("concrete-inner-dual"), DeclarationHandle.Create(Prefix + "entry_mem_innerDual_iff"),
                    H("The concrete nonnegative dual"),
                    StatementSource.FromAuthor(F.Disp(All(Iff(F.Seq(E(w), F.Sp, F.InMacro, F.Sp, Call("innerDual", V("K"))), Bp(w)), "W"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("innerDual uses innerReal(v,e(W)) >= 0 for every v in K. "
                        + "Block positivity on arbitrary complex matrices does not by itself assert Hermiticity."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("independent-argmin"), DeclarationHandle.Create(Prefix + "Argmin"),
                    H("The independent argmin predicate"),
                    StatementSource.FromAuthor(F.Disp(All(Iff(argmin, And(Sep(p), All(Implies(Sep(q),
                        Le(distance, Call("distanceSq", rInput, q))), "Q"))), "R", "P"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("This definition contains neither projection nor uniqueness nor a witness conclusion."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("unique-argmin"), DeclarationHandle.Create(Prefix + "existsUnique_argmin"),
                    H("A unique minimizer for every matrix"),
                    StatementSource.FromAuthor(F.Disp(All(F.Seq(F.Exists, F.Bang, F.Sp, p, F.Sp, F.InMacro,
                        F.Sp, V("Mat"), F.Comma, F.Sp, argmin), "R"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("nearestSeparable chooses the point from this independent characterization. "
                        + "nearestSeparable_spec proves Argmin(R,nearestSeparable(R)); nearestSeparable_unique proves "
                        + "P = nearestSeparable(R) for every P satisfying Argmin(R,P). Existence is unconditional."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("projection-identification"), DeclarationHandle.Create(Prefix + "nearestSeparable_projection"),
                    H("Identification with the generic cone projection"),
                    StatementSource.FromAuthor(F.Disp(All(Eq(E(nearest), Call("coneProjection", V("K"), E(rInput))), "R"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("This equality is proved after the independent optimization problem has been solved."))), DescribeRole.Theorem),
                Paragraph(Text("In the following two statements, for each input R set P = nearestSeparable(R), "
                    + "r = R - P and W = P - R. These are dependent abbreviations, not extra hypotheses.")),
                Describe.Lean(DescribeId.Create("unique-polar-decomposition"), DeclarationHandle.Create(Prefix + "separable_moreau_decomposition"),
                    H("Unique orthogonal polar decomposition"),
                    StatementSource.FromAuthor(F.Disp(All(And(decomposition,
                        All(Implies(And(Sep(q), Bp(Minus(V("s"))), Eq(Pair(q, V("s")), zero),
                            Eq(rInput, F.Seq(q, F.Plus, V("s")))), And(Eq(q, p), Eq(V("s"), r))), "Q", "s")), "R"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The residual r lies in the polar cone: its negative lies in the nonnegative dual. "
                        + "The uniqueness follows from the existing moreau_decomposition theorem and applies to this "
                        + "orthogonal decomposition, not to all entanglement witnesses."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("canonical-residual-witness"), DeclarationHandle.Create(Prefix + "separable_cone_residual_witness"),
                    H("The canonical negative residual witness"),
                    StatementSource.FromAuthor(F.Disp(All(Implies(Call("PosSemidef", rInput), And(
                        Sep(p), Eq(rInput, F.Seq(p, F.Plus, r)), Call("IsHermitian", w), Bp(w), Eq(Pair(p, r), zero),
                        All(Implies(Sep(s), And(Le(Pair(s, r), zero), Le(zero, Pair(s, w)))), "S"),
                        Eq(Pair(rInput, w), Minus(Pair(r, r))), Eq(Pair(rInput, w), Minus(SqNorm(E(r)))),
                        Implies(F.Seq(F.Neg, F.Sp, Sep(rInput)), F.Seq(Pair(rInput, w), F.Lt, zero)))), "R"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Only the physical witness conclusion requires a PSD input R. "
                        + "The separable minimizer P is PSD, hence P and R are Hermitian and W = P - R is Hermitian. "
                        + "W is not asserted PSD. On this source domain the displayed projection and pairing agree "
                        + "with the finite Hermitian/PSD problem because the same entries and trace pairing are used. "
                        + "Strict negativity additionally requires nonseparability; the negative-square identities hold even inside SEP."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("inside-cone-branch"), DeclarationHandle.Create(Prefix + "separable_zero_residual"),
                    H("Zero residual inside the cone"),
                    StatementSource.FromAuthor(F.Disp(All(Implies(Sep(rInput), And(Eq(nearest, rInput),
                        Eq(Sub(rInput, nearest), zero), Eq(Sub(nearest, rInput), zero))), "R"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("nearestSeparable_of_separable also exposes the first equality separately. "
                        + "Zero and any PSD product matrix satisfy this branch."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("zero-residual-characterization"), DeclarationHandle.Create(Prefix + "zero_residual_iff"),
                    H("Zero residual characterizes separability"),
                    StatementSource.FromAuthor(F.Disp(All(Iff(Eq(Sub(rInput, nearest), zero), Sep(rInput)), "R"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("This equivalence holds for every matrix and all natural dimensions. "
                        + "No entangled matrix is assumed to exist in each dimension."))), DescribeRole.Theorem),
                Paragraph(Text("This unit supplies only the separable-cone row. The finance row still lacks an "
                    + "independently specified canonical shadow-price residual for the unrestricted market. "
                    + "The Weil row still needs its Hilbert carrier, critical cone and closedness, pairing/Riesz "
                    + "identification, and recovery of the source negative direction. The Nyman row is independent. "
                    + "No whole-atom closure, Riemann-hypothesis result, or general Banach extension is asserted.")))));
    }
}
