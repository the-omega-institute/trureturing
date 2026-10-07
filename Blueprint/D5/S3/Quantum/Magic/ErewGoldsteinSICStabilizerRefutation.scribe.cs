using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class ErewGoldsteinSICStabilizerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/erewgoldstein2025magic");
    private static readonly LibraryNoteRef Family =
        LibraryNoteRef.Create("D5/L/QuantumStates/tabiaappleby2013qutrit");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The special Clifford group of a qutrit is finite, and its eigenphase extension has only finitely many one-dimensional fixed spaces. The continuous qutrit SIC family supplies infinitely many distinct pure-state projectors. Consequently, some SIC fiducials are not Clifford-stabilizer states.",
        H("SIC fiducials beyond Clifford-stabilizer states"),
        Blocks(
            Definition("zeta", "The half-period phase", ZetaFormula(),
                "The computational basis is indexed by ZMod d. The clock phase is exp(2 pi i / d), and zeta is exp(pi i / d). The shift sends basis vector j to basis vector j + 1. Write D(a,b) for the displacement X to the power a times Z to the power b."),
            Definition("pauliGroup", "The single-qudit Pauli group", PauliFormula(),
                "The finite Pauli group includes the sign exponent x in ZMod 2 and the phase, shift and clock exponents k, a and b in ZMod d. Powers use the least nonnegative representatives of residues."),
            Definition("cliffordGroup", "The Clifford group", CliffordFormula(),
                "A Clifford matrix is unitary, and conjugation by it maps the entire Pauli group onto itself. Here Ad(U) sends P to U P U adjoint."),
            Definition("specialClifford", "The special Clifford group", SpecialFormula(),
                "Special Clifford matrices have determinant one."),
            Definition("Lambda", "The eigenvalue set", LambdaFormula(),
                "Lambda contains every eigenvalue of every special Clifford matrix. An eigenvalue has a nonzero eigenvector."),
            Definition("eigenphaseClifford", "The eigenphase extension", ExtensionFormula(),
                "The extension consists of all scalar multiples mu U with U special Clifford and mu in Lambda."),
            Definition("invariantSubspace", "The pointwise fixed space", FixedFormula(),
                "The invariant subspace is the intersection of the kernels of U minus the identity over U in S. The condition is pointwise fixation, U v = v."),
            Definition("IsNormalized", "Pure-state normalization", NormalizedFormula(),
                "The Hermitian inner product is the sum of conjugate(psi j) times phi j. Normalization is inner(psi,psi) = 1, equivalently Hilbert norm one."),
            Definition("IsCliffordStabilizerState", "Clifford-stabilizer states", StabilizerFormula(),
                "A normalized state is Clifford-stabilized when its complex line is exactly the pointwise fixed space of a subset of the eigenphase extension. This is the fixed-space formulation of the source's convention."),
            Definition("IsSICFiducial", "SIC fiducials", SICFormula(),
                "Every nonidentity displacement has overlap modulus one divided by the square root of d + 1. Multiplying a displacement by a unit-modulus phase preserves this condition."),
            Definition("claim", "The proposed stabilizer nature of SIC fiducials",
                Disp(Iff(F.Id("claim"), ClaimBody())),
                "The conjecture quantifies over all prime dimensions and all single-qudit SIC fiducials."),
            Theorem("specialClifford_three_finite", "Finiteness of the special qutrit Clifford group",
                Disp(Call("Finite", Call("specialClifford", D(3)))),
                "Conjugating X and Z gives a pair of Pauli matrices, so there are finitely many such pairs. If U and V give the same pair, V adjoint times U commutes with both X and Z. The clock-and-shift commutant consists of scalar matrices. Determinant one forces that scalar to be a cube root of unity. Thus every fiber contains finitely many matrices."),
            Theorem("eigenphaseClifford_three_finite", "Finiteness of the eigenphase extension",
                Disp(Call("Finite", Call("eigenphaseClifford", D(3)))),
                "A finite-dimensional matrix has finitely many eigenvalues. Taking the union over the finite special Clifford group leaves Lambda finite, and taking scalar multiples from two finite sets leaves the extension finite."),
            Theorem("stabilizer_projectors_three_finite", "Finitely many Clifford-stabilizer projectors",
                ProjectorsFormula(),
                "There are finitely many subsets of the eigenphase extension. Each subset determines one fixed space. Two normalized vectors spanning the same complex line have the same rank-one projector, so the set of resulting projectors is finite."),
            Describe.Lean(DescribeId.Create("erew-goldstein-qutrit-family"),
                DeclarationHandle.Create(Prefix + "qutritFiducial"), H("The continuous qutrit family"),
                StatementSource.FromAuthor(FamilyFormula()), AssessedProvenance.FromLiterature(Family),
                Blocks(Paragraph(Text("For each complex parameter z, the column vector has amplitudes 0, 1 and -z, divided by the square root of two."))), DescribeRole.Definition),
            Theorem("qutritFiducial_isSIC", "A unit circle of SIC fiducials", FamilySICFormula(),
                "For modulus-one z the vector is normalized. When a = 0 and b is nonzero, the overlap is -1/2 because 1 + omega + omega squared = 0. When a = 1 the overlap is -conjugate(z) omega to the power b divided by two; when a = 2 it is -z omega to the power 2b divided by two. Each has modulus 1/2, equal to one divided by the square root of 3 + 1. Tabia and Appleby state this family for z = e^{2it} with t in [0, pi/6]; the proof here covers every unit z by direct computation.",
                AssessedProvenance.FromLiterature(Family)),
            Theorem("qutrit_projector_injective", "Distinct parameters give distinct projectors", InjectionFormula(),
                "The projector entry in row 1, column 2 is -conjugate(z)/2. Equality of projectors therefore forces equality of the parameters."),
            Describe.Lean(DescribeId.Create("erew-goldstein-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Refutation in dimension three"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Par(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The complex unit circle is infinite: its real-coordinate image contains the entire range of cosine. The qutrit family maps that circle injectively to pure-state projectors. If every SIC fiducial were Clifford-stabilized, this infinite image would be a subset of the finite set of Clifford-stabilizer projectors. Hence the conjecture is false, already in prime dimension three."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("erew-goldstein-2025-sic-clifford-stabilizer"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("erew-goldstein-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("erew-goldstein-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Field(string x) => Seq(Mathbb, Grp(F.Id(x)));
    private static Formula Named(string x) => Seq(Operatorname, Grp(F.Id(x)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Subset(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.SubsetOf, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Par(y));
    private static Formula All(string x, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Some(string x, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Par(x), FormulaBinaryOperator.Multiply, Par(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(Par(x), FormulaBinaryOperator.Add, Par(y));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(Par(x), y);
    private static Formula Negate(Formula x) => new Formula.Negate(Par(x));
    private static Formula Residues(Formula d) => Call("ZMod", d);
    private static Formula Vec(Formula d) => Par(Seq(Residues(d), Sp, To, Sp, Field("C")));
    private static Formula Mat(Formula d) => Call("Matrix", Residues(d), Residues(d), Field("C"));
    private static Formula Sets(Formula domain) => Call("Set", domain);
    private static Formula Tuple(params Formula[] values) =>
        Par(Seq(values.SelectMany((value, index) =>
            index == 0 ? new[] { value } : new[] { Comma, Sp, value }).ToArray()));
    private static Formula Inner(Formula x, Formula y) => Call("inner", x, y);
    private static Formula Rho(Formula x) => Mul(x, Call("adjoint", x));
    private static Formula Where(Formula x, Formula predicate) => Seq(OpenBrace, Sp, x, Sp, Mid, Sp, predicate, Sp, CloseBrace);
    private static Formula Dimensions(Formula body) => All("d", Field("N"), Imp(Ne(F.Id("d"), D(0)), body));

    private static Formula ZetaFormula() => Disp(All("d", Field("N"),
        Eq(Call("zeta", F.Id("d")), Call("exp", new Formula.Fraction(Mul(Pi, F.Id("i")), F.Id("d"))))));

    private static Formula PauliFormula()
    {
        Formula d = F.Id("d"), p = F.Id("P"), x = F.Id("x"), k = F.Id("k"), a = F.Id("a"), b = F.Id("b");
        Formula scalar = Mul(Pow(Negate(D(1)), Call("val", x)), Pow(Call("zeta", d), Call("val", k)));
        Formula body = Some("x", Residues(D(2)), Some("k", Residues(d), Some("a", Residues(d), Some("b", Residues(d),
            Eq(p, Mul(scalar, Call("displacement", d, a, b)))))));
        return Disp(Dimensions(All("P", Mat(d), Iff(Mem(p, Call("pauliGroup", d)), body))));
    }

    private static Formula CliffordFormula()
    {
        Formula d = F.Id("d"), u = F.Id("U"), p = Call("pauliGroup", d);
        return Disp(Dimensions(All("U", Mat(d), Iff(Mem(u, Call("cliffordGroup", d)),
            And(Mem(u, Call("Unitary", d)), Eq(Call("image", Call("Ad", u), p), p))))));
    }

    private static Formula SpecialFormula()
    {
        Formula d = F.Id("d"), u = F.Id("U");
        return Disp(Dimensions(All("U", Mat(d), Iff(Mem(u, Call("specialClifford", d)),
            And(Mem(u, Call("cliffordGroup", d)), Eq(Call("det", u), D(1)))))));
    }

    private static Formula LambdaFormula()
    {
        Formula d = F.Id("d"), u = F.Id("U"), mu = F.Id("mu"), v = F.Id("v");
        Formula body = Some("U", Mat(d), And(Mem(u, Call("specialClifford", d)),
            Some("v", Vec(d), And(Ne(v, D(0)), Eq(Mul(u, v), Mul(mu, v))))));
        return Disp(Dimensions(All("mu", Field("C"), Iff(Mem(mu, Call("Lambda", d)), body))));
    }

    private static Formula ExtensionFormula()
    {
        Formula d = F.Id("d"), v = F.Id("V"), mu = F.Id("mu"), u = F.Id("U");
        Formula body = Some("mu", Field("C"), And(Mem(mu, Call("Lambda", d)),
            Some("U", Mat(d), And(Mem(u, Call("specialClifford", d)), Eq(v, Mul(mu, u))))));
        return Disp(Dimensions(All("V", Mat(d), Iff(Mem(v, Call("eigenphaseClifford", d)), body))));
    }

    private static Formula FixedFormula()
    {
        Formula d = F.Id("d"), s = F.Id("S"), v = F.Id("v"), u = F.Id("U");
        Formula fixedCondition = All("U", Mat(d), Imp(Mem(u, s), Eq(Mul(u, v), v)));
        Formula membership = Iff(Mem(v, Call("invariantSubspace", s)), fixedCondition);
        return Disp(Dimensions(All("S", Sets(Mat(d)), All("v", Vec(d), membership))));
    }

    private static Formula NormalizedFormula()
    {
        Formula d = F.Id("d"), psi = F.Id("psi");
        return Disp(Dimensions(All("psi", Vec(d), Iff(Call("IsNormalized", psi), Eq(Inner(psi, psi), D(1))))));
    }

    private static Formula StabilizerFormula()
    {
        Formula d = F.Id("d"), psi = F.Id("psi"), s = F.Id("S");
        Formula ray = Eq(Call("invariantSubspace", s),
            Call("span", Field("C"), new Formula.SetLiteral([psi])));
        Formula body = And(Call("IsNormalized", psi), Some("S", Sets(Mat(d)),
            And(Subset(s, Call("eigenphaseClifford", d)), ray)));
        return Disp(Dimensions(All("psi", Vec(d), Iff(Call("IsCliffordStabilizerState", d, psi), body))));
    }

    private static Formula SICFormula()
    {
        Formula d = F.Id("d"), psi = F.Id("psi"), a = F.Id("a"), b = F.Id("b");
        Formula overlap = Call("norm", Inner(psi, Mul(Call("displacement", d, a, b), psi)));
        Formula body = And(Call("IsNormalized", psi), All("a", Residues(d), All("b", Residues(d),
            Imp(Ne(Tuple(a, b), Tuple(D(0), D(0))),
                Eq(overlap, new Formula.Fraction(D(1), Call("sqrt", Add(d, D(1)))))))));
        return Disp(Dimensions(All("psi", Vec(d), Iff(Call("IsSICFiducial", d, psi), body))));
    }

    private static Formula ClaimBody()
    {
        Formula d = F.Id("d"), psi = F.Id("psi");
        return All("d", Field("N"), Imp(Call("Prime", d), All("psi", Vec(d),
            Imp(Call("IsSICFiducial", d, psi), Call("IsCliffordStabilizerState", d, psi)))));
    }

    private static Formula ProjectorsFormula()
    {
        Formula p = F.Id("P"), psi = F.Id("psi");
        return Disp(Call("Finite", Where(p, Some("psi", Vec(D(3)),
            And(Call("IsCliffordStabilizerState", D(3), psi), Eq(p, Rho(psi)))))));
    }

    private static Formula FamilyFormula()
    {
        Formula z = F.Id("z");
        return Disp(All("z", Field("C"), Eq(Call("qutritFiducial", z),
            new Formula.Fraction(Tuple(D(0), D(1), Negate(z)), Call("sqrt", D(2))))));
    }

    private static Formula FamilySICFormula()
    {
        Formula z = F.Id("z");
        return Disp(All("z", Field("C"), Imp(Eq(Call("norm", z), D(1)),
            Call("IsSICFiducial", D(3), Call("qutritFiducial", z)))));
    }

    private static Formula InjectionFormula()
    {
        Formula z = F.Id("z"), w = F.Id("w");
        return Disp(All("z", Field("C"), All("w", Field("C"),
            Imp(Eq(Rho(Call("qutritFiducial", z)), Rho(Call("qutritFiducial", w))), Eq(z, w)))));
    }
}
