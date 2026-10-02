using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CyclicYangBaxterPauliRigidityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/galindorowell2026unitaryyb");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mixed-sign Gaussian in dimension fifteen refutes the Pauli-direction rigidity conjecture for cyclic unitary Yang–Baxter operators.",
        H("A mixed-sign Gaussian refutes Galindo–Rowell Conjecture 10.6"),
        Blocks(
            Node("clock-matrix", "The cyclic clock matrix", "clockZ", ClockFormula(),
                "The source fixes the clock by (arXiv:2608.16865v1, §10.2): \"Ze_j=w^je_j\". The diagonal entry at j is w raised to the canonical ZMod representative.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pauli-direction", "The Pauli-direction operator", "P", PFormula(),
                "The source writes (arXiv:2608.16865v1, §10.2): \"P_α=X⊗Z^α\". The Lean definition is the Kronecker product of the shift and the α-th clock power. The inner val is Units.val and the outer val is ZMod.val.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cyclic-operator", "The cyclic coefficient operator", "R", RFormula(),
                "The source writes (arXiv:2608.16865v1, §10.2): \"R(a)=∑_{t=0}^{d−1}a_tP^t\". The Lean sum ranges over ZMod d and uses the literal P power and coefficient scalar multiplication.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("braid-ybe", "The braid Yang–Baxter equation", "BraidYBE", BraidFormula(),
                "Section 2 of arXiv:2608.16865v1 displays \"(R⊗I)(I⊗R)(R⊗I) = (I⊗R)(R⊗I)(I⊗R)\". The symbols prodAssoc, reindex and kronecker denote Equiv.prodAssoc, Matrix.reindex and Matrix.kronecker. Both identity matrices have type Matrix (ZMod d) (ZMod d) Complex. The reindexed first placement and the second placement act on ZMod d × (ZMod d × ZMod d).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("projective-unitarity", "Projective unitarity", "ProjectivelyUnitary", ProjectiveUnitaryFormula(),
                "Projectively unitary means that some nonzero complex scalar multiple of the operator is a member of the Mathlib Matrix.unitaryGroup object. Its matrix index type is ZMod d × ZMod d and its scalar type is Complex.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("pauli-rigidity-claim", "Galindo–Rowell Conjecture 10.6", "claim", ClaimFormula(),
                "Galindo–Rowell, Conjecture 10.6, arXiv:2608.16865v1, p. 43, §10.2.7: \"Let d≥2 with 4∤d, let α∈(Z/dZ)^×, and put P_α=X⊗Z^α, τ_α(s,t)=w^{αst} (s,t∈Z/dZ). Suppose that a=(1,a_1,…,a_{d−1})∈T_d^{coef} and that R_α(a)=∑_{t∈Z/dZ}a_tP_α^t satisfies the Yang--Baxter equation and is projectively unitary. Then a belongs to one of the two signed Gaussian torsors for τ_α: there exists ε∈{+1,−1} such that a_{s+t}=a_sa_tτ_α(s,t)^ε (s,t∈Z/dZ).\" The encoding uses ZMod d, primitive roots in Complex, unit alpha, a 0 = 1, and the unit-modulus phase-torus condition for every index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pauli-rigidity-refuted", "Conjecture 10.6 is refuted", "result", ResultFormula(),
                "At d=15, α=1, and a_t=w^(2t²) for a primitive fifteenth root, the coefficient-to-braid identity and a translation of the finite character sum prove the braid equation. Character orthogonality gives R R†=15·I, hence projective unitarity. At s=t=1 the two signs would require w^8=w^5 or w^8=w^3, both impossible for a primitive fifteenth root.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("galindo-rowell-2026-pauli-rigidity-mixed-sign-refutation"),
                    ResolutionKind.Refuted)
))));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula C() => Seq(Mathbb, Grp(V("C")));
    private static Formula ZMod(Formula d) => Call("ZMod", d);
    private static Formula Units(Formula x) => Call("Units", x);
    private static Formula Matrix(Formula i, Formula j) => Call("Matrix", i, j, C());
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Sp, Times, Sp, y));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula For(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula For(string name, Formula type, Formula instance, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, instance, Comma, Sp, body);
    private static Formula Bracket(Formula type) => Seq(OpenBracket, type, CloseBracket);
    private static Formula EqualFormula(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Not(Formula body) => Seq(Neg, Sp, body);
    private static Formula Pow(Formula baseValue, Formula exponent) =>
        new Formula.Power(baseValue, exponent);

    private static Formula ClockFormula()
    {
        Formula w = V("w"), d = V("d"), j = V("j");
        Formula body = Call("diagonal", Seq(LambdaLower, Sp, j, Colon, Sp, ZMod(d), Sp, Mapsto, Sp,
            Pow(w, Call("val", j))));
        return Disp(For("w", C(), For("d", N(), EqualFormula(Call("clockZ", w, d), body))));
    }

    private static Formula PFormula()
    {
        Formula d = V("d"), w = V("w"), alpha = V("alpha"), zd = ZMod(d);
        Formula body = Call("kronecker", Call("shiftMatrix", d),
            Pow(Call("clockZ", w, d), Call("val", Call("val", alpha))));
        return Disp(For("d", N(), Bracket(Call("NeZero", d)),
            For("w", C(), For("alpha", Units(zd), EqualFormula(Call("P", w, alpha), body)))));
    }

    private static Formula RFormula()
    {
        Formula d = V("d"), w = V("w"), alpha = V("alpha"), a = V("a"), t = V("t");
        Formula zd = ZMod(d);
        Formula sum = Call("sum", Seq(t, InMacro, zd),
            Seq(a, Sp, t, Sp, Cdot, Sp, Pow(Call("P", w, alpha), Call("val", t))));
        return Disp(For("d", N(), Bracket(Call("NeZero", d)),
            For("w", C(), For("alpha", Units(zd),
                For("a", Seq(zd, Sp, To, Sp, C()), EqualFormula(Call("R", w, alpha, a), sum))))));
    }

    private static Formula BraidFormula()
    {
        Formula d = V("d"), r = V("r"), zd = ZMod(d);
        Formula pair = Pair(zd, zd);
        Formula matrix = Matrix(pair, pair);
        Formula assoc = Call("prodAssoc", zd, zd, zd);
        Formula left = Call("reindex", assoc, assoc, Call("kronecker", r, D(1)));
        Formula right = Call("kronecker", D(1), r);
        Formula equation = EqualFormula(Parenthesized(Call("mul", Call("mul", left, right), left)),
            Parenthesized(Call("mul", Call("mul", right, left), right)));
        return Disp(For("d", N(), Bracket(Call("NeZero", d)),
            For("r", matrix, EqualFormula(Call("BraidYBE", r),
                Parenthesized(equation)))));
    }

    private static Formula ProjectiveUnitaryFormula()
    {
        Formula d = V("d"), r = V("r"), zd = ZMod(d), pair = Pair(zd, zd);
        Formula matrix = Matrix(pair, pair), c = V("c");
        Formula body = Seq(Exists, Sp, c, Colon, Sp, C(), Comma, Sp,
            And(Seq(c, Sp, Neq, Sp, D(0)),
                Seq(c, Sp, Cdot, Sp, r, Sp, InMacro, Sp, Call("unitaryGroup", pair, C()))));
        return Disp(For("d", N(), Bracket(Call("NeZero", d)),
            For("r", matrix, EqualFormula(Call("ProjectivelyUnitary", r), Parenthesized(body)))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = V("d"), w = V("w"), alpha = V("alpha"), a = V("a"),
            s = V("s"), t = V("t"), eps = V("eps"), zd = ZMod(d);
        Formula signCondition = Seq(EqualFormula(eps, D(1)), Sp, Lor, Sp,
            EqualFormula(eps, Seq(Minus, D(1))));
        Formula polarization = EqualFormula(Call("a", Seq(s, Sp, Plus, Sp, t)),
            Seq(Call("a", s), Sp, Times, Sp, Call("a", t), Sp, Times, Sp,
                Pow(w, Call("val", Seq(eps, Sp, Times, Sp, Call("val", alpha), Sp, Times, Sp,
                    s, Sp, Times, Sp, t)))));
        Formula sign = And(Parenthesized(signCondition),
            Parenthesized(For("s", zd, For("t", zd, polarization))));
        Formula conclusion = Seq(Exists, Sp, eps, Colon, Sp, zd, Comma, Sp, sign);
        Formula hNorm = For("t", zd, EqualFormula(Call("norm", Call("a", t)), D(1)));
        Formula hUnitary = Call("ProjectivelyUnitary", Call("R", w, alpha, a));
        Formula hBraid = Call("BraidYBE", Call("R", w, alpha, a));
        Formula hA0 = EqualFormula(Call("a", D(0)), D(1));
        Formula hypotheses = Imp(Parenthesized(Seq(D(2), Sp, Leq, Sp, d)),
            Imp(Not(Parenthesized(Seq(D(4), Sp, Mid, Sp, d))),
                For("w", C(),
                    Imp(Call("IsPrimitiveRoot", w, d), For("alpha", Units(zd),
                        For("a", Seq(zd, Sp, To, Sp, C()), Imp(hA0,
                            Imp(Parenthesized(hNorm), Imp(hBraid, Imp(hUnitary, conclusion))))))))));
        return Disp(For("d", N(), hypotheses));
    }

    private static Formula ResultFormula() => Disp(Not(V("claim")));
}
