using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class WoldDecompositionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/atlas2026wold");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite wandering decompositions and the actual residual isometry for arbitrary real or complex inner product spaces.",
        H("Finite Wold decomposition and residual equivalence"),
        Blocks(
            Entry("wandering-subspace", "wanderingSub", Context(false, Eqn(Call("W", V("V")), Call("Orthogonal", Call("Range", V("V"))))),
                "W(V) is wanderingSub V, the orthogonal complement of the linear range of V. Scalar and space universes are independent. No completeness is needed for this definition.", DescribeRole.Definition),
            Entry("finite-wandering-decomposition", "exists_wold_decomposition", Context(true,
                All("x", V("H"), All("n", V("Nat"), Some("w", Arrow(V("Nat"), V("H")), Some("y", V("H"),
                    And(All("j", V("Nat"), Member(Call("w", V("j")), Call("W", V("V")))),
                        And(All("j", V("Nat"), Imp(Le(V("n"), V("j")), Eqn(Call("w", V("j")), D(0)))), Reconstruction()))))))),
                "For every x and every natural n, including zero, a single family w and remainder y realize all clauses together. Every w j lies in W(V), w j vanishes for j >= n, and x is the sum over j in Finset.range n of (V^j)(w j), plus (V^n)y. SumRange(n,f) denotes that finite sum; PowerApply(V,j,z) denotes (V^j)z. Completeness gives the orthogonal range splitting. The source induction splits the old remainder and updates its coefficient family at n. No separability, finite dimension or ambient surjectivity is required."),
            Entry("finite-pythagorean-identity", "wold_norm_sq", Context(false,
                All("n", V("Nat"), All("w", Arrow(V("Nat"), V("H")),
                    All("hw", All("j", V("Nat"), Member(Call("w", V("j")), Call("W", V("V")))),
                        All("y", V("H"), All("x", V("H"), Imp(Reconstruction(),
                            Eqn(SqNorm(V("x")), Add(Call("SumRange", V("n"), Call("NormSquareFamily", V("w"))), SqNorm(V("y"))))))))))),
                "For any n, family w with every coefficient in W(V), y and x satisfying exactly the reconstruction equation, norm(x)^2 equals the sum over j in Finset.range n of norm(w j)^2 plus norm(y)^2. NormSquareFamily(w) is j mapped to norm(w j)^2. This theorem needs neither completeness nor the support condition. It applies to the SAME w and y supplied by exists_wold_decomposition. The source norm induction groups the terminal wandering coefficient with V y and uses orthogonality and isometry."),
            Entry("residual-subspace", "residualSub", Context(false, Eqn(Call("R", V("V")), Call("InfPowerRanges", V("V")))),
                "R(V) is residualSub V, the infimum over all natural m of the linear range of V^m. Membership means membership in every actual power range. No closure or completeness assumption is added.", DescribeRole.Definition),
            Entry("actual-residual-equivalence", "woldResidualEquiv", Context(false,
                And(Call("LinearIsometricEquiv", Call("U", V("V")), Call("R", V("V")), Call("R", V("V"))),
                    All("z", Call("R", V("V")), Eqn(Call("Coe", Call("U", V("V"), V("z"))), Call("V", Call("Coe", V("z"))))))),
                "U(V) is woldResidualEquiv V, a linear isometric equivalence R(V) to itself over k. Its forward function is literally the linear restriction of V, so after subtype coercion U(V)z = Vz for every z. Invariance shifts the power-range witnesses. For surjectivity take a V-preimage of a residual point; injectivity of V and the next power-range witness put that preimage in every power range. The equivalence packages this bijection and preservation of inner products. Completeness is absent from its full telescope. These finite and residual statements give no infinite direct-sum or coefficientwise uniqueness theorem.", DescribeRole.Definition))));

    private static DocumentBlock Entry(string id, string decl, Formula statement, string explanation, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/HilbertOperators/WoldDecomposition." + decl),
            H(decl), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(explanation))), role);
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] xs)
    {
        var a = new List<Formula> { Operatorname, Grp(V(n)), Open };
        for (int i = 0; i < xs.Length; i++) { if (i > 0) a.AddRange([Comma, Sp]); a.Add(xs[i]); }
        a.Add(Close); return Seq([.. a]);
    }
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Par(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, Par(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Rightarrow, Sp, Par(b));
    private static Formula Add(Formula a, Formula b) => Seq(Par(a), Plus, Par(b));
    private static Formula SqNorm(Formula a) => Call("NormSquare", a);
    private static Formula Reconstruction() => Eqn(V("x"), Add(Call("SumRange", V("n"), Call("PowerWanderingFamily", V("V"), V("w"))), Call("PowerApply", V("V"), V("n"), V("y"))));
    private static Formula Context(bool complete, Formula b)
    {
        var instances = new List<Formula> { Call("NormedAddCommGroup", V("H")), Call("InnerProductSpace", V("k"), V("H")) };
        if (complete) instances.Add(Call("CompleteSpace", V("H")));
        Formula result = All("V", Call("LinearIsometry", V("k"), V("H"), V("H")), b);
        for (int i = instances.Count - 1; i >= 0; i--) result = Seq(OpenBracket, instances[i], CloseBracket, Sp, result);
        return All("k", Seq(V("Type"), Star), Seq(OpenBracket, Call("RCLike", V("k")), CloseBracket, Sp,
            All("H", Seq(V("Type"), Star), result)));
    }
}
