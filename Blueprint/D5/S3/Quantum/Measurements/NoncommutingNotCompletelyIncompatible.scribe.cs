using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class NoncommutingNotCompletelyIncompatibleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurements/NoncommutingNotCompletelyIncompatible.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/debievre2023incompatibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In every complex dimension d ≥ 4, two orthonormal bases can have noncommuting coordinate projectors for every pair of nonempty proper index sets while failing complete incompatibility.",
        H("Noncommutativity does not imply complete incompatibility"),
        Blocks(
            Node("projector", "Coordinate orthogonal projectors", ProjectorFormula(),
                "Section 3, p. 5: “Given bases 𝒜 and ℬ, we introduce a family of orthogonal projectors as follows. For every S,T ⊂ ⟦1,d⟧ := {1,2,...,d},” followed by Π_𝒜(S) = ∑_{i∈S} |a_i⟩⟨a_i| and Π_ℬ(T) = ∑_{j∈T} |b_j⟩⟨b_j|. The displayed matrix entry is exactly this sum of rank-one projectors. star is complex conjugation; b(k)(i) is the i-th coordinate of the k-th basis vector.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("NonCommutingProjectors", "Condition (ii)", NoncommutingFormula(),
                "Proposition 7(ii), p. 16: “For all S,T ⊂ ⟦1,d⟧, with 1 ≤ |S|, |T| < d, [Π_𝒜(S),Π_ℬ(T)] ≠ 0.” Nonempty proper finite subsets express precisely the two cardinality bounds. The two products are complex matrix products, so their inequality expresses a nonzero operator commutator.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("CompletelyIncompatible", "Condition (i): complete incompatibility", CoincFormula(),
                "Definition 4, p. 14: “We say that two bases 𝒜 and ℬ are completely incompatible (COINC) if and only if all index sets S,T in ⟦1,d⟧ for which |S|+|T|≤d have the property that Π_𝒜(S)ℋ∩Π_ℬ(T)ℋ={0}.” The image of each coordinate projector is the complex span of the indicated basis vectors. coe denotes SetLike.coe from Finset (Fin d) to Set (Fin d); image is set image; inf is intersection of complex submodules; bot is the zero submodule. Empty index sets remain in scope.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "De Bièvre's conjecture", ClaimFormula(),
                "Section 5, p. 16: “We conjecture it is true that (ii) does not imply (i) in all dimensions d ≥ 4, but we have not produced such examples in other dimensions than 4 and 6.” Thus for each natural dimension at least four there exist two arbitrary orthonormal bases satisfying condition (ii) and failing condition (i).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture holds in every dimension at least four", Disp(F.Id("claim")),
                "Take the standard basis and the columns of H = I − (2/q)wwᵀ, where w = (1,2,...,2) and q = 4d−3. This real Householder reflection is unitary over the complex space. For a nonempty proper set T let m = ∑_{k∈T} w_k², so 0 < m < q. Every off-diagonal entry of its coordinate projector equals (2w_iw_j/q²)(2m−q(1_T(i)+1_T(j))). The last factor is nonzero: indicator sums zero and two use the strict mass bounds, and indicator sum one uses the oddness of q. A coordinate inside S and one outside S then give a nonzero commutator entry for every nonempty proper S. Finally 2e₀−e₁ is nonzero and equals 2He₀−He₁, so it lies in both two-coordinate spans for S = T = {0,1}. Their total cardinality is four, which is at most d.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("noncommuting-not-coinc-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula SpaceType(Formula d) => Call("EuclideanSpace", Complexes(), Fin(d));
    private static Formula Basis(Formula d) => Call("OrthonormalBasis", Fin(d), Complexes(), SpaceType(d));
    private static Formula Sets(Formula d) => Call("Finset", Fin(d));

    private static Formula ProjectorFormula()
    {
        Formula d = F.Id("d"), b = F.Id("b"), s = F.Id("S"),
            i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula term = Mul(new Formula.Apply(new Formula.Apply(b, [k]), [i]),
            Call("star", new Formula.Apply(new Formula.Apply(b, [k]), [j])));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Rel(k, FormulaRelationOperator.MemberOf, s)), Sp, term);
        return Disp(All("d", Nats(), All("b", Basis(d), All("S", Sets(d),
            All("i", Fin(d), All("j", Fin(d), Equal(Call("projector", b, s, i, j), sum)))))));
    }

    private static Formula NoncommutingFormula()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), s = F.Id("S"), t = F.Id("T");
        Formula pa = Call("projector", a, s), pb = Call("projector", b, t);
        Formula body = Rel(Mul(pa, pb), FormulaRelationOperator.NotEqual, Mul(pb, pa));
        body = Implies(Rel(t, FormulaRelationOperator.NotEqual, Call("univ", Fin(d))), body);
        body = Implies(Call("Nonempty", t), body);
        body = Implies(Rel(s, FormulaRelationOperator.NotEqual, Call("univ", Fin(d))), body);
        body = Implies(Call("Nonempty", s), body);
        return Disp(All("d", Nats(), All("a", Basis(d), All("b", Basis(d),
            Iff(Call("NonCommutingProjectors", a, b), All("S", Sets(d), All("T", Sets(d), body)))))));
    }

    private static Formula CoincFormula()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b"), s = F.Id("S"), t = F.Id("T");
        Formula sa = Call("span", Complexes(), Call("image", a, Call("coe", s)));
        Formula sb = Call("span", Complexes(), Call("image", b, Call("coe", t)));
        Formula size = new Formula.Binary(Call("card", s), FormulaBinaryOperator.Add, Call("card", t));
        Formula body = Implies(Rel(size, FormulaRelationOperator.LessThanOrEqual, d),
            Equal(Call("inf", sa, sb), Call("bot", Complexes(), SpaceType(d))));
        return Disp(All("d", Nats(), All("a", Basis(d), All("b", Basis(d),
            Iff(Call("CompletelyIncompatible", a, b), All("S", Sets(d), All("T", Sets(d), body)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), a = F.Id("a"), b = F.Id("b");
        Formula body = Some("a", Basis(d), Some("b", Basis(d),
            And(Call("NonCommutingProjectors", a, b),
                Seq(Neg, Parenthesized(Call("CompletelyIncompatible", a, b))))));
        return Disp(Iff(F.Id("claim"), All("d", Nats(),
            Implies(Rel(D(4), FormulaRelationOperator.LessThanOrEqual, d), body))));
    }
}
