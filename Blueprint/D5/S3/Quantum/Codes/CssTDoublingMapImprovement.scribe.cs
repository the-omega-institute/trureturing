using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class CssTDoublingMapImprovementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Codes/CssTDoublingMapImprovement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/berardini2025csst");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary cyclic map gives an admissible CSS-T extension with distance at least five, while identity doubling has distance at most four.",
        H("A strict distance improvement for CSS-T doubling"),
        Blocks(
            Node("cssDistance", "The two CSS distance legs", DistanceFormula(),
                "Theorem 1 defines CSS distance using the weights in C₁ outside C₂ and in C₂⊥ outside C₁⊥. Here wt is Hamming weight, orthogonality uses the binary dot product, and the infimum is taken in the natural numbers over the union of these two sets of weights. Thus the formula also specifies the empty-set convention sInf ∅ = 0 and does not assume C₂ ⊆ C₁. The index type I is any finite type.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("extension", "The graph extension", ExtensionFormula(),
                "Definition 3 writes C^{Nφ} = {(x, φ(x)) : x ∈ C}. For C ⊆ C₁, the map φ is linear on C₁ and is restricted to C through the inclusion determined by h. In the formula, inclusion(h) maps C to C₁ and val is the underlying vector. A pair of vectors denotes the corresponding function on Fin(n) ⊕ Fin(n), so the extension is a binary linear code of length 2n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("admissible", "Triple-product parity", AdmissibleFormula(),
                "Proposition 1 requires the sum of the two triple-product weights to be even for every x,y ∈ C₁ and z ∈ C₂. Over the binary field, this is exactly the displayed equality to zero of the two coordinate sums. The linearity of φ is part of its type. The inclusion determined by h supplies the argument of φ when z belongs to C₂.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "A map with better distance than identity", Disp(IffF(Named("claim"), ClaimBody())),
                "Remark 1 asks for maps φ giving better parameters than the identity or a permutation. The existential statement asks for a nested binary code pair of positive dimension difference and an admissible linear map whose extension has strictly greater CSS distance than identity doubling of that same pair. The first argument of cssDistance is the smaller code. Here leRefl(C₁) is the reflexive inclusion C₁ ⊆ C₁, and subtype(C₁) is the inclusion into the ambient vector space, which gives the identity choice of φ. Both extensions have length 2n and dimension dim C₁ − dim C₂.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A cyclic length-thirteen construction", Disp(ClaimBody()),
                "Write vectors of length 26 as two blocks over 𝔽₂¹³. Take C₁ = {(x,x) : x ∈ 𝔽₂¹³} and C₂ = {(x,x) : Σᵢ xᵢ = 0}. Their dimensions are 13 and 12. Let (Ax)ᵢ = xᵢ + xᵢ₊₁ + xᵢ₊₂, with indices modulo 13, and set φ(x,x) = (Ax,Ax). Every vector of C₁ and of φ(C₁) has two equal blocks, so each triple product has even weight and the admissibility condition holds. Identity doubling sends (x,x) to (x,x,x,x). Taking x to be a coordinate unit vector gives a vector outside the smaller extension of weight 4, hence identity distance at most 4. For the φ-extension a nontrivial X vector is (x,x,Ax,Ax) with Σᵢ xᵢ = 1, of weight 2(wt(x) + wt(Ax)). If wt(x) = 1, then wt(Ax) = 3. Otherwise wt(x) ≥ 3 and Ax ≠ 0: Ax = 0 would imply xᵢ₊₃ = xᵢ, hence x is constant because 3 is coprime to 13, and then x = 0. Thus the X-distance is at least 8. For a nontrivial Z vector (a,b,c,d), orthogonality to the smaller extension and failure of orthogonality to the larger one give a + b + Aᵀ(c + d) = 𝟙. Put w = c + d and j = wt(w). Its total weight is at least wt(w) + wt(𝟙 + Aᵀw) = j + 13 − wt(Aᵀw). The transpose is a sum of three coordinate permutations, so wt(Aᵀw) ≤ 3 wt(w). If j ≤ 4 the total weight is at least 13 − 2j ≥ 5; if j ≥ 5 it is already at least 5. Consequently the new distance is at least 5, strictly greater than the identity bound 4, at length 52 and encoded dimension 1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("berardini-et-al-2024-csst-doubling-map-improvement"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("csst-doubling-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Ex(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula AndF(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffF(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula EqualF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LeF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula AddF(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula MulF(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula NatType() => Seq(Mathbb, Grp(X("N")));
    private static Formula Field() => new Formula.Subscript(Seq(Mathbb, Grp(X("F"))), D(2));
    private static Formula FinType() => Call("Fin", X("n"));
    private static Formula Vectors(Formula index) => new Formula.TypeArrow(index, Field());
    private static Formula Codes(Formula index) => Call("Submodule", Field(), Parenthesized(Vectors(index)));
    private static Formula C(int index) => new Formula.Subscript(X("C"), index == 1 ? D(1) : D(2));
    private static Formula LinearMaps() => Call("LinearMap", Field(), C(1), Parenthesized(Vectors(FinType())));
    private static Formula Orthogonal(Formula code) => new Formula.Power(code, Perp);
    private static Formula Extended(Formula inclusion, Formula map) => Call("extension", inclusion, map);
    private static Formula Refl() => Call("leRefl", C(1));
    private static Formula IntoUpper(Formula value) => App(Call("inclusion", X("h")), value);

    private static Formula WeightSet(Formula upper, Formula lower)
    {
        Formula body = Ex(X("x"), Vectors(X("I")), AndF(Member(X("x"), upper),
            AndF(new Formula.Not(Parenthesized(Member(X("x"), lower))),
                EqualF(Call("hammingNorm", X("x")), X("d")))));
        return Seq(OpenBrace, X("d"), Colon, Sp, NatType(), Sp, Mid, Sp, body, CloseBrace);
    }

    private static Formula DistanceFormula()
    {
        Formula weights = Seq(WeightSet(C(1), C(2)), Sp, Cup, Sp,
            WeightSet(Orthogonal(C(2)), Orthogonal(C(1))));
        Formula body = All(C(2), Codes(X("I")), All(C(1), Codes(X("I")),
            EqualF(Call("cssDistance", C(2), C(1)), Call("sInf", Parenthesized(weights)))));
        return Disp(All(X("I"), Named("Type"), Seq(OpenBracket, Call("Fintype", X("I")), CloseBracket, Sp, body)));
    }

    private static Formula ExtensionFormula()
    {
        Formula pair = Parenthesized(Seq(Call("val", X("x")), Comma, Sp, App(Varphi, IntoUpper(X("x")))));
        Formula graph = Seq(OpenBrace, pair, Sp, Mid, Sp, X("x"), Colon, Sp, X("C"), CloseBrace);
        Formula notation = new Formula.Power(X("C"), new Formula.Subscript(X("N"), Varphi));
        Formula equation = new Formula.RelationChain(FormulaRelationOperator.Equal,
            [Extended(X("h"), Varphi), notation, graph]);
        return Disp(All(X("n"), NatType(), All(X("C"), Codes(FinType()), All(C(1), Codes(FinType()),
            All(X("h"), LeF(X("C"), C(1)), All(Varphi, LinearMaps(), equation))))));
    }

    private static Formula TripleSum(bool mapped)
    {
        Formula At(Formula value) => App(mapped ? App(Varphi, value) : Call("val", value), X("i"));
        Formula z = mapped ? IntoUpper(X("z")) : X("z");
        Formula summand = MulF(MulF(At(X("x")), At(X("y"))), At(z));
        return Seq(new Formula.Subscript(Sum, Seq(X("i"), Colon, Sp, FinType())), Parenthesized(summand));
    }

    private static Formula AdmissibleFormula()
    {
        Formula parity = All(X("x"), C(1), All(X("y"), C(1), All(X("z"), C(2),
            EqualF(AddF(Parenthesized(TripleSum(false)), Parenthesized(TripleSum(true))), D(0)))));
        Formula body = IffF(Call("admissible", C(2), C(1), X("h"), Varphi), parity);
        return Disp(All(X("n"), NatType(), All(C(2), Codes(FinType()), All(C(1), Codes(FinType()),
            All(X("h"), LeF(C(2), C(1)), All(Varphi, LinearMaps(), body))))));
    }

    private static Formula ClaimBody()
    {
        Formula rank = new Formula.Relation(Call("finrank", Field(), C(2)),
            FormulaRelationOperator.LessThan, Call("finrank", Field(), C(1)));
        Formula identity = Call("subtype", C(1));
        Formula comparison = new Formula.Relation(
            Call("cssDistance", Extended(X("h"), Varphi), Extended(Refl(), Varphi)),
            FormulaRelationOperator.GreaterThan,
            Call("cssDistance", Extended(X("h"), identity), Extended(Refl(), identity)));
        Formula map = Ex(Varphi, LinearMaps(),
            AndF(Call("admissible", C(2), C(1), X("h"), Varphi), comparison));
        return Ex(X("n"), NatType(), Ex(C(2), Codes(FinType()), Ex(C(1), Codes(FinType()),
            Ex(X("h"), LeF(C(2), C(1)), AndF(rank, map)))));
    }
}
