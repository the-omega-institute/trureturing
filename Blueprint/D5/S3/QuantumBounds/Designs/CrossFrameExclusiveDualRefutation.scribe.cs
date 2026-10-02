using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.Designs;

internal sealed class CrossFrameExclusiveDualRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/Designs/CrossFrameExclusiveDualRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/aceska2022crossframe");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A frame can have a unique dual minimizing the off-diagonal cross-Gramian magnitude without that dual being canonical.",
        H("An exclusive Grassmannian dual need not be canonical"),
        Blocks(
            Node("frame", "Finite real frame", FrameFormula(), "IsFrame",
                "Definition 1 (p. 3): A sequence of vectors F = {f_i}_{i=1}^k, with k ≥ n, in an n-dimensional Hilbert space H is a frame for H if there exist real constants 0 < A ≤ B < +∞ such that A‖f‖² ≤ ∑_{i=1}^k |⟨f, f_i⟩|² ≤ B‖f‖² for every f ∈ H. The separate hypothesis n <= k imposes the source's size condition; EuclideanSpace over the reals realizes its real Hilbert space. Indices run from 0 through k - 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dual", "Dual reconstruction", DualFormula(), "IsDualFrame",
                "Definition 3 (p. 3): Let {f_i}_{i=1}^k be a frame for H. A dual frame for {f_i}_{i=1}^k is a frame {g_i}_{i=1}^k such that for every f ∈ H, f = ∑_{i=1}^k ⟨f, g_i⟩f_i = ∑_{i=1}^k ⟨f, f_i⟩g_i. IsDualFrame records the first operator identity. Over the reals, its transpose gives the second; reconstruction also makes both finite families span the space, so they are frames.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mu", "Off-diagonal magnitude", MuFormula(), "mu",
                "Section 4 (p. 12) defines: µ(Gr(F, H)) := max_{i≠j} |⟨f_i, h_j⟩|. The finite supremum is taken in the nonnegative reals and val denotes its coercion to the reals. An empty off-diagonal set has supremum zero. For a real scalar the nonnegative norm is its absolute value.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("operator", "Frame operator", OperatorFormula(), "frameOperator",
                "Page 3 states: The frame operator of F = {f_i}_{i=1}^k is defined as S = θ_F* θ_F. Its action is the displayed reconstruction sum with F in both places.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("canonical", "Canonical dual", CanonicalFormula(), "canonicalDual",
                "Page 4 states: The canonical dual frame for a frame F = {f_i}_{i=1}^k for H with frame operator S is the frame F̃ = {S^{-1} f_i}_{i=1}^k. Mathlib's invFun is the inverse function of frameOperator; for a frame its positive lower bound makes this operator invertible in finite dimension.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 42", ClaimFormula(), "claim",
                "Conjecture 42 (Section 4.2, p. 17): If a frame F for F^n forms an exclusive Grassmannian pair with one of its duals, then that dual must be the canonical dual frame of F. Definition 34 (p. 13): A frame F for F^n forms a Grassmannian pair with its dual frame F̃ if µ(Gr(F, F̃)) = min{µ(Gr(F, H)) | H is a dual frame of F}. (14) The following sentence (p. 14) reads: Some frames form an exclusive Grassmannian pair with their canonical dual (Example 32), while other frames (Example 31) have more than one dual frame which satisfy (14). Section 4.2 (p. 17) further specifies that the canonical dual in Example 32 is the only dual frame that satisfies (14). The encoding quantifies over all dimensions, sizes and real finite families. The first universal condition says G minimizes the magnitude over every dual H; the second says any dual H with no greater magnitude equals G. A real counterexample suffices to disprove the assertion for real or complex Hilbert spaces.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A noncanonical unique minimizer", Disp(new Formula.Not(Call("claim"))), "result",
                "Take n = 1, k = 3 and F = (3, 2, 1). Its frame bound is 14 and its duals satisfy 3 h_0 + 2 h_1 + h_2 = 1. The off-diagonal bounds imply 2 |h_0| <= mu(F,H), 3 |h_1| <= mu(F,H) and 3 |h_2| <= mu(F,H). Hence 1 <= (5/2) mu(F,H). The dual G = (1/5, 2/15, 2/15) attains mu(F,G) = 2/5. If a dual has magnitude at most 2/5, the reconstruction identity and the three coordinate upper bounds force each coordinate to equal the corresponding coordinate of G. Thus G is the unique minimizer. The frame operator is multiplication by 14, so its canonical dual has first coordinate 3/14, different from 1/5.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string name,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("cross-frame-exclusive-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name)))
            : new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsVar(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula EqTo(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula LeTo(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula AndAlso(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinOf(Formula k) => Call("Fin", k);
    private static Formula Space(Formula n) => Call("EuclideanSpace", Reals(), FinOf(n));
    private static Formula Family(Formula n, Formula k) => Seq(FinOf(k), Sp, To, Sp, Space(n));
    private static Formula Inner(Formula x, Formula y) => Seq(Langle, Sp, x, Comma, Sp, y, Sp, Rangle);
    private static Formula SumI(Formula k, Formula body) => Seq(new Formula.Subscript(Sum,
        Seq(F.Id("i"), Colon, Sp, FinOf(k))), Sp, body);
    private static Formula Dimensions(Formula body) => All("n", Nats(), All("k", Nats(), body));
    private static Formula FamilyF(Formula body) => All("F", Family(F.Id("n"), F.Id("k")), body);
    private static Formula Families(Formula body) => FamilyF(All("G", Family(F.Id("n"), F.Id("k")), body));

    private static Formula FrameFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), f = F.Id("F"), x = F.Id("x");
        Formula a = F.Id("A"), b = F.Id("B");
        Formula energy = SumI(k, new Formula.Power(new Formula.Absolute(Inner(x, Apply(f, F.Id("i")))), D(2)));
        Formula normSq = new Formula.Power(new Formula.Norm(x), D(2));
        Formula bounds = AndAlso(Rel(D(0), FormulaRelationOperator.LessThan, a),
            AndAlso(LeTo(a, b), All("x", Space(n), AndAlso(LeTo(Mul(a, normSq), energy), LeTo(energy, Mul(b, normSq))))));
        return Disp(Dimensions(FamilyF(IffTo(Call("IsFrame", f),
            ExistsVar("A", Reals(), ExistsVar("B", Reals(), bounds))))));
    }

    private static Formula DualFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), f = F.Id("F"), g = F.Id("G"), x = F.Id("x"), i = F.Id("i");
        return Disp(Dimensions(Families(IffTo(Call("IsDualFrame", f, g), All("x", Space(n),
            EqTo(SumI(k, Seq(Inner(x, Apply(g, i)), Sp, Cdot, Sp, Apply(f, i))), x))))));
    }

    private static Formula MuFormula()
    {
        Formula k = F.Id("k"), f = F.Id("F"), g = F.Id("G"), i = F.Id("i"), j = F.Id("j");
        Formula indices = Seq(i, Comma, Sp, j, Colon, Sp, FinOf(k), Comma, Sp,
            Rel(i, FormulaRelationOperator.NotEqual, j));
        Formula nnNorm = new Formula.Subscript(new Formula.Norm(Inner(Apply(f, i), Apply(g, j))), Plus);
        Formula maximum = Seq(new Formula.Subscript(Max, indices), Sp, nnNorm);
        return Disp(Dimensions(Families(EqTo(new Formula.Apply(Mu, [f, g]), Call("val", maximum)))));
    }

    private static Formula OperatorFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), f = F.Id("F"), x = F.Id("x"), i = F.Id("i");
        return Disp(Dimensions(FamilyF(All("x", Space(n), EqTo(Call("frameOperator", f, x),
            SumI(k, Seq(Inner(x, Apply(f, i)), Sp, Cdot, Sp, Apply(f, i))))))));
    }

    private static Formula CanonicalFormula()
    {
        Formula k = F.Id("k"), f = F.Id("F"), i = F.Id("i");
        return Disp(Dimensions(FamilyF(All("i", FinOf(k), EqTo(Call("canonicalDual", f, i),
            Apply(Call("invFun", Call("frameOperator", f)), Apply(f, i)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), f = F.Id("F"), g = F.Id("G"), h = F.Id("H");
        Formula fg = new Formula.Apply(Mu, [f, g]), fh = new Formula.Apply(Mu, [f, h]);
        Formula minimum = All("H", Family(n, k), Imp(Call("IsDualFrame", f, h), LeTo(fg, fh)));
        Formula unique = All("H", Family(n, k), Imp(Call("IsDualFrame", f, h), Imp(LeTo(fh, fg), EqTo(h, g))));
        Formula body = Dimensions(Families(Imp(LeTo(n, k), Imp(Call("IsFrame", f),
            Imp(Call("IsDualFrame", f, g), Imp(minimum, Imp(unique, EqTo(g, Call("canonicalDual", f)))))))));
        return Disp(IffTo(Call("claim"), body));
    }
}
