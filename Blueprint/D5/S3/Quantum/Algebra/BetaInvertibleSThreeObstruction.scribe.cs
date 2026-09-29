using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class BetaInvertibleSThreeObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/BetaInvertibleSThreeObstruction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/lu2024galitydefects");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "When 3 divides N, no copy of the symmetric group S_3 inside the anyon permutation symmetries of the Z_N x Z_N SymTFT has all of its non-identity elements beta-invertible, as conjectured by D.-C. Lu, Z. Sun and Z. Zhang (arXiv:2406.12151, JHEP 11 (2025) 081); so the Z_N x Z_N theory admits no S_3-ality extension of this kind for such N.",
        H("No beta-invertible S_3 symmetry when 3 divides N"),
        Blocks(
            Node("q", "The quadratic form of the SymTFT", QFormula(),
                "On the anyons (a, a') of the Z_N x Z_N SymTFT, with a in A = (Z/N)^2 the left summand and a' in the dual group identified with (Z/N)^2, Q is the dot product a . a' modulo N; the self-statistics of the anyon is exp(2 pi i Q / N).",
                "Q", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture for N divisible by 3", ClaimFormula(),
                "For every N divisible by 3 there is no group homomorphism rho from S_3, the permutations of three letters, to the invertible 4 x 4 matrices over Z/N such that every rho(g) preserves Q and, for every g other than the identity, the upper-right 2 x 2 block beta of rho(g), the component from the dual group to A, has a unit determinant. A subgroup isomorphic to S_3 whose non-identity elements are all beta-invertible is exactly such a homomorphism, which is then injective.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Reduce rho modulo 3. The reduced matrices still preserve Q, since every vector over Z/3 lifts to Z/N, and still have invertible beta blocks at g other than the identity, since the determinant reduces to a unit. Over Z/3 let S_g = delta_g beta_g^{-1}, where delta_g is the lower-right block. The matrix rho(g) sends (0, x) to (beta_g x, delta_g x), and Q vanishes at (0, x), so y . S_g y = 0 for every y; hence S_g has zero diagonal and opposite off-diagonal entries and is determined by its entry S_g(0, 1). If g and h are different non-identity permutations with S_g = S_h, then rho(h) sends (0, z) to rho(g)(0, x) for z = beta_h^{-1} beta_g x, so rho(h^{-1} g) sends (0, x) to (0, z) for every x and its beta block vanishes, although h^{-1} g is not the identity. So g -> S_g(0, 1) maps the five non-identity permutations injectively into Z/3, which has three elements, a contradiction. The same argument bounds every beta-invertible group by p + 1 for any prime p dividing N.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("s3ality-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ZModN() => Call("ZMod", F.Id("N"));
    private static Formula Index() => Seq(Call("Fin", D(2)), Sp, Plus, Sp, Call("Fin", D(2)));
    private static Formula Vectors() => new Formula.TypeArrow(Index(), ZModN());

    private static Formula QFormula()
    {
        Formula v = F.Id("v");
        Formula Entry(string side, byte i) => new Formula.Apply(v, [Call(side, D(i))]);
        Formula sum = new Formula.Binary(
            new Formula.Binary(Entry("inl", 0), FormulaBinaryOperator.Multiply, Entry("inr", 0)),
            FormulaBinaryOperator.Add,
            new Formula.Binary(Entry("inl", 1), FormulaBinaryOperator.Multiply, Entry("inr", 1)));
        return Disp(All("v", Vectors(), Equal(Call("Q", v), sum)));
    }

    private static Formula ClaimFormula()
    {
        Formula g = F.Id("g"), v = F.Id("v"), rho = F.Id("rho");
        Formula perm = Call("Perm", Call("Fin", D(3)));
        Formula homs = Call("MonoidHom", perm, Call("GL", Index(), ZModN()));
        Formula image = new Formula.Apply(rho, [g]);
        Formula preserves = All("g", perm, All("v", Vectors(),
            Equal(Call("Q", Seq(image, Sp, v)), Call("Q", v))));
        Formula betaInvertible = All("g", perm, Implies(NotEqual(g, D(1)),
            Call("IsUnit", Call("det", new Formula.Apply(new Formula.Subscript(Named("toBlocks"), Seq(D(1), D(2))), [image])))));
        Formula body = Implies(Divides(D(3), F.Id("N")),
            Seq(Neg, Parenthesized(Some("rho", homs, And(preserves, betaInvertible)))));
        return Disp(Iff(F.Id("claim"), All("N", Naturals(), body)));
    }
}
