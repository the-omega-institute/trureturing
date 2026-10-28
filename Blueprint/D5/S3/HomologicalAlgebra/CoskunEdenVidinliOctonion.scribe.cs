using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class CoskunEdenVidinliOctonionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/CoskunEdenVidinliOctonion.";
    private const string OctonionOwner = "D5.S3.VertexAlgebra.MonsterTwistedOctonionNorm";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/coskuneden2025vidinli");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exceptional seven-dimensional Vidinli product is not a linear push-forward of octonion multiplication.",
        H("No octonion push-forward for the exceptional Vidinli algebra"),
        Blocks(
            Node("vidinliMul", "The exceptional Vidinli product", ProductFormula(),
                "Definition 5.1 and its coordinate expression, pp. 19–20: “a ⊻₇ b = c₁e₁ + ∑_{i=2}^{7} cᵢeᵢ, where c₁ = a₁b₁ − ∑_{i=2}^{7} aᵢbᵢ + (a₂b₃ − a₃b₂) + (a₄b₅ − a₅b₄) + (a₆b₇ − a₇b₆), cᵢ = a₁bᵢ + b₁aᵢ for i = 2, …, 7.” The coordinate i : Fin 7 represents the paper's coordinate i + 1. Finset.Ioi (0 : Fin 7) consists of indices 1 through 6.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The octonion clause of Remark 5.9", Disp(Equal(
                    Parenthesized(Seq(Named("claim"), Colon, Sp, Named("Prop"))),
                    Parenthesized(ClaimBody()))),
                "Remark 5.9, p. 23: “By [5, Proposition 9], see also Section 3.1, the Vidinli multiplication in dimension three arises as a push-forward of quaternion multiplication. Whether a similar push-forward description exists for the exceptional Vidinli algebra V₇ in terms of the octonions, or more generally for V_{2^k−1} in relation to higher Cayley-Dickson algebras, remains an open question.” The proposition expresses the affirmative answer to the octonion clause: there are real-linear maps ν and π satisfying the product identity for every pair a, b. The octonions and their multiplication are the eight-coordinate signed Cayley–Dickson model MonsterTwistedOctonionNorm.Octonion and MonsterTwistedOctonionNorm.mul. Neither map is assumed to preserve products.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "The octonion clause has a negative answer",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "The right unit forces ν to be injective and π to be surjective. Rank-nullity gives a one-dimensional kernel for π. Left multiplication by the nonzero octonion ν(e₂) is injective by the multiplicative positive-definite square norm. The vectors e₂ + e₃, e₄, e₅, e₆, e₇ are independent and are killed by left multiplication by e₂ in the Vidinli algebra. Their images would therefore embed a five-dimensional real vector space into ker π, contradicting rank-nullity. Here e₂ in the paper is Pi.single 1 1 in the zero-based coordinates. The statement concerns arbitrary real-linear maps. It does not address the higher Cayley–Dickson clause, where zero divisors prevent this injectivity argument.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("coskun-eden-2025-vidinli-octonion-pushforward"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("vidinli-octonion-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Coordinates() => new Formula.TypeArrow(Call("Fin", D(7)), Reals());
    private static Formula Linear(Formula domain, Formula codomain) =>
        Seq(Parenthesized(domain), Sp, new Formula.Subscript(To, F.Id("l")),
            OpenBracket, Reals(), CloseBracket, Sp, Parenthesized(codomain));

    private static Formula ClaimBody()
    {
        Formula nu = Nu, pi = Pi, a = F.Id("a"), b = F.Id("b");
        Formula octonion = Named(OctonionOwner + ".Octonion");
        return Some(nu, Linear(Coordinates(), octonion),
            Some(pi, Linear(octonion, Coordinates()),
                All(a, Coordinates(), All(b, Coordinates(),
                    Equal(Call("vidinliMul", a, b),
                        App(pi, Call(OctonionOwner + ".mul", App(nu, a), App(nu, b))))))));
    }

    private static Formula ProductFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), i = F.Id("i"), j = F.Id("j");
        Formula CoordinateProduct(Formula index) => Multiply(App(a, index), App(b, index));
        Formula Alternating(byte x, byte y) => Parenthesized(Subtract(
            Multiply(App(a, D(x)), App(b, D(y))), Multiply(App(a, D(y)), App(b, D(x)))));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Seq(j, Sp, InMacro, Sp, Call("Finset.Ioi",
                Parenthesized(Seq(D(0), Colon, Sp, Call("Fin", D(7))))))), Sp,
            Parenthesized(CoordinateProduct(j)));
        Formula scalar = Add(Add(Add(Subtract(CoordinateProduct(D(0)), sum),
            Alternating(1, 2)), Alternating(3, 4)), Alternating(5, 6));
        Formula other = Add(Multiply(App(a, D(0)), App(b, i)), Multiply(App(b, D(0)), App(a, i)));
        Formula body = Parenthesized(Seq(LambdaLower, Sp, i, Colon, Sp, Call("Fin", D(7)), Sp,
            Mapsto, Sp, Call("ite", Equal(i, D(0)), scalar, other)));
        return Disp(All(a, Coordinates(), All(b, Coordinates(),
            Equal(Call("vidinliMul", a, b), body))));
    }
}
