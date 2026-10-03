using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class SuvagiyaSignedSquareCycleRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/suvagiya2026parity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A signed square-cycle on 32 vertices has radius below the proposed universal optimum.",
        H("Suvagiya Conjecture 28 is false"),
        Blocks(
            Node("independent-signings", "All independent edge signings", "Signing",
                SigningFormula(),
                "The two Boolean functions assign independent signs to the forward edges "
                    + "of lengths one and two. True represents +1 and false represents -1. "
                    + "For n at least five these index each undirected edge exactly once; "
                    + "the carrier includes both Hamilton-cycle sign products.", DescribeRole.Definition),
            Node("edge-sign", "The two edge weights", "edgeSign",
                Disp(All("b", Bool(), Eq(Call("edgeSign", F.Id("b")),
                    Call("if", F.Id("b"), D(1), Seq(Minus, D(1)))))),
                "Each Boolean selects exactly one of the two rational weights.", DescribeRole.Definition),
            Node("forward-edges", "Forward adjacency", "forward", ForwardFormula(),
                "Indices are residues modulo n, represented by Fin n. The first test "
                    + "assigns the step-one sign and the second assigns the step-two sign; "
                    + "every remaining forward entry is zero.", DescribeRole.Definition),
            Node("symmetric-adjacency", "Undirected rational adjacency", "adjacencyRat",
                Disp(All("n", Nat(), All("sigma", Call("Signing", F.Id("n")),
                    Eq(Call("adjacencyRat", F.Id("sigma")),
                        Seq(Call("forward", F.Id("sigma")), Sp, Plus, Sp,
                            Call("transpose", Call("forward", F.Id("sigma")))))))),
                "Adding the transpose places each signed edge in both symmetric positions. "
                    + "At n = 8m with m at least four, the diagonal is zero and there are "
                    + "exactly 2n undirected edges, with four incident edges at each vertex.",
                DescribeRole.Definition),
            Node("real-adjacency", "Real signed adjacency", "adjacency",
                Disp(All("n", Nat(), All("sigma", Call("Signing", F.Id("n")),
                    Eq(Call("adjacency", F.Id("sigma")),
                        Call("map", Call("adjacencyRat", F.Id("sigma")),
                            Call("castHom", Real())))))),
                "The rational entries are cast into the real field. The real matrix "
                    + "is the actual symmetric signed adjacency, with unchanged edge weights.",
                DescribeRole.Definition),
            Node("quartic", "The proposed optimal-radius quartic", "quartic", QuarticFormula(),
                "This is the quartic in Conjecture 28.", DescribeRole.Definition),
            Node("quartic-roots", "Real quartic roots", "quarticRoots",
                Disp(All("x", Real(), IffFormula(
                    Member(F.Id("x"), F.Id("quarticRoots")),
                    Eq(Call("quartic", F.Id("x")), D(0))))),
                "A greatest element of this set is a real root and bounds every real root above.",
                DescribeRole.Definition),
            Node("attained-radii", "Attained maximum absolute spectra", "radiusValues",
                RadiusFormula(),
                "The radius set ranges over the entire finite signing carrier. IsGreatest "
                    + "requires membership in the absolute spectrum as well as an upper bound "
                    + "for every member. Thus these are attained maxima, with no default value "
                    + "for an empty set.", DescribeRole.Definition),
            Node("source-conjecture", "The complete Conjecture 28", "claim", ClaimFormula(),
                "The source asserts the equality for every integer m at least four. "
                    + "IsLeast requires the radius to be attained by some signing and to "
                    + "bound every signing's radius below. Greatest roots are unique, so "
                    + "the per-m existential denotes the same r-star at every m. "
                    + "No periodic or gauge restriction is imposed.", DescribeRole.Definition),
            Node("conjecture-refuted", "A strict counterexample to Conjecture 28", "result",
                Disp(new Formula.Not(F.Id("claim"))),
                "At m = 4, the step-one weights are +1 except a_31 = -1. Repeat "
                    + "(1,1,-1,1,-1,-1,1,-1) for the step-two weights, then set "
                    + "b_30 = -1 and b_31 = +1. The squared adjacency is annihilated by "
                    + "R(y) = y^8-32y^7+416y^6-2816y^5+10568y^4-21632y^3 "
                    + "+22168y^2-9408y+1262. Exact finite Horner identities establish R(A^2) = 0. "
                    + "Every coefficient of R((279/100)^2+z) is positive. Spectral mapping "
                    + "therefore gives absolute eigenvalues at most 279/100; the finite "
                    + "real spectrum attains its maximum. "
                    + "The quartic takes values -6766519/100000000 at 279/100 and 5 at 3. "
                    + "Continuity supplies a root strictly between them. A greatest root "
                    + "therefore exceeds the attained radius of the displayed signing, "
                    + "contradicting the proposed minimum. Theorem 26's upper bound is unaffected; "
                    + "the exact optima and any repaired restrictions remain undetermined.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("suvagiya-conjecture28-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo()
                : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula SigningFormula()
    {
        var n = F.Id("n");
        var signs = Arrow(Call("Fin", n), Bool());
        return Disp(All("n", Nat(), Eq(Call("Signing", n),
            Seq(Paren(signs), Sp, Times, Sp, Paren(signs)))));
    }

    private static Formula ForwardFormula()
    {
        var n = F.Id("n");
        var sigma = F.Id("sigma");
        var i = F.Id("i");
        var j = F.Id("j");
        Formula Step(byte k) => Eq(Call("val", j),
            Call("mod", Seq(Call("val", i), Sp, Plus, Sp, D(k)), n));
        var value = Call("if", Step(1), Call("edgeSign", Seq(Call("fst", sigma), Open, i, Close)),
            Call("if", Step(2), Call("edgeSign", Seq(Call("snd", sigma), Open, i, Close)), D(0)));
        return Disp(All("n", Nat(), All("sigma", Call("Signing", n),
            All("i", Call("Fin", n), All("j", Call("Fin", n),
                Eq(Call("forward", sigma, i, j), value))))));
    }

    private static Formula QuarticFormula()
    {
        var x = F.Id("x");
        return Disp(All("x", Real(), Eq(Call("quartic", x),
            Seq(x, Caret, Grp(D(4)), Sp, Minus, Sp, D(2), Cdot, Sp, x, Caret, Grp(D(3)),
                Sp, Minus, Sp, D(6), Cdot, Sp, x, Caret, Grp(D(2)), Sp, Plus, Sp,
                D(1,2), Cdot, Sp, x, Sp, Minus, Sp, D(4)))));
    }

    private static Formula RadiusFormula()
    {
        var n = F.Id("n");
        var s = F.Id("s");
        var sigma = F.Id("sigma");
        var absoluteSpectrum = Call("image", F.Id("abs"),
            Call("spectrum", Real(), Call("adjacency", sigma)));
        return Disp(All("n", Nat(), All("s", Real(), IffFormula(
            Member(s, Call("radiusValues", n)), Some("sigma", Call("Signing", n),
                Call("IsGreatest", absoluteSpectrum, s))))));
    }

    private static Formula ClaimFormula()
    {
        var m = F.Id("m");
        var r = F.Id("r");
        var n = Seq(D(8), Cdot, Sp, Call("toNat", m));
        return Disp(IffFormula(F.Id("claim"), All("m", Integer(), ImpliesFormula(
            LeFormula(D(4), m), Some("r", Real(), AndFormula(
                Call("IsGreatest", F.Id("quarticRoots"), r),
                Call("IsLeast", Call("radiusValues", n), r)))))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeFormula(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula IffFormula(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.Iff, Paren(b));
    private static Formula ImpliesFormula(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.Implies, Paren(b));
    private static Formula AndFormula(Formula a, Formula b) =>
        new Formula.Logic(Paren(a), FormulaLogicOperator.And, Paren(b));
    private static Formula Paren(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Paren(a), Sp, To, Sp, Paren(b));
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Integer() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Bool() => new Formula.NamedConstant(FormulaIdentifier.Create("Bool"));
}
