using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GraphDensity;

internal sealed class BraunsteinGhoshSeveriniStarRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Entanglement/GraphDensity/BraunsteinGhoshSeveriniStarRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refutation of the Braunstein\u2013Ghosh\u2013Severini star maximum conjecture.",
        H("BraunsteinGhoshSeveriniStarRefutation"),
        Blocks(
            Paragraph(Text("Scalar quotients are real unless a complex cast is displayed. Fin indices are zero based. Matrix, rankOneDensity, partialTraceRight and partialTransposeB denote the actual Lean operations. All entropy values are in bits.")),
            Describe.Lean(DescribeId.Create("degreesum"),
                DeclarationHandle.Create(Module + "degreeSum"), H("degreeSum"),
                StatementSource.FromAuthor(Disp(All(F.Id("p"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("q"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("G"), Call("SimpleGraph", Seq(Parenthesized(Call("Fin", F.Id("p"))), Times, Sp, Parenthesized(Call("Fin", F.Id("q"))))), Seq(Call("degreeSum", F.Id("G")), Eq, SumOver(F.Id("v"), Seq(Parenthesized(Call("Fin", F.Id("p"))), Times, Sp, Parenthesized(Call("Fin", F.Id("q")))), Apply(Seq(F.Id("G"), Dot, Seq(Operatorname, Grp(F.Id("degree")))), F.Id("v"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("Page 2 defines dG = ∑ᵢ₌₁ⁿ dG(vi). The sum is over Fin p × Fin q."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sigma"),
                DeclarationHandle.Create(Module + "sigma"), H("sigma"),
                StatementSource.FromAuthor(Disp(All(F.Id("p"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("q"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("G"), Call("SimpleGraph", Seq(Parenthesized(Call("Fin", F.Id("p"))), Times, Sp, Parenthesized(Call("Fin", F.Id("q"))))), Seq(Call("sigma", F.Id("G")), Eq, Seq(Parenthesized(Seq(new Formula.Fraction(D(1), Seq(Call("degreeSum", F.Id("G")), Colon, Seq(Mathbb, Sp, F.Id("R")))), Colon, Seq(Mathbb, Sp, F.Id("C")))), Cdot, Sp, Apply(Seq(F.Id("G"), Dot, Seq(Operatorname, Grp(F.Id("lapMatrix")))), Seq(Mathbb, Sp, F.Id("C")))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("Definition 2.2, p. 3: “The density matrix of a graph G is the matrix” σ(G) = (1/dG)L(G). The source expression is the complex SimpleGraph.lapMatrix divided by degreeSum. A nonempty edge set ensures a positive denominator."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("root"),
                DeclarationHandle.Create(Module + "root"), H("root"),
                StatementSource.FromAuthor(Disp(All(F.Id("p"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("q"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("x"), Seq(Parenthesized(Call("Fin", F.Id("p"))), Times, Sp, Parenthesized(Call("Fin", F.Id("q")))), Seq(Call("root", F.Id("x")), Iff, Sp, Seq(Parenthesized(Seq(Call("val", Seq(F.Id("x"), Dot, D(1))), Eq, D(0))), Land, Sp, Parenthesized(Seq(Call("val", Seq(F.Id("x"), Dot, D(2))), Eq, D(0)))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("The source labels i = sq + s′. Its vertex v₁ is zero-based (0,0)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("stargraph"),
                DeclarationHandle.Create(Module + "starGraph"), H("starGraph"),
                StatementSource.FromAuthor(Disp(All(F.Id("p"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("q"), Seq(Mathbb, Sp, F.Id("N")), Seq(Call("starGraph", F.Id("p"), F.Id("q")), Eq, Seq(Begin, Grp(F.Id("cases")), Apply(Qualified("SimpleGraph", "starGraph"), Parenthesized(Seq(Seq(Langle, D(0), Comma, Seq(F.Id("h"), Dot, D(1)), Rangle), Comma, Seq(Langle, D(0), Comma, Seq(F.Id("h"), Dot, D(2)), Rangle)))), Amp, Seq(Operatorname, Grp(F.Id("if"))), Sp, F.Id("h"), Colon, Seq(Parenthesized(Seq(D(0), Lt, F.Id("p"))), Land, Sp, Parenthesized(Seq(D(0), Lt, F.Id("q")))), RowBreak, Qualified("Bot", "bot"), Amp, Seq(Operatorname, Grp(F.Id("otherwise"))), End, Grp(F.Id("cases")))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("The source star K₁,ₙ₋₁ is rooted at v₁. The positive dimensions use Mathlib SimpleGraph.starGraph directly at the two Fin zero coordinates. The total extension is the empty graph when a dimension is zero; the conjecture domain excludes those cases because the edge set must be nonempty."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("center"),
                DeclarationHandle.Create(Module + "center"), H("center"),
                StatementSource.FromAuthor(Disp(All(F.Id("k"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("x"), Seq(Parenthesized(Call("Fin", D(2))), Times, Sp, Parenthesized(Call("Fin", Seq(D(2), Cdot, Sp, F.Id("k"))))), Seq(Call("center", F.Id("x")), Iff, Sp, Seq(Parenthesized(Seq(Call("val", Seq(F.Id("x"), Dot, D(1))), Eq, D(0))), Land, Sp, Parenthesized(Seq(Apply(Qualified("Nat", "mod"), Call("val", Seq(F.Id("x"), Dot, D(2))), D(2)), Eq, D(0))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("A block center has first coordinate zero and an even second coordinate. Nat.mod is natural-number remainder."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gk"),
                DeclarationHandle.Create(Module + "Gk"), H("Gk"),
                StatementSource.FromAuthor(Disp(All(F.Id("k"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("x"), Seq(Parenthesized(Call("Fin", D(2))), Times, Sp, Parenthesized(Call("Fin", Seq(D(2), Cdot, Sp, F.Id("k"))))), All(F.Id("y"), Seq(Parenthesized(Call("Fin", D(2))), Times, Sp, Parenthesized(Call("Fin", Seq(D(2), Cdot, Sp, F.Id("k"))))), Seq(Apply(Seq(Call("Gk", F.Id("k")), Dot, Seq(Operatorname, Grp(F.Id("Adj")))), F.Id("x"), F.Id("y")), Iff, Sp, Seq(Parenthesized(Seq(F.Id("x"), Neq, Sp, F.Id("y"))), Land, Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Apply(Qualified("Nat", "div"), Call("val", Seq(F.Id("x"), Dot, D(2))), D(2)), Eq, Apply(Qualified("Nat", "div"), Call("val", Seq(F.Id("y"), Dot, D(2))), D(2)))), Land, Sp, Parenthesized(Seq(Call("center", F.Id("x")), Lor, Sp, Call("center", F.Id("y")))))), Lor, Sp, Parenthesized(Seq(Parenthesized(Call("center", F.Id("x"))), Land, Sp, Parenthesized(Call("center", F.Id("y"))), Land, Sp, Parenthesized(Seq(Call("root", F.Id("x")), Lor, Sp, Call("root", F.Id("y"))))))))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("Each four-vertex block is a star. Block centers are joined to the global root. Nat.div means natural-number integer division; the displayed divisions are not real fractions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + "claim"), H("claim"),
                StatementSource.FromAuthor(Disp(Seq(Seq(Operatorname, Grp(F.Id("claim"))), Iff, Sp, All(F.Id("p"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("q"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("G"), Call("SimpleGraph", Seq(Parenthesized(Call("Fin", F.Id("p"))), Times, Sp, Parenthesized(Call("Fin", F.Id("q"))))), Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("G"), Dot, Seq(Operatorname, Grp(F.Id("Connected"))))), Land, Sp, Parenthesized(Seq(Seq(F.Id("G"), Dot, Seq(Operatorname, Grp(F.Id("edgeSet")))), Dot, Seq(Operatorname, Grp(F.Id("Nonempty"))))))), Longrightarrow, Sp, Seq(Apply(Seq(F.Id("E"), Underscore, F.Id("F")), Call("sigma", F.Id("G"))), Le, Sp, Apply(Seq(F.Id("E"), Underscore, F.Id("F")), Call("sigma", Call("starGraph", F.Id("p"), F.Id("q")))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("Conjecture 6.7, p. 18, verbatim: “Let 𝒢⁽ᶜ⁾ₙ be the set of all connected graphs on n vertices. Let G ∈ 𝒢⁽ᶜ⁾ₙ (|V| = pq). Then max𝒢⁽ᶜ⁾ₙ EF(σ(G)) = EF(σ(K₁,ₙ₋₁)).” Encoding: every p,q and connected simple graph on Fin p × Fin q with nonempty edge set. The maximum assertion means that every such graph has formation at most the rooted star."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("family"),
                DeclarationHandle.Create(Module + "family"), H("family"),
                StatementSource.FromAuthor(Disp(All(F.Id("k"), Seq(Mathbb, Sp, F.Id("N")), Seq(Parenthesized(Seq(D(3,2), Le, Sp, F.Id("k"))), Longrightarrow, Sp, Seq(Parenthesized(Seq(new Formula.Fraction(D(4,9,9,7,5,1), D(1,6,6,4,6,1,4,4)), Lt, Apply(Seq(F.Id("E"), Underscore, F.Id("F")), Call("sigma", Call("Gk", F.Id("k")))))), Land, Sp, Parenthesized(Seq(Apply(Seq(F.Id("E"), Underscore, F.Id("F")), Call("sigma", Call("starGraph", D(2), Seq(D(2), Cdot, Sp, F.Id("k"))))), Lt, new Formula.Fraction(D(8,9), D(3,1,7,5))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("For every k ≥ 32 the family density has a strict lower bound exceeding the strict star upper bound. The difference between the rational bounds is positive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Module + "result"), H("result"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Seq(Operatorname, Grp(F.Id("claim")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("Refutation of BGS Conjecture 6.7: the instance k = 32 has 128 vertices with tensor dimensions 2 × 64. The graph is connected and has nonempty edge set, and its formation exceeds the rooted star."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        Seq(function, Parenthesized(Join(arguments)));
    private static Formula Join(Formula[] arguments) => arguments.Length switch
    {
        0 => Seq(),
        1 => arguments[0],
        _ => Seq(arguments[0], Comma, Join(arguments[1..]))
    };
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Named(name));
    private static Formula Named(string name) => name.Contains('_')
        ? Seq(Operatorname, Grp(F.Id(name.Split('_')[0])), Underscore, Grp(F.Id(name.Split('_')[1])))
        : Seq(Operatorname, Grp(F.Id(name)));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, type)), Comma, Sp, body);
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(variable, InMacro, Sp, type), Sp, Parenthesized(body));
}
