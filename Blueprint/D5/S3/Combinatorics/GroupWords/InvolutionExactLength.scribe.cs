using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GroupWords;

internal sealed class InvolutionExactLengthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-length products of two involutions retain parity-specific exponent bounds.",
        H("Exact Length Products of Two Involutions"),
        Blocks(Describe.Lean(
            DescribeId.Create("involution-exact-length-products"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/GroupWords/InvolutionExactLength.exact_length_products"),
            H("Even and odd reachable exponent intervals"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/HilbertOperators/raeburnsinclair1989twoprojections")),
            Blocks(
                Paragraph(Text(
                    "G is any group, u and v are any elements with u*u=v*v=one, "
                    + "and m is any natural number. Put S={u,v} and R=u*v. "
                    + "ExactPower(S,n) is the pointwise set power S^n: every element "
                    + "is an ordered product of exactly n letters from S; at n=zero "
                    + "it is the singleton identity.")),
                Paragraph(Text(
                    "PowerInterval(R,a,b) is the image of the closed integer interval "
                    + "[a,b] under k maps to R^k. LeftPowerInterval(u,R,a,b) is its "
                    + "image under left multiplication by u. The two equalities "
                    + "are simultaneous: the even interval is [-m,m], and the odd "
                    + "interval is [-m,m+one]. The latter upper endpoint is included.")),
                Paragraph(Text(
                    "The proof first inducts on m to characterize products of "
                    + "{one,R,R inverse} by bounded integer exponents. Squaring S "
                    + "gives this set. For odd length, left multiplication by u "
                    + "preserves the index and left multiplication by v shifts "
                    + "it by one, producing the stated union of intervals.")),
                Paragraph(Text(
                    "Neither distinctness of u and v nor infinite order of R is "
                    + "assumed. Trivial groups, finite orders, coincident powers "
                    + "and m=zero are included. The conclusion gives sets, not "
                    + "unique expressions or their cardinalities. It supplies "
                    + "the exact-length group step for terminal Kraus words, "
                    + "but proves no matrix rank, minimal polynomial, channel "
                    + "realization or physical environment claim."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula g = F.Id("G"), u = F.Id("u"), v = F.Id("v"), m = F.Id("m");
        Formula r = Call("Product", u, v), s = Call("PairSet", u, v);
        Formula even = Call("Equal", Call("ExactPower", s, Call("Twice", m)),
            Call("PowerInterval", r, Call("Negate", m), m));
        Formula odd = Call("Equal", Call("ExactPower", s, Call("Successor", Call("Twice", m))),
            Call("LeftPowerInterval", u, r, Call("Negate", m), Call("Successor", m)));
        return Disp(ForAll("G", F.Id("Type"),
            Implies(Call("Group", g), ForAll("u", g, ForAll("v", g,
                Implies(Call("Involution", u), Implies(Call("Involution", v),
                    ForAll("m", F.Id("Nat"),
                        new Formula.Logic(even, FormulaLogicOperator.And, odd)))))))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
