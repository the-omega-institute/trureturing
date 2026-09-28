using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class GridAcyclicOrientationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/GridAcyclicOrientations.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/muhlherr2026acyclic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 7 x 7 grid graph has a number of acyclic orientations divisible by 4, so clause (1) of Conjecture 1 of L. Mühlherr and G. Poullot (arXiv:2609.02249), which asks for 2 modulo 4 on every grid P_m x P_n with m and n odd and at least 3, fails at m = n = 7. The number of acyclic orientations of a graph is its Tutte polynomial at (2, 0), the q = -1 point of the Potts model.",
        H("Acyclic orientations of the 7 x 7 grid modulo 4"),
        Blocks(
            Node("claim", "Clause (1) of Conjecture 1", ClaimFormula(),
                "For all m and n at least 3 and both odd, the grid graph P_m x P_n, the box product of the path graphs on Fin m and Fin n, has a number psi of acyclic orientations congruent to 2 modulo 4. Orientations and psi are those of the complete tripartite document: Boolean relations that give every edge exactly one arc, counted when their transitive closure has no loop.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation of clause (1)", Disp(new Formula.Not(F.Id("claim"))),
                "Let r reverse all arcs and, for a graph automorphism s of order two, let s also act on orientations by transport. If r and s commute and r has no fixed point on a finite set Y, the orbits of r and s have two or four elements, so the size of Y is congruent modulo 4 to the number of elements fixed by s plus the number fixed by r s. For the reflection of the first factor of P_(2a+1) x P_n with n at least 2, the middle copy of P_n is fixed pointwise, so r s fixes no orientation. The orientations fixed by s correspond to the acyclic orientations of the half P_(a+1) x P_n: folding the far half onto the near one sends a directed cycle to a closed directed walk. Hence psi(P_(2a+1) x P_n) is congruent to psi(P_(a+1) x P_n) modulo 4, and psi(P_7 x P_7), psi(P_4 x P_7) = psi(P_7 x P_4) and psi(P_4 x P_4) agree modulo 4. On the 4 x 4 grid the column and row reflections swap the ends of the middle edges and fix no orientation, so psi is congruent to the number of acyclic orientations reversed by both reflections. The transpose t splits these into those it fixes and those it reverses. An orientation reversed by the column reflection and by t is invariant under the rotation by 90 degrees and orients the central square as a directed 4-cycle, so none is acyclic. In an orientation fixed by t and reversed by both reflections every corner is a source or a sink, so reversing the eight corner edges keeps it acyclic; this reversal and r generate a group of order four acting without fixed points, and the number of such orientations is divisible by 4. So psi(P_7 x P_7) is divisible by 4, not congruent to 2.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("gridao-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        Formula grid = Call("boxProd", Call("pathGraph", m), Call("pathGraph", n));
        Formula conclusion = Equal(Seq(Call("acyclicOrientationCount", grid), Sp, Named("mod"),
            Sp, D(4)), D(2));
        Formula body = Implies(AtMost(D(3), m), Implies(AtMost(D(3), n),
            Implies(Call("Odd", m), Implies(Call("Odd", n), conclusion))));
        return Disp(Iff(F.Id("claim"), All("m", Naturals(), All("n", Naturals(), body))));
    }
}
