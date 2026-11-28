using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Permutohedra;

internal sealed class OlairezCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/olairez2026dihedralpermutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prefix recurrence counts the lattice points in every nonnegative integral dilation of the dihedral permutohedron.",
        H("Lattice points in the dihedral permutohedron"),
        Blocks(
            Definition("source-points", "SourcePoints", "Integer points of the source dilation",
                "Let Qₙ be the real convex hull of the orbit of (1, …, n) under the two permutation matrices of Equation (2). Residue zero denotes paper label n. Write Xₙ,ₖ for the integer-coordinate vectors whose real images lie in kQₙ. Question 6.1 of Colin Olairez, arXiv:2610.28672v2, §6, printed p. 21, asks for the number of lattice points or the Ehrhart polynomial. Source locator https://arxiv.org/html/2610.28672v2#S6.Thmquestion1 . Both n and k are natural; the counting theorem assumes n ≥ 3 and includes k = 0."),
            Definition("difference-coset", "Coset", "The integral difference coset",
                "Set S = n(n + 1)/2 and T = n(n − 1)/2. The existing source-coordinate conjugacy identifies the real signed wrap hull for every n ≥ 3. The forward difference dᵢ = xᵢ₊₁ − xᵢ wraps cyclically. It has sum zero and weighted sum W(d) = ∑ᵢ i dᵢ = nx₀ − ∑ᵢ xᵢ. On the plane ∑ᵢ xᵢ = kS, its image is precisely the sum-zero lattice coset W(d) ≡ −kS modulo n. This residue is n/2 when n is even and k is odd, and zero otherwise."),
            Paragraph(Text("For the inverse, let pᵢ be the sum of dⱼ over 0 ≤ j < i. The sum-zero condition supplies the last cyclic increment. Recover xᵢ by adding (kS − ∑ⱼ pⱼ)/n to each pᵢ. The residue condition makes this constant integral.")),
            Paragraph(Text("The signed wrap hull is the image of the radius-k cross-polytope under the map u ↦ (∑ᵢ uᵢ)1 − nu. Thus a difference vector is feasible exactly when some translate z = d + t1 has absolute sum at most B = nk. For integral d, the absolute sum is affine between consecutive integers, so feasibility over the reals implies feasibility at an integer endpoint.")),
            Definition("least-translate", "IsFirst", "The least feasible integer translate",
                "Feasible integer translates form an interval inside −k ≤ t ≤ k. At z = d + t1 let a = ∑ᵢ |zᵢ| and let p count its positive entries. The absolute sum at the predecessor z − 1 is a + n − 2p. The least feasible translate is characterized by a ≤ B and B + 2p < a + n."),
            Definition("prefix-count", "D", "The prefix recurrence",
                "The state (s, r, a, p) records coordinate sum, weighted residue, absolute sum and positive entry count. At length zero the state (0, 0, 0, 0) has count one and every other state has count zero. At length i, for each integer v with |v| ≤ B − a, add the old count to (s + v, r + iv, a + |v|, p + [v > 0]), reducing r modulo n. Distinct prefixes that reach the same state contribute separately."),
            Definition("terminal-sum", "terminalSum", "The terminal sum",
                "Write E(n, k) for the sum of Dₙ(nt, Tt − kS mod n, a, p) over integers t with |t| ≤ k, natural numbers a ≤ B and p ≤ n, and the strict inequality B + 2p < a + n. Each terminal vector recovers t from its coordinate sum, then d by subtracting t from every coordinate."),
            Describe.Lean(
                DescribeId.Create("olairez-count-dilation"),
                DeclarationHandle.Create(Module + ".latticePointCount_terminalSum"),
                H("Finite cardinality in every dilation"),
                StatementSource.FromAuthor(CountFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every source point corresponds to one terminal prefix of length n, and every such prefix recovers one source point. The sum counts the prefixes with multiplicity across states. Taking k = 1 gives the undilated count, and k = 0 gives the singleton at the origin. This resolves the lattice-point alternative of Question 6.1. An explicit Ehrhart coefficient formula remains open here.")),
                    Paragraph(Text("On the named input fourOneInput = (4, 1), kernel evaluation counts 22 occurrences passing the terminal filter. An anonymous application of the cardinality theorem and the recurrence identity gives 22 points in the original source lattice."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("olairez-2026-dihedral-permutohedron-lattice-points"),
                    ResolutionKind.Proved)),
            Definition("four-one-input", "fourOneInput", "Four coordinates at unit dilation",
                "The input pair (4, 1) gives the coordinate count and dilation for the anonymous checker application."))));

    private static Formula CountFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var points = Seq(F.Id("X"), Underscore, Grp(Seq(n, Comma, k)));
        return Disp(Seq(Forall, Sp, n, Comma, k, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp, n, Sp, Geq, Sp, D(3), Sp, Implies, Sp,
            Open, Call(Operator("Finite"), points), Sp, Land, Sp,
            Call(Operator("card"), points), Eq, Call(F.Id("E"), n, k), Close));
    }

    private static Formula Operator(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static DocumentBlock Definition(string id, string selector, string heading, string text) =>
        Describe.Lean(DescribeId.Create("olairez-count-" + id),
            DeclarationHandle.Create(Module + "." + selector), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
