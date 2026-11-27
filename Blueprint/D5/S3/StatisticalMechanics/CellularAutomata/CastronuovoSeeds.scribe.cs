using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class CastronuovoSeedsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/CastronuovoSeeds.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/castronuovodennunziomargara2026orbits");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One four-input rule admits a complete simple cyclic seed and a complete unrestricted line seed at k = 2. "
        + "Every simple line seed omits XOR for this rule.",
        H("Complete cyclic and line seeds for a four-input cellular rule"),
        Blocks(
            Paragraph(Text(
                "A letter is a Boolean function of k inputs. The initial alphabet consists of the two constant "
                + "functions and the k projections. A simple seed uses each projection exactly once. A line seed "
                + "has finitely many exceptions to a constant background, either 0 or 1, with 0 the paper's default. "
                + "A cyclic seed of length N uses sites in Z/NZ and requires N at least the rule arity n. "
                + "Completeness asks for every Boolean function to occur as a whole letter at some site and natural "
                + "time, including time zero. The paper starts projection indices at one and this module starts at zero.")),
            Paragraph(Text(
                "The rule updates site i from i−1, i, i+1, i+2, in that order, by "
                + "φ(a,b,c,d) = ¬a ∧ ((b ∧ ¬c) ∨ d). The lifted update applies this formula "
                + "pointwise for each assignment of the input variables.")),
            Paragraph(Text(
                "The ring starts at sites 0 through 4 with (X,Y,0,0,1). A mask stores the value at "
                + "(X,Y) in bit 2X+Y. The six rows are (12,10,0,0,15), (0,2,5,12,11), "
                + "(4,14,9,0,3), (8,2,1,4,15), (0,6,13,8,3), and (12,10,1,0,7). "
                + "The proof checks all thirty entries at each of the four assignments. Each mask from 0 through 15 appears.")),
            Node("xor-exclusion", "XOR is absent from every simple line orbit", XorExclusion(),
                "For fixed Y, toggling X changes only its unique initial site. The usual Boolean order at "
                + "even sites and its reverse at odd sites order the pair in a direction independent of Y. "
                + "The signed monotonicity of the four local inputs preserves this order. At any output "
                + "site and time the resulting order in X has the same direction for both choices of Y. "
                + "XOR reverses that direction as Y changes. The argument uses the alphabet and simplicity "
                + "and applies to both constant backgrounds.",
                "simple_line_omits_xor"),
            Node("question-5-9", "A complete simple ring with no complete simple line seed",
                Existence("StronglyCyclicUniversal"),
                "Question 5.9 quantifies over one positive arity n, one Boolean local rule φ of that arity, "
                + "and one positive input count k. StronglyCyclicUniversal requires a complete simple cyclic "
                + "seed at some legal ring length. StronglyUniversal requires a complete simple finite-background "
                + "line seed. Here n = 4 and k = 2. The five-ring has length at least four, uses both "
                + "projections once, and contains all sixteen target letters by time five.",
                "question_5_9",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("castronuovo-dennunzio-margara-2026-question-5-9"), ResolutionKind.Proved)),
            Node("question-5-6", "A complete unrestricted line seed with no complete simple line seed",
                Existence("Universal"),
                "Question 5.6 uses the same existential quantifiers. Universal permits any seed in the "
                + "finite-background line family, including repeated projections. The witness consists of four "
                + "copies of (X,Y,0,0,1) on the inclusive interval [−5,14] starting at −5, with zero "
                + "elsewhere. All cones [i−t,i+2t] for 0 ≤ i ≤ 4 and 0 ≤ t ≤ 5 lie inside that interval. "
                + "Periodic extension commutes with the update, so the checked ring letters also occur on this line.",
                "question_5_6",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("castronuovo-dennunzio-margara-2026-question-5-6"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose, string declaration,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("castronuovo-seeds-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, resolution);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula XorExclusion()
    {
        Formula p = F.Id("P"), i = F.Id("i"), t = F.Id("t");
        return Disp(Seq(Forall, Sp, p, Sp, InMacro, Sp,
            Seq(new Formula.Integers(), Sp, To, Sp, Call("Letter", D(2))), Comma, Sp,
            Call("SeedAlphabet", p), Sp, Land, Sp, Call("Simple", p), Sp, Implies, Sp,
            Forall, Sp, i, Sp, InMacro, Sp, new Formula.Integers(), Comma, Sp, t, Sp, InMacro, Sp,
            Naturals, Comma, Sp, Call("orbit", Call("lineStep", Phi), t, p, i),
            Sp, Neq, Sp, F.Id("xorLetter")));
    }

    private static Formula Existence(string positive)
    {
        Formula n = F.Id("n"), k = F.Id("k");
        return Disp(Seq(Exists, Sp, n, Sp, InMacro, Sp, Naturals, Comma, Sp,
            Phi, Sp, InMacro, Sp, Call("LocalRule", n), Comma, Sp,
            k, Sp, InMacro, Sp, Naturals, Comma, Sp,
            D(0), Sp, Lt, Sp, n, Sp, Land, Sp, D(0), Sp, Lt, Sp, k, Sp, Land, Sp,
            Call(positive, Phi, k), Sp, Land, Sp, Neg, Call("StronglyUniversal", Phi, k)));
    }

    private static Formula Phi => new Formula.Phi();
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
}
