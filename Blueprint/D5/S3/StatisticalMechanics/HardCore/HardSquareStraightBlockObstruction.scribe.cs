using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class HardSquareStraightBlockObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/HardCore/HardSquareStraightBlockObstruction";
    private const string Slug = "ortega-pena-ancavil-2026-question-5-2-straight";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ortegapenaancavil2026hardsquare");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The straight horizontal clause of Ortega and Peña-Ancavil's Question 5.2.",
        H("A Yang–Baxter obstruction for straight hard-square blocks"),
        Blocks(
            Definition("word", "Legal block heights", "Word",
                "Word k consists of binary words on Fin k with no two consecutive occupied sites. The finite enumeration counts each legal word once."),
            Definition("weight", "Face weights", "Weight",
                "Weight k assigns a complex number to each ordered face [a,b;c,d], with top row (a,b) and bottom row (c,d)."),
            Definition("seam", "Ordered horizontal compatibility", "H",
                "The last bit of the left height and the first bit of the right height cannot both be occupied."),
            Definition("vertical", "Vertical compatibility", "V",
                "No coordinate is occupied in both heights."),
            Definition("face", "Common face support", "FaceSupport",
                "The two ordered seams are H(a,b) and H(c,d). The two vertical pairs are V(a,c) and V(b,d)."),
            Definition("supported", "Zero extension", "Supported",
                "The weight vanishes when any of the four compatibility conditions fails. Values on legal faces can vanish."),
            Definition("occupation", "Occupation", "occ",
                "Sum the binary entries of the height as natural numbers."),
            Definition("blocked", "Blocked hard-square weight", "blocked",
                "On a legal face the value is A^occ(a) B^occ(b) C^occ(c) D^occ(d). The four parameters are complex units. The value on every other face is zero."),
            Definition("equation", "Equation (2.2)", "EqAt",
                "At (a,b,c,d,e,f), sum P[f,g;a,b] Q[e,d;f,g] R[d,c;g,b] over all legal g. "
                + "The right side is the nonzero scalar ρ times the sum of R[e,g;f,a] Q[g,c;a,b] P[e,d;g,c] over the same heights."),
            Definition("family", "Analytic family through a target", "HasFamily",
                "All parameter pairs in Ω use the common face support. Each matrix entry is holomorphic in each variable on Ω. "
                + "For every p,q,r in Ω one nonzero scalar works for all boundaries, with (P,Q,R) = (W(p,q),W(p,r),W(q,r)). "
                + "The weight equals the target at some ordered pair in Ω × Ω, including the possibility of equal parameters."),
            Describe.Lean(DescribeId.Create("straight-obstruction-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Nonexistence through the blocked weight"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let 0 be the empty height, L the even-position height and M the odd-position height, with one-based numbering. "
                        + "At the ordered boundary (0,M,L,L,0,L), simultaneous support of the left P and Q factors requires V(g,M) and V(L,g). "
                        + "The two parity classes cover every site, so only g = 0 can contribute. The right P factor has vertical column (L,L), "
                        + "which shares the occupied second site and forces every right summand to vanish.")),
                    Paragraph(Text(
                        "The retained faces are [L,0;0,M], [0,L;L,0], and [L,L;0,M]. "
                        + "The last face is legal because L starts empty and L and M are disjoint. "
                        + "Fix the special pair (p,r) and vary q. The middle factor is a nonzero blocked weight, so the first and third factors form a product of holomorphic slices that vanishes throughout Ω. "
                        + "The identity theorem makes one slice zero throughout Ω, contradicting its special value at r or p.")),
                    Paragraph(Text(
                        "The theorem concerns straight horizontal blocks and the common support. Arbitrary shapes, mixed support for row weights and intertwiners, and hidden heights are open here."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create(Slug), ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string id, string title, string name, string prose) =>
        Describe.Lean(DescribeId.Create("straight-obstruction-" + id), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Statement() =>
        Seq(Forall, Sp, F.Id("k"), Sp, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(3), Sp, Leq, Sp, F.Id("k"), Sp, Implies, Sp,
            Forall, Sp, F.Id("A"), Comma, F.Id("B"), Comma, F.Id("C"), Comma, F.Id("D"),
            Sp, Colon, Sp, Mathbb, Grp(F.Id("C")), Caret, Grp(Times), Comma, Sp,
            Forall, Sp, F.Id("U"), Sp, Subseteq, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
            Call("IsOpen", F.Id("U")), Sp, Land, Sp, Call("IsConnected", F.Id("U")), Sp, Implies, Sp,
            Neg, Sp, Call("HasFamily", F.Id("k"), F.Id("U"),
                Call("blocked", F.Id("A"), F.Id("B"), F.Id("C"), F.Id("D"))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
