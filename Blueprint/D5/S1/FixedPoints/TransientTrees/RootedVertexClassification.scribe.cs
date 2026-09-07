using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints.TransientTrees;

internal sealed class RootedVertexClassificationDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S1/FixedPoints/TransientTrees/RootedVertexClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual rooted vertex equivalences preserve branch codes and are classified by them.",
        H("Rooted Vertex Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-equivalence-preserves-code"),
                DeclarationHandle.Create(Owner + "branch_code_eq_of_rooted_vertex_equiv"),
                H("Actual rooted equivalences preserve branch codes"),
                StatementSource.FromAuthor(ClassificationFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Descendant and RootedVertexEquiv are the existing original-vertex "
                    + "definitions. The latter stores an actual equivalence of descendant "
                    + "subtypes, its two inverse laws, the distinguished root equality, and "
                    + "preservation and reflection of internal TransientChild edges.")),
                    Paragraph(Text(
                    "Fix the given equivalence on its original carriers. Every descendant's "
                    + "complete child fiber is transported using this equivalence and its inverse. "
                    + "Well-founded induction proves branch-code equality at every descendant "
                    + "and its image. Multiset transport retains all occurrences, including "
                    + "repeated identical child branches. Specialization at the root gives "
                    + "the displayed equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-rooted-classification"),
                DeclarationHandle.Create(Owner + "rooted_vertex_classification"),
                H("Branch codes classify actual rooted vertices"),
                StatementSource.FromAuthor(ClassificationFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The forward implication is the preceding invariant transport theorem. "
                    + "The reverse implication directly uses the existing reconstruction "
                    + "theorem rooted_vertex_equiv_of_branch_code_eq. The carrier universes "
                    + "and finiteness instances are independent; ambient cardinalities may differ.")),
                    Paragraph(Text(
                    "Roots may be transient or periodic. A transient root's outgoing update "
                    + "may leave its descendant carrier, so this classification concerns the "
                    + "internal child relation. Global update conjugacy, directed cycle rotation, "
                    + "component multiplicities, actual depth truncation and naturality, "
                    + "cardinal-depth sufficiency, and compatible-family reconstruction remain "
                    + "separate obligations. The finite-realization domain of an unrestricted "
                    + "compatible family remains unresolved."))),
                DescribeRole.Theorem))));

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula TypeAt(string level) => Seq(Name("Type"), Underscore, Grp(F.Id(level)));
    private static Formula Row => Seq(RowBreak, Grp());

    private static Formula ClassificationFormula(bool iff)
    {
        Formula y = F.Id("Y"), z = F.Id("Z"), f = F.Id("f"), g = F.Id("g");
        Formula r = F.Id("r"), s = F.Id("s"), e = F.Id("e");
        Formula equivalence = Call("RootedVertexEquiv", f, g, r, s);
        Formula premise = iff
            ? Seq(Call("Nonempty", equivalence), Sp, Iff, Sp)
            : Seq(Forall, Sp, e, Colon, Sp, equivalence, Comma, Sp);
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            F.Id("u"), Comma, Sp, F.Id("v"), Sp, Name("universes"), Comma, Row,
            Forall, Sp, y, Colon, Sp, TypeAt("u"), Comma, Sp,
            z, Colon, Sp, TypeAt("v"), Comma, Row,
            OpenBracket, Call("Fintype", y), CloseBracket, Comma, Sp,
            OpenBracket, Call("Fintype", z), CloseBracket, Comma, Row,
            Forall, Sp, f, Colon, Sp, y, Sp, To, Sp, y, Comma, Sp,
            g, Colon, Sp, z, Sp, To, Sp, z, Comma, Row,
            Forall, Sp, r, Colon, Sp, y, Comma, Sp, s, Colon, Sp, z, Comma, Row,
            premise, Call("branchCode", f, r), Eq, Call("branchCode", g, s),
            End, Grp(F.Id("gathered"))));
    }
}
