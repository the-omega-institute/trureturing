using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Selection;

internal sealed class MeasurableDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Selection/Measurable.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Fn(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula MemberLaw => Seq(All("a", V("A")),
        Call("f", V("a")), Sp, InMacro, Sp, Call("Phi", V("a")));
    private static Formula SelectionStatement => Disp(new Formula.Aligned([
        Seq(All("A", Call("Type", V("u"))), All("Y", Call("Type", V("v")))),
        Seq(Call("MeasurableSpace", V("A")), Sp, Land, Sp,
            Call("CompleteSeparableMetricBorelSpace", V("Y")), Sp, Rightarrow),
        Seq(All("Phi", Fn(V("A"), Call("Set", V("Y"))))),
        Seq(Grp(Seq(All("a", V("A")), Call("Nonempty", Call("Phi", V("a"))),
            Sp, Land, Sp, Call("IsClosed", Call("Phi", V("a"))))), Sp, Rightarrow),
        Seq(Grp(Seq(All("U", Call("Set", V("Y"))), Call("IsOpen", V("U")),
            Sp, Rightarrow, Sp, Call("MeasurableSet", Call("Hit", V("Phi"), V("U"))))), Sp, Rightarrow),
        Seq(Exists, Sp, V("f"), Colon, Sp, Fn(V("A"), V("Y")), Comma, Sp,
            Call("Measurable", V("f")), Sp, Land, Sp, Grp(MemberLaw))
    ]));
    private static Formula SectionStatement => Disp(new Formula.Aligned([
        Seq(All("K", Call("Type", V("u"))), All("L", Call("Type", V("v")))),
        Seq(Call("CompactMetricBorelSpace", V("K")), Sp, Land, Sp,
            Call("HausdorffBorelSpace", V("L")), Sp, Rightarrow),
        Seq(All("p", Fn(V("K"), V("L"))), Call("Continuous", V("p")), Sp, Land, Sp,
            Call("Surjective", V("p")), Sp, Rightarrow),
        Seq(Exists, Sp, V("q"), Colon, Sp, Fn(V("L"), V("K")), Comma, Sp,
            Call("Measurable", V("q")), Sp, Land, Sp,
            Grp(Seq(All("y", V("L")), Call("p", Call("q", V("y"))), Sp, Eq, Sp, V("y"))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak-measurable nonempty closed fibers admit measurable selectors; continuous compact metric quotients have Borel right inverses.",
        H("Measurable selection and compact metric quotient sections"),
        Blocks(
            Paragraph(Text(
                "All carrier universes are independent. BorelSpace means that the specified measurable structure equals the Borel structure. "
                + "Hit(Phi,U) is exactly the set of a with nonempty Phi(a) intersect U. "
                + "No carrier is assumed nonempty. The first theorem has an arbitrary measurable source and a complete separable metric Borel target.")),
            Describe.Lean(DescribeId.Create("exists-measurable-selection"),
                DeclarationHandle.Create(Owner + "exists_measurable_selection"),
                H("Kuratowski–Ryll-Nardzewski measurable selection"),
                StatementSource.FromAuthor(SelectionStatement),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/wu2026measurableselection")),
                Blocks(Paragraph(Text(
                    "The actual KT. Wu / LeanPool proof is ported from commit 7d5e94f7172d47c78cac7f23c0dd01cef1665e42 under Apache 2.0. "
                    + "At stage n the selector takes values in a dense sequence and is the least index whose ball, intersected with the previous ball, meets the current fiber. "
                    + "The predicate splits over the countably many measurable fibers of the previous index. Geometric bounds give a Cauchy sequence; "
                    + "its pointwise limit is measurable and belongs to each closed fiber. The empty-source case uses the empty function. "
                    + "The source identity and license are recorded in the cited Library note; no originality is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-measurable-right-inverse"),
                DeclarationHandle.Create(Owner + "exists_measurable_right_inverse"),
                H("Borel section of a compact metric quotient"),
                StatementSource.FromAuthor(SectionStatement),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/wu2026measurableselection")),
                Blocks(Paragraph(Text(
                    "For every continuous surjection p from compact metric K to Hausdorff Borel L, put Phi(y)=p-preimage({y}). "
                    + "Surjectivity gives nonempty fibers and continuity gives closed fibers. An open U in K is locally compact and second countable as a subspace, "
                    + "hence sigma-compact. Its continuous image p[U] is a countable union of compact sets. Each compact set is closed in Hausdorff L, so this union is Borel. "
                    + "This image equals the hit set of U. The selector theorem gives measurable q with p(q(y))=y. "
                    + "No zero-dimensionality, positivity or metrizability assumption on L is imposed; empty carriers remain included."))),
                DescribeRole.Theorem))));
}
