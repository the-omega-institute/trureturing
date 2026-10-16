using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class GirardPlagneBoxLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-support box Davenport ratios converge to the largest augmented sign determinant in every positive dimension.",
        H("GirardPlagneBoxLimit"),
        Blocks(
            Describe.Lean(DescribeId.Create("d"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/GirardPlagneBoxLimit.D"),
                H("D"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, F.Id("m"), Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Seq(Seq(F.Id("D"), Sp, F.Id("d"), Sp, F.Id("m"), Sp, F.Id("k")), Sp, Eq, Sp, Parenthesized(Seq(Call("sSup"), Sp, Parenthesized(Seq(Call("lengths"), Sp, F.Id("d"), Sp, F.Id("m"), Sp, F.Id("k"))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/girardplagne2026boxes")),
                Blocks(Paragraph(Text("Section 2, printed page 2: \"we study the quantity D^(d+1)(⟦−m, m⟧^d) which is defined as the maximal length of a minimal zero-sum sequence over ⟦−m, m⟧^d having a support of size d + 1.\" Multiplicity functions use pointwise subsequence order; support cardinality counts distinct vectors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/GirardPlagneBoxLimit.claim"),
                H("claim"),
                StatementSource.FromAuthor(Disp(Seq(Call("claim"), Sp, Eq, Sp, Parenthesized(Seq(Forall, Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1), Sp, Le, Sp, F.Id("d"), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1), Sp, Le, Sp, F.Id("m"), Sp, To, Sp, Parenthesized(Seq(Call("lengths"), Sp, F.Id("d"), Sp, F.Id("m"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Dot, Sp, Call("Nonempty"), Sp, Land, Sp, Call("BddAbove"), Sp, Parenthesized(Seq(Call("lengths"), Sp, F.Id("d"), Sp, F.Id("m"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))))), Sp, Land, Sp, Exists, Sp, F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Comma, Sp, Call("Filter"), Sp, Dot, Sp, Call("Tendsto"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("D"), Sp, F.Id("d"), Sp, F.Id("m"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Slash, Sp, Sp, new Formula.Power(Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), F.Id("d")))), Sp, Call("Filter"), Sp, Dot, Sp, Call("atTop"), Sp, Parenthesized(Seq(Call("nhds"), Sp, F.Id("L")))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/girardplagne2026boxes")),
                Blocks(Paragraph(Text("Section 2, printed page 4: \"It appears tempting to conjecture that for every integer d ≥ 1, the ratio D^(d+1)(⟦−m, m⟧^d)/m^d has a limit when m tends to infinity. This is clear when d = 1, and it follows from Theorems 1 and 5 when d ∈ {2, 3}. However, this problem remains open when d ≥ 4.\" The natural-number parameter tends to infinity. The length set is nonempty and bounded for every m ≥ 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("girard-plagne-box-limit"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/GirardPlagneBoxLimit.girard_plagne_box_limit"),
                H("girard plagne box limit"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Seq(Parenthesized(Seq(D(1), Sp, Le, Sp, F.Id("d"))), Sp, To, Sp, Seq(Call("Tendsto"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("D"), Sp, F.Id("d"), Sp, F.Id("m"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Slash, Sp, Sp, new Formula.Power(Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))))), F.Id("d")))), Sp, Call("atTop"), Sp, Parenthesized(Seq(Call("nhds"), Sp, Parenthesized(Seq(Call("delta"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("R")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixed-support box Davenport ratios converge to the largest augmented sign determinant in every positive dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/GirardPlagneBoxLimit.result"),
                H("result"),
                StatementSource.FromAuthor(Disp(Call("claim"))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/girardplagne2026boxes")),
                Blocks(Paragraph(Text("Fixed-support box Davenport ratios converge to the largest augmented sign determinant in every positive dimension."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("girard-plagne-2026-box-davenport-limit"),
                    ResolutionKind.Proved)))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name) => Seq(Operatorname, Grp(F.Id(name)));
}
