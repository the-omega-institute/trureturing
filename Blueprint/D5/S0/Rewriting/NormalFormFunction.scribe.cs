using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class NormalFormFunctionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Newman =
        LibraryNoteRef.Create("D5/L/Rewriting/newman1942theories");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Terminating locally confluent rewrite systems admit a canonical normal-form function.",
            H("Normal Form Function"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("the-chosen-normal-form-is-reachable-and-normal"),
                    DeclarationHandle.Create("D5/S0/Rewriting/NormalFormFunction.nf_spec"),
                    H("The chosen normal form is reachable and irreducible"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Operatorname, Grp(F.Id("ReflTransGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp,
                        F.Id("nf"), Open, F.Id("r"), Comma, Sp, F.Id("termination"), Comma,
                        Sp, F.Id("localConfluence"), Comma, Sp, F.Id("a"), Close, Close,
                        Sp, Land, Sp,
                        Operatorname, Grp(F.Id("IsNormalForm")), Open, F.Id("r"), Close,
                        Open, F.Id("nf"), Open, F.Id("r"), Comma, Sp, F.Id("termination"), Comma,
                        Sp, F.Id("localConfluence"), Comma, Sp, F.Id("a"), Close, Dot))),
                    AssessedProvenance.FromLiterature(Newman),
                    Blocks(
                        Paragraph(Text(
                            "The function is defined by choosing the unique normal form supplied "
                            + "by the frozen Newman theorem.")),
                        Paragraph(Text(
                            "Its specification records both the reflexive-transitive reduction "
                            + "from the source and irreducibility of the chosen endpoint."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("choosing-the-normal-form-twice-is-idempotent"),
                    DeclarationHandle.Create("D5/S0/Rewriting/NormalFormFunction.nf_idempotent"),
                    H("Normal-form selection is idempotent"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("nf"), Open, F.Id("r"), Comma, Sp, F.Id("termination"), Comma,
                        Sp, F.Id("localConfluence"), Comma, Sp,
                        F.Id("nf"), Open, F.Id("r"), Comma, Sp, F.Id("termination"), Comma,
                        Sp, F.Id("localConfluence"), Comma, Sp, F.Id("a"), Close, Close,
                        Sp, Eq, Sp,
                        F.Id("nf"), Open, F.Id("r"), Comma, Sp, F.Id("termination"), Comma,
                        Sp, F.Id("localConfluence"), Comma, Sp, F.Id("a"), Close, Dot))),
                    AssessedProvenance.FromLiterature(Newman),
                    Blocks(Paragraph(Text(
                        "The first selection reaches a normal form from the second selection's "
                        + "source; uniqueness therefore identifies the two choices."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("equivalent-starting-points-have-the-same-normal-form"),
                    DeclarationHandle.Create("D5/S0/Rewriting/NormalFormFunction.nf_eq_of_eqvGen"),
                    H("Equivalent starting points share a normal form"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Operatorname, Grp(F.Id("EqvGen")), Open, F.Id("r"), Close,
                        Open, F.Id("a"), Comma, Sp, F.Id("b"), Close, Sp, Rightarrow, Sp,
                        F.Id("nf"), Open, F.Id("r"), Comma, Sp, F.Id("termination"), Comma,
                        Sp, F.Id("localConfluence"), Comma, Sp, F.Id("a"), Close,
                        Sp, Eq, Sp,
                        F.Id("nf"), Open, F.Id("r"), Comma, Sp, F.Id("termination"), Comma,
                        Sp, F.Id("localConfluence"), Comma, Sp, F.Id("b"), Close, Dot))),
                    AssessedProvenance.FromLiterature(Newman),
                    Blocks(
                        Paragraph(Text(
                            "Church-Rosser converts the generated equivalence into a common "
                            + "reduct, and Newman normal-form uniqueness identifies both choices "
                            + "with the normal form of that reduct."))),
                    DescribeRole.Theorem))));
}
